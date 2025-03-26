#include "engines/ic3ng.h"

#include <fstream>

#include "smt-switch/smtlib_reader.h"
#include "utils/logger.h"
#include "smt-switch/logging_solver.h"

namespace pono {

void IC3ng::set_helper_term_predicates(const smt::TermVec & preds) {

  solver_->push();
  disable_all_labels();
    for (const auto & p : preds) {
      if (!(p->get_sort()->get_sort_kind() == smt::SortKind::BOOL ||
          (p->get_sort()->get_sort_kind() == smt::SortKind::BV && 
           p->get_sort()->get_width() == 1)))
           continue;
      if(solver_->check_sat_assuming({p}).is_unsat())
        continue;
      auto neg_p = smart_not(p);
      if(solver_->check_sat_assuming({neg_p}).is_unsat())
        continue;
      // check init/\not(p)  unsat
      // if (solver_->check_sat_assuming({ts_.init() ,neg_p}).is_unsat())
        loaded_predicates_.push_back(p);

      // if (solver_->check_sat_assuming({ts_.init() ,p}).is_unsat())
        loaded_predicates_.push_back(neg_p);
    }
  solver_->pop();

}

void IC3ng::set_helper_term_clauses(const smt::TermVec & clauses) {
  // Store validated clauses
  
  logger.log(1, "Starting to validate {} external clauses", clauses.size());
  
  for (const auto & clause : clauses) {
    // check type
    // HZ: some SMT solvers (e.g. Boolector), does not distinguish 
    // Bool vs. BV of width 1
    if ( (clause->get_sort()->get_sort_kind() != smt::SortKind::BOOL) &&
         !(clause->get_sort()->get_sort_kind() == smt::SortKind::BV &&
           clause->get_sort()->get_width() == 1 )) {
      logger.log(2, "Clause {} is not boolean type, skipping", clause);
      continue;
    }

    // check init =>  c? 
    // HZ: the clause we load should contain a "NOT" itself
    solver_->push();
    disable_all_labels();
    solver_->assert_formula(ts_.init());
    solver_->assert_formula(smart_not(clause));
    auto r = solver_->check_sat();
    solver_->pop();
    if (!r.is_unsat()) {
      logger.log(2, "Clause {} does not cover initial states, skipping", clause);
      continue;
    } // HZ: it must be unsat

    // check:  init & T => clause' ?
    // HZ: no need to have clause in the previous frame
    //     because init => clause
    solver_->push();
    disable_all_labels();
    solver_->assert_formula(ts_.init());
    solver_->assert_formula(ts_.trans());
    smt::Term next_clause = ts_.next(clause);
    solver_->assert_formula(smart_not(next_clause));
    r = solver_->check_sat();
    solver_->pop();

    if (r.is_unsat()) {
      // clause is inductive
      loaded_clauses_.push_back(clause);
      logger.log(2, "Added valid clause: {}", clause);

      // if frames is not empty, add clause to F₀
      if (!frames.empty()) {
        // Create new lemma, marked as FromSideLoad source
        auto lemma = new_lemma(clause, 
                              nullptr,  // External clauses have no counterexamples
                              LCexOrigin::FromSideLoad());
        
        logger.log(1, "Adding clause to initial frame: {}", clause->to_string());
        // add to F1 // 0 is for init, it should be on F1
        add_lemma_to_frame(lemma, 1); 
        
        // HZ: I don't see the reason for doing this. So I remove it.
        // assert it as a valid invariant to solver
        // solver_->assert_formula(clause);
      } else {
        // HZ: I think you may want to throw an exception
        // because normally this should not happen 
        throw PonoException("Frames not initialized yet, clause will be stored in loaded_clauses_");
      }
    } else {
      logger.log(2, "Clause {} fails to cover reachable states at F1, skipping", clause);
    }
  } // end of for each clause
  
  logger.log(1, 
             "Loaded {} valid clauses out of {} total clauses",
             loaded_clauses_.size(),
             clauses.size());
} // end of IC3ng::set_helper_term_clauses

// if  A is a subset (or equal to ) B, returns true
bool static is_subset(const smt::UnorderedTermSet & A, const smt::UnorderedTermSet & B) {
  for (const auto & e : A) {
    if (B.find(e) == B.end())
      return false;
  }
  return true;
}

bool static has_intersection(const smt::UnorderedTermSet & a, const smt::UnorderedTermSet & b) {
  const auto & smaller = a.size() < b.size() ? a : b;
  const auto & other = a.size() < b.size() ? b : a;
  for (const auto & e : smaller)
    if (other.find(e) != other.end())
      return true;
  return false;
}


void IC3ng::clear_cex_info() {
  // for each cex we stored, clear its related predicates
  model_info_map_.clear();
  // clear sliced var info
  for (const auto & str_slicevar_ptr : cube_slicedvar_info_allocation_pool) {
    auto slicedvar_ptr = str_slicevar_ptr.second;
    slicedvar_ptr->preds_w_related_vars.clear();
    slicedvar_ptr->preds_w_subset_vars.clear();
    slicedvar_ptr->related_info_populated = false;
  }
}


void IC3ng::sort_pred_in_extend_predicates(smt::TermVec & inout) {
  // we don't want to sort the term themselves
  // we don't want to invoke TermScore function more than once for a term
  std::vector<std::pair<size_t,size_t>> complexity_index_pair;
  size_t idx = 0;
  for (const auto & t : inout) {
    auto pos = internal_nodes_to_aiglit_map.find(t);
    if (pos == internal_nodes_to_aiglit_map.end())
      pos = internal_nodes_to_aiglit_map.find(smart_not(t));
    assert(pos != internal_nodes_to_aiglit_map.end()); // you should always find it
    complexity_index_pair.push_back({ pos->second, idx});
    ++ idx;
  }
  // sort in descending order (the `first` is compared first), so term-index with 
  // the highest score will rank first
  std::sort(complexity_index_pair.begin(), complexity_index_pair.end(), std::greater<>());

  // now map back to termvec
  smt::TermVec sorted_term;
  for (const auto & cpl_idx_pair : complexity_index_pair) {
    sorted_term.push_back(inout.at(cpl_idx_pair.second));
  }
  inout.swap(sorted_term); // this is the same as inout = sorted_term, but faster
} // end of SortPredicates

static bool is_symbol_or_extract_symbol(const smt::Term & t) {
  if (t->is_symbol())
    return true;
  if (t->get_op().prim_op == smt::PrimOp::Extract) {
    if( (*t->begin())->is_symbol() )
      return true;
  }
  return false;
}
// s 00 a 0001 b 0011
// s ==00 ->  a > b   a == b a>=b 
unsigned IC3ng::extend_predicates(Model *cex, smt::TermVec & conj_inout) {
  //TODO:
  // for each predicate p:
  //   check if  cex_expr /\ p  is unsat            :   use (p)
  //         or  cex_expr /\ not(p)  is unsat       :   use (not p)
  //   you may only check the case when (cex_expr) and p have shared variables
  //   you don't need to check every time, you can cache this...
  //   you can also cache the result of which p to consider for a given variable set
  
  // make sure newly added preds are put in the beginning of conj_inout
  
  auto model_info_pos = model_info_map_.find(cex);
  if (model_info_pos == model_info_map_.end()) {
    PerSlicedVarInfo * var_info_ = cex->get_per_slicedvar_info();
    if (!var_info_->related_info_populated) {
      // TODO: setup related info
      // based on structural varset check
      const smt::UnorderedTermSet & vars_in_cex =
        cex->get_varset_sliced();

      // check loaded_predicates_
      for (const auto & p : loaded_predicates_) {
        smt::UnorderedTermSet vars_in_pred;
        smt::get_matching_terms(p, vars_in_pred, is_symbol_or_extract_symbol);
        
        if(is_subset(vars_in_pred, vars_in_cex))
          var_info_->preds_w_subset_vars.push_back(p);
        else if(has_intersection(vars_in_pred, vars_in_cex))
          var_info_->preds_w_related_vars.push_back(p);
      }

      // check internal_nodes_to_aiglit_map
      for (const auto & p : loaded_preds_from_aiger_) {
        smt::UnorderedTermSet vars_in_pred;
        smt::get_matching_terms(p, vars_in_pred, is_symbol_or_extract_symbol);
        
        if(is_subset(vars_in_pred, vars_in_cex))
          var_info_->preds_w_subset_vars.push_back(p);
        else if(has_intersection(vars_in_pred, vars_in_cex))
          var_info_->preds_w_related_vars.push_back(p);
      }
      var_info_->related_info_populated = true;
    }

    // compute the predicates to use below
    smt::TermVec predicates_to_use;
    {
      solver_->push();
      disable_all_labels();
      solver_->assert_formula(cex->to_expr(solver_));
      for (const auto & p : var_info_->preds_w_subset_vars) {
        auto r = solver_->check_sat_assuming({p});
        if (r.is_unsat())
          predicates_to_use.push_back(smart_not(p));
        else {
          r = solver_->check_sat_assuming({smart_not(p)});
          if (r.is_unsat())
            predicates_to_use.push_back(p);
        }
      }
      if (predicates_to_use.empty()) {
        for (const auto & p : var_info_->preds_w_related_vars) {
          auto r = solver_->check_sat_assuming({p});
          if (r.is_unsat())
            predicates_to_use.push_back(smart_not(p));
          else {
            r = solver_->check_sat_assuming({smart_not(p)});
            if (r.is_unsat())
              predicates_to_use.push_back(p);
          }
        }
      } // end of if predicates_to_use.empty()
      solver_->pop();
    }
    // TODO: from preds_w_subset_vars -> PerCexInfo::preds_to_use
    //  solve sat?
    sort_pred_in_extend_predicates(predicates_to_use);
    auto res = model_info_map_.emplace(cex, PerCexInfo(std::move(predicates_to_use)));
    model_info_pos = res.first;
  } // end of if not found in model_info_map_
  auto preds = model_info_pos->second.preds_to_use;
  auto num_preds = preds.size();
  preds.insert(preds.end(), conj_inout.begin(), conj_inout.end() );
  conj_inout.swap(preds);
  return num_preds;
} // end of extend_predicates

} // namespace pono

