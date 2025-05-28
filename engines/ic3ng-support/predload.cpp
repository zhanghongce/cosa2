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

// s 00 a 0001 b 0011
// s ==00 ->  a > b   a == b a>=b 
unsigned IC3ng::extend_predicates(Model *cex, smt::TermVec & conj_inout) {
  auto model_info_pos = model_info_map_.find(cex);
  PerUnslicedVarInfo * var_info = cex->get_per_unslicedvar_info();

  if (model_info_pos == model_info_map_.end()) {
    if (!var_info->related_info_populated) {
      const smt::UnorderedTermSet & vars_in_cex =
        cex->get_varset_unslice();

      for (const auto & p : loaded_predicates_) {
        smt::UnorderedTermSet vars_in_pred;
        smt::get_free_symbolic_consts(p, vars_in_pred);
        
        // First check if it has any intersection with cex vars
        if(has_intersection(vars_in_pred, vars_in_cex)) {
          // Then check if it's a complete subset
          if(is_subset(vars_in_pred, vars_in_cex)) {
            var_info->preds_w_subset_vars.push_back(p);
          } else {
            // Has intersection but not subset - these are the related vars
            var_info->preds_w_related_vars.push_back(p);
          }
        }
      } // end of for each load_predicates_
      var_info->related_info_populated = true;
    }

    // Calculate predicates to use
    smt::TermVec predicates_to_use;
    {
      solver_->push();
      disable_all_labels();
      solver_->assert_formula(cex->to_expr(solver_));

      // First check subset vars, double check
      for (const auto & p : var_info->preds_w_subset_vars) {
        // check p
        auto r = solver_->check_sat_assuming({p});
        if (r.is_unsat()) {
          predicates_to_use.push_back(smart_not(p));
          continue;
        }
        // check not(p)
        r = solver_->check_sat_assuming({smart_not(p)});
        if (r.is_unsat()) {
          predicates_to_use.push_back(p);
        }
      }

      // HZ: is this substitution really helpful?
      // always handle related vars, no matter how many subset vars found
      const auto & vars_in_cex = cex->get_varset_unslice();
      for (const auto & p : var_info->preds_w_related_vars) {
        // achieve the vars in p but not in cex
        smt::UnorderedTermSet vars_in_pred;
        smt::get_free_symbolic_consts(p, vars_in_pred);
        smt::UnorderedTermSet external_vars; // external_vars = vars_in_pred - vars_in_cex
        for (const auto & v : vars_in_pred) {
          if (vars_in_cex.find(v) == vars_in_cex.end()) {
            external_vars.insert(v);
          }
        }

        // Try different values for each external variable
        bool found_useful = false;
        for (const auto & ext_var : external_vars) {
          // Get the sort of the variable
          auto var_sort = ext_var->get_sort();
          
          // Try special values based on the bit-width
          std::vector<int64_t> test_values;
          if (var_sort->get_sort_kind() == smt::BV) {
            uint32_t width = var_sort->get_width();
            test_values = {0, 1};  // Always safe values
            if (width > 1) {
              test_values.push_back((1ll << (width-1)) - 1);  // Maximum positive value
              test_values.push_back(-(1ll << (width-1)));     // Minimum negative value
            }
          } else {
            // For non-bitvector sorts, use simple values
            test_values = {0, 1, -1};
          }
          
          for (auto val : test_values) {
            try {
              // Create a constant of appropriate width
              auto const_val = solver_->make_term(val, var_sort);
              
              // Create substitution map
              smt::UnorderedTermMap subst_map;
              subst_map[ext_var] = const_val;
              
              // Create terms vector with single term
              smt::TermVec terms;
              terms.push_back(p);
              
              // Replace the external variable
              auto subst_terms = solver_->substitute_terms(terms, subst_map);
              auto subst_p = subst_terms[0];  // We only substituted one term
              
              // Check the substituted predicate (bi-directional check)
              auto r1 = solver_->check_sat_assuming({subst_p});
              if (r1.is_unsat()) {
                predicates_to_use.push_back(smart_not(subst_p));
                found_useful = true;
                break;
              }
              
              auto r2 = solver_->check_sat_assuming({smart_not(subst_p)});
              if (r2.is_unsat()) {
                predicates_to_use.push_back(subst_p);
                found_useful = true;
                break;
              }
            } catch (const std::exception & e) {
              // If we get an exception creating the constant, skip this value
              continue;
            }
          }
          
          if (found_useful) break;
        }
      }
      solver_->pop();
    }

    auto res = model_info_map_.emplace(cex, PerCexInfo(std::move(predicates_to_use)));
    model_info_pos = res.first;
  }

  auto preds = model_info_pos->second.preds_to_use;
  auto num_preds = preds.size();

  if (num_preds == 0) {
    // if we find no additional predicates, we will just return
    return 0;
  }
  // conj_inout := VectorConcat(preds, conj_inout)
  preds.insert(preds.end(), conj_inout.begin(), conj_inout.end());
  conj_inout.swap(preds);

  // print all the predicates
  std::cout << "\n=== Extended Predicates Analysis ===\n";
  
  // Print variables in cex
  const auto & vars_in_cex = cex->get_varset_unslice();
  std::cout << "Variables in counterexample:\n";
  for (const auto & v : vars_in_cex) {
    std::cout << "  " << v->to_string() << " [sort: " << v->get_sort()->to_string() << "]\n";
  }

  // Print original predicates
  std::cout << "\nOriginal predicates from external source:\n";
  for (const auto & p : loaded_predicates_) {
    std::cout << "  " << p->to_string() << "\n";
  }

  // Print subset vars predicates
  std::cout << "\nPredicates with subset vars (vars fully in cex):\n";
  for (const auto & p : var_info->preds_w_subset_vars) {
    // Get variables in this predicate
    smt::UnorderedTermSet vars_in_pred;
    smt::get_free_symbolic_consts(p, vars_in_pred);
    
    std::cout << "  Pred: " << p->to_string() << "\n";
    std::cout << "    Variables: ";
    for (const auto & v : vars_in_pred) {
      std::cout << v->to_string() << " ";
    }
    std::cout << "\n";
  }

  // Print related vars predicates and their substitutions
  std::cout << "\nPredicates with related vars:\n";
  for (const auto & p : var_info->preds_w_related_vars) {
    // Get variables in this predicate
    smt::UnorderedTermSet vars_in_pred;
    smt::get_free_symbolic_consts(p, vars_in_pred);
    
    std::cout << "  Pred: " << p->to_string() << "\n";
    std::cout << "    All vars: ";
    for (const auto & v : vars_in_pred) {
      std::cout << v->to_string() << " ";
    }
    std::cout << "\n    External vars: ";
    for (const auto & v : vars_in_pred) {
      if (vars_in_cex.find(v) == vars_in_cex.end()) {
        std::cout << v->to_string() << " ";
      }
    }
    std::cout << "\n";
  }

  // Print final selected predicates
  std::cout << "\nFinal selected predicates:\n";
  for (const auto & p : conj_inout) {
    std::cout << "  " << p->to_string() << "\n";
  }

  std::cout << "\nTotal predicates selected: " << num_preds << "\n";
  std::cout << "================================\n\n";
  
  return num_preds;
} // end of extend_predicates

} // namespace pono
