/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The Unsat core based Enumerator
 **
 ** 
 **/

#include "engines/apdr/config.h"
#include "unsat_enum.h"

#include "utils/container_shortcut.h"
#include "utils/term_analysis.h"
#include "utils/logger.h"
#include "utils/str_util.h"
#include "utils/multitimer.h"

#include <cassert>

#define AND(x, y)    (solver_->make_term(smt::And, (x), (y)))
#define OR(x, y)     (solver_->make_term(smt::Or, (x), (y)))
#define NOT(x)       (solver_->make_term(smt::Not, (x)))
#define EQ(x, y)     (solver_->make_term(smt::Equal, (x), (y)))
#define NEQ(x, y)     (NOT(EQ( (x) , (y) )))



#define DEBUG
#ifdef DEBUG
  #define D(...) logger.log( __VA_ARGS__ )
  #define INFO(...) D(0, __VA_ARGS__)
#else
  #define D(...) do {} while (0)
  #define INFO(...) logger.log(1, __VA_ARGS__)
#endif

#define TERM_TABLE_DEBUG_LVL 2

namespace cosa {

namespace unsat_enum {


cex_term_map_t  Enumerator::cex_term_map_;
  

// ----------------------------------------------------------------
//
//                         Enumerator
//
//                        Main Functions
//
// ----------------------------------------------------------------


Enumerator::Enumerator(
    to_next_t to_next_func,
    extract_model_t extract_model_func,
    smt::SmtSolver & btor_solver,
    //smt::SmtSolver & msat_solver,
    const smt::Term & T_btor, const smt::Term & Init_btor, const smt::Term & Fprev_btor,
    Model * cex,
    VarTermManager & var_term_extractor
    ):
      to_next_(to_next_func),
      extract_model_(extract_model_func),
      solver_(btor_solver),
      trans_(T_btor), init_(Init_btor), prev_(Fprev_btor),
      cex_(cex), 
      per_cex_info_(setup_cex_info(var_term_extractor))
{ // you need to make this incremental
  TermsDumping();
  terms_to_predicates();
} // Enumerator::Enumerator

// will not update : Question when to update ?

PerCexInfo & Enumerator::setup_cex_info(VarTermManager & var_term_extractor) {
  assert (cex_);
  auto cex_ptr = cex_;
  auto cex_term_map_pos = cex_term_map_.find(cex_ptr);
  if (cex_term_map_pos == cex_term_map_.end()) {
    bool nouse;
    std::tie(cex_term_map_pos ,  nouse) =
      cex_term_map_.emplace(cex_ptr, 
          PerCexInfo( var_term_extractor.GetAllTermsForVarsInModel(cex_ptr) ));
  }

  PerCexInfo & per_cex_info = cex_term_map_pos->second;

  GlobalTimer.RegisterEventStart("Enum.TermEval", 0);
  unsigned nterm = 0;

  // then evalute the terms on the cex
  solver_->push();
  solver_->assert_formula( cex_ptr->to_expr_btor(solver_) );
  auto res = solver_->check_sat();
  assert (res.is_sat());

  for (const auto & width_term_const_pair : per_cex_info.varset_info.terms) {
    auto width = width_term_const_pair.first;
    unsigned nc = per_cex_info.prev_per_width_term_num[width].const_num; // when to update this
    unsigned nt = per_cex_info.prev_per_width_term_num[width].term_num;
    auto nt_end = width_term_const_pair.second.terms.size();
    auto nc_end = width_term_const_pair.second.constants.size();
    // cache the terms and constants value under the cex
    for (unsigned tidx = nt; tidx < nt_end ; ++tidx) {
      const auto & t = width_term_const_pair.second.terms.at(tidx);
      per_cex_info.terms_val_under_cex.emplace(
        t, eval_val( solver_->get_value(t)->to_raw_string() ));
      ++ nterm;
    }
    for (unsigned cidx = nc ; cidx <  nc_end; ++cidx) {
      const auto & c = width_term_const_pair.second.constants.at(cidx);
      per_cex_info.terms_val_under_cex.emplace(
        c, c->to_raw_string() );
      ++ nterm;
    }
  } // eval terms on cex

  solver_->pop();

  GlobalTimer.RegisterEventEnd("Enum.TermEval", nterm);
  // finally return it
  return per_cex_info;
} // setup_cex_info

void Enumerator::TermsDumping() const {
#if TERM_TABLE_DEBUG_LVL >= 1
  
  for (auto && w_term_cnst_pair : per_cex_info_.varset_info.terms) {
    auto width = w_term_cnst_pair.first;
    const PerWidthInfo & terms_consts = w_term_cnst_pair.second;

    auto nt_size = terms_consts.terms.size();
    auto nc_size = terms_consts.constants.size();

    std::cout << "[Width = " << width << "] "
              << "[#Term = " << nt_size
              << ", #Consts = " << nc_size << "]\n";
    
    std::cout << "  C : ";
#if TERM_TABLE_DEBUG_LVL < 2
    if (nc_size == 0)
      std::cout << " (none) " << std::endl;
    else if (nc_size == 1)
      std::cout << ((terms_consts.constants.at(0))->to_string()) << " (1) "<< std::endl;
    else
      std::cout << (terms_consts.constants.front()->to_string()) << " .. "
                << (terms_consts.constants.back()->to_string()) <<  " (" << nc_size << ")" << std::endl;
#else
    for (auto && t : terms_consts.constants)
      std::cout << t->to_raw_string() << ", ";
    std::cout << " (" << nc_size << ")\n";
#endif
    
    std::cout << "  T : ";
#if TERM_TABLE_DEBUG_LVL < 2
    if (nt_size == 0)
      std::cout << " (none) " << std::endl;
    else if (nt_size == 1)
      std::cout << ((terms_consts.terms.at(0))->to_string()) << " (1) "<< std::endl;
    else
      std::cout << (terms_consts.terms.front()->to_string()) << " .. "
                << (terms_consts.terms.back()->to_string()) <<  " (" << nt_size << ")" << std::endl;
#else
    for (auto && t : terms_consts.terms)
      std::cout << t->to_raw_string() << ", ";
    std::cout << " (" << nt_size << ")\n";
#endif
    
  }
#endif
} // term dumping

void Enumerator::terms_to_predicates() {

  GlobalTimer.RegisterEventStart("Enum.PredGen", per_cex_info_.predicates_nxt.size() );

  auto & preds = per_cex_info_.predicates_nxt;
  auto & next_to_curr = per_cex_info_.pred_next_to_pred_curr;
  const auto & value_map = per_cex_info_.terms_val_under_cex;
  for (auto && w_term_cnst_pair : per_cex_info_.varset_info.terms) {
    // const - term
    auto width = w_term_cnst_pair.first;
    const PerWidthInfo & terms_consts = w_term_cnst_pair.second;
    const auto & terms = terms_consts.terms;
    const auto & constants = terms_consts.constants;

    unsigned nc = per_cex_info_.prev_per_width_term_num[width].const_num;
    unsigned nt = per_cex_info_.prev_per_width_term_num[width].term_num;
    auto nt_size = terms.size();
    auto nc_size = constants.size();

    for (unsigned cidx = 0; cidx < nc_size; ++ cidx ) {
      const auto & c = constants.at(cidx);
      const auto & cval = value_map.at(c);
      for (unsigned tidx = (cidx < nc ? nt : 0); // if c is an old one, we will start from new terms
           tidx < nt_size; ++ tidx) {            // else we can also use old terms
        const auto & t = terms.at(tidx);
        const auto & tval = value_map.at(t);
        
        auto pred_curr = (cval == tval) ? EQ(c, t) : NEQ(c, t);
        if (pred_curr->is_value())
          continue;
        auto pred_next = to_next_(pred_curr);
        next_to_curr.emplace(pred_next, pred_curr);
        preds.push_back(pred_next);
      }
    } // end of c-t
    
    for (size_t idx1 = 0; idx1 < nt_size; ++idx1 ) {
      const auto & t1 = terms.at(idx1);
      const auto & tval1 = value_map.at( t1 );
      for (size_t idx2 = (idx1 < nt ? nt : idx1 + 1);  // we must pick a new one
        idx2 < nt_size; ++idx2) {

        const auto & t2 = terms.at(idx2);
        const auto & tval2 = value_map.at( t2 );
        auto pred_curr = (tval1 == tval2) ? EQ(t1, t2) : NEQ(t1, t2);
        if (pred_curr->is_value())
          continue;
        auto pred_next = to_next_(pred_curr);
        next_to_curr.emplace(pred_next, pred_curr);
        preds.push_back(pred_next);
      }
    } // end of t-t

    // update record
    per_cex_info_.prev_per_width_term_num[width].const_num = nc_size;
    per_cex_info_.prev_per_width_term_num[width].term_num = nt_size;
  } // end of w_term_cnst_pair

  GlobalTimer.RegisterEventEnd("Enum.PredGen", per_cex_info_.predicates_nxt.size() );
} // terms_to_predicates

// solver_->assert_formula(base_term);
// have base term in const smt::Term & base_term, 

void Enumerator::DebugRegAllpred(const smt::UnorderedTermSet & inpreds) {
  unsigned idx = 0;
  for (const auto & t : inpreds) {
    pred_to_numbers.emplace(t,idx++);
  }
  std::cerr << "Total pred: #" << idx << std::endl;
}

void Enumerator::DebugRegSelRemove(const smt::Term & sel, const std::string & action) {
  auto pos = pred_to_numbers.find(sel);
  assert(pos != pred_to_numbers.end());
  std::cerr << "  -> " << action << " no. " << pos->second << std::endl;
}

void Enumerator::DebugRegResult(const smt::UnorderedTermSet & res) {
  std::cerr << "     result : {" ;
  for (const auto & p : res) {
    auto pos = pred_to_numbers.find(p);
    assert(pos != pred_to_numbers.end());
    std::cerr << pos->second << ", ";
  }
  std::cerr << "}" << std::endl;
}

bool Enumerator::CheckPrepointNowHasPred(Model * m) {
  smt::Term Prepoint = m->to_expr_btor(solver_);
  smt::Term F_and_T = AND(prev_, trans_);
  smt::Term base_term = OR( AND(Prepoint, F_and_T) ,to_next_(init_) );
  //smt::UnorderedTermSet inpreds (.begin(), per_cex_info_.predicates_nxt.end());
  //inpreds.insert(base_term);
  solver_->push();
  solver_->assert_formula(base_term);
  for (const auto & p : per_cex_info_.predicates_nxt) {
    solver_->assert_formula(p);
    D(0, "Assert : {}", p->to_string() );
  }
  auto res = solver_->check_sat();
  solver_->pop();
  return res.is_unsat();
}

// if n == 0, will get all
// if cands is empty: no good predicates
void Enumerator::GetNCandidates(smt::TermVec & cands, size_t n) {

  smt::Term F_and_T = AND(prev_, trans_);
  smt::Term base_term = OR( F_and_T ,to_next_(init_) );
  smt::UnorderedTermSet inpreds (per_cex_info_.predicates_nxt.begin(), per_cex_info_.predicates_nxt.end());
  DebugRegAllpred(inpreds);
  inpreds.insert(base_term);
  unsigned init_preds_n = inpreds.size();
  
  struct stack_state {
    smt::UnorderedTermSet choice_set;
    smt::UnorderedTermSet::iterator pos;
    stack_state(const smt::UnorderedTermSet & in) : choice_set(in), pos(choice_set.begin())  {
      assert(pos != choice_set.end());
    } };
  std::vector<stack_state> stack; // we don't need to copy inpreds, we only need to 

  // first round
  smt::UnorderedTermSet init_choice; // base term is already removed from it
  GetOneCandidate( /*in*/ inpreds, /*out*/ init_choice, /*in*/ base_term, /*IN*/ F_and_T, true);
  if (init_choice.empty()) {
    return; // no good pred
  }
  DebugRegResult(init_choice);
  // assemble the output HERE
  cands.push_back(AssembleCandFromUnsatCore(base_term, init_choice));
  stack.push_back(init_choice);

  while(n == 0 || (cands.size() < n) ) {
    // change inpreds to not include the one under pos
    assert (stack.back().pos != stack.back().choice_set.end());
    assert(IN(*(stack.back().pos), inpreds));
    DebugRegSelRemove(*(stack.back().pos), "remove");
    inpreds.erase(*(stack.back().pos));

    smt::UnorderedTermSet choice_set;
    GetOneCandidate( /*in*/ inpreds, /*out*/ choice_set, /*in*/ base_term, /*IN*/ F_and_T, false);
    DebugRegResult(choice_set);

    if (choice_set.empty()) { // bad attempt : becomes sat
      assert(!IN(*(stack.back().pos), inpreds));
      DebugRegSelRemove(*(stack.back().pos), "insert");
      inpreds.insert( *(stack.back().pos) ); // add it back
      ++ stack.back().pos; // move iterator to next candidate

      while( !stack.empty() && stack.back().pos == stack.back().choice_set.end()) {
        stack.pop_back();
        if (!stack.empty()) {
          assert(!IN(*(stack.back().pos), inpreds));

          DebugRegSelRemove(*(stack.back().pos), "insert");
          inpreds.insert( *(stack.back().pos) );
          ++ stack.back().pos;
        }
      }; // backtrack
      if (stack.empty()) {
        assert(inpreds.size() == init_preds_n); // we should have been add/remove properly
        return;
      }
    } else {
      // make the output
      cands.push_back(AssembleCandFromUnsatCore(base_term, choice_set));
      stack.push_back(stack_state(choice_set));
    }
    // if choice_set is empty, we need to backtrack
    // else push the choice and foreach one remove it from inpreds
  }  // while (get n cands)
} // GetAllCandidates

void Enumerator::GetOneCandidate(const smt::UnorderedTermSet & in, smt::UnorderedTermSet & unsatcore, 
  const smt::Term & base_term, const smt::Term & F_and_T, bool first_check) {

  unsatcore.clear();
  unsatcore.insert(in.begin(), in.end());

  D(0, "Enumerate: pred: {}", unsatcore.size());
  unsigned n_iter = 0;
  GlobalTimer.RegisterEventStart("Enum.SMTQuery", n_iter );

  do {

    solver_->push();

    // for(const auto & p: inpreds) {
    //   D(0, "Assert pred: {}, sort: {}", p->to_string(), p->get_sort()->to_string());
    // }
    
    ++ n_iter;
    D(0, "Unsat enum iter #{}, core size {} ", n_iter, unsatcore.size());
    auto res = solver_->check_sat_assuming(unsatcore);
    if (res.is_sat()) {
      // we cannot find a good set of predicates
      assert (n_iter == 1);

      if (first_check) {
        DebugPredicates(in, base_term, init_, false);

        std::unordered_set<smt::Term> varset;
        cex_->get_varset(varset);
        bool fail_at_init = check_failed_at_init(F_and_T);
        extract_model_(varset, fail_at_init); // must before pop
        // will replace var to its prime and then use the next part
        // inside it will store the model to a necesary place
      }
      solver_->pop();

      GlobalTimer.RegisterEventEnd("Enum.SMTQuery", n_iter );
      unsatcore.clear();
      return; // no good candidates
    }

    auto old_size = unsatcore.size();
    unsatcore.clear();
    solver_->get_unsat_core(unsatcore);
    solver_->pop();

    assert (unsatcore.size() <= old_size);
    assert (!unsatcore.empty());
    assert(IN(base_term, unsatcore)); // otherwise just the conjunction of preds are unsat
    // if dump
    for(const auto & p: unsatcore) {
      if (p == base_term)
        D(0, "Unsat base: (F/\\T)\\/INIT' ");
      else
        D(0, "Unsat pred: {}", p->to_raw_string());
    }
    
    if (unsatcore.size() == old_size) {
      D(0, "Unsat enum done, iter {}, core size {}", n_iter, unsatcore.size());
      break;
    } // else continue to shrink

    //inpreds.insert(inpreds.begin(), unsat_core.begin(), unsat_core.end());
  } while(GlobalAPdrConfig.UNSAT_CORE_RUN_MULITTIMES);

  GlobalTimer.RegisterEventEnd("Enum.SMTQuery", n_iter );

  assert(IN(base_term, unsatcore));
  unsatcore.erase(base_term);
  assert(!unsatcore.empty());
} // GetOneCandidate

// base term should already been removed
smt::Term Enumerator::AssembleCandFromUnsatCore(const smt::Term & base_term, const smt::UnorderedTermSet & unsatcore) {
  //bool base_term_in = false;
  smt::Term ret = nullptr;
  for (const auto & t : unsatcore) {
    assert (t != base_term);
      //base_term_in = true;
    auto t_curr = per_cex_info_.pred_next_to_pred_curr.at(t);
    if (ret == nullptr)
      ret = t_curr;
    else
      ret = AND(ret, t_curr);
  }
  assert (ret); // unsatcore should not be empty
  return NOT(ret);
} // AssembleCandFromSet


// (F/\T) \/ init'
// we want to favor the init case
bool Enumerator::check_failed_at_init(const smt::Term & F_and_T) {
  auto init_val = solver_->get_value(to_next_(init_))->to_int();
  if (init_val)
    return true;

  auto F_and_T_val = solver_->get_value(F_and_T)->to_int();
  assert(F_and_T_val);
  return false;
}


void Enumerator::DebugPredicates(const smt::UnorderedTermSet & inpreds, const smt::Term & base, const smt::Term & init, bool rm_pre) {

  bool base_term_in = false;
  for (const auto & p : inpreds) {
    if (p == base) {
      base_term_in = true;
    } else {
      auto t_curr = per_cex_info_.pred_next_to_pred_curr.at(p);
      D(0, "{} on s': {} ", t_curr->to_raw_string(), solver_->get_value(p)->to_string());
    }
  }

  // finally print base and init
  D(0, "INIT' : {} ", solver_->get_value(to_next_(init))->to_string());
  const char * info = rm_pre ? "( not (/\\p) /\\ F /\\ T ) \\/ (INIT') : {} " : "( F /\\ T ) \\/ (INIT') : {} " ;
  D(0, info, solver_->get_value(base)->to_string());

} // DebugPredicates



bool Enumerator::CheckPredDisjFailInit() {
  solver_->push();
  for (const auto & primeP : per_cex_info_.predicates_nxt ) {
    solver_->assert_formula(primeP);
  }
  solver_->assert_formula(to_next_(init_));
  auto res = solver_->check_sat();
  if (res.is_sat()) {
      std::unordered_set<smt::Term> varset;
      cex_->get_varset(varset);
      extract_model_(varset, true);
  }
  solver_->pop();
  return res.is_sat();
}

// if n == 0, will get all
// if cands is empty: no good predicates
void Enumerator::GetNCandidatesRemoveInPrev(smt::TermVec & cands, size_t n) {

  if ( CheckPredDisjFailInit() )
    return;

  smt::Term F_and_T = AND(prev_, trans_);
  //smt::Term Pre_not_conj = NOT(ANDN_pre(per_cex_info_.predicates_nxt));
  // convert predicates_nxt to unprimed ones and and them together

  //smt::Term init_base_term = OR( AND(Pre_not_conj, F_and_T) ,to_next_(init_) );
  smt::UnorderedTermSet inpreds (per_cex_info_.predicates_nxt.begin(), per_cex_info_.predicates_nxt.end());
  // inpreds.insert(init_base_term); // in preds will not include base_term
  // will assemble that in GetOneCandidateRemoveInPrev
  unsigned init_preds_n = inpreds.size();
  
  struct stack_state {
    smt::UnorderedTermSet choice_set;
    smt::UnorderedTermSet::iterator pos;
    stack_state(const smt::UnorderedTermSet & in) : choice_set(in), pos(choice_set.begin())  {
      assert(pos != choice_set.end());
    } };
  std::vector<stack_state> stack; // we don't need to copy inpreds, we only need to 

  // first round
  smt::UnorderedTermSet init_choice; // base term is already removed from it
  auto new_base = GetOneCandidateRemoveInPrev( /*in*/ inpreds, /*out*/ init_choice,  /*IN*/ F_and_T, true);
  if (init_choice.empty()) {
    return; // no good pred
  }
  // assemble the output HERE
  cands.push_back(AssembleCandFromUnsatCore(new_base, init_choice));
  stack.push_back(init_choice);

  while(n == 0 || (cands.size() < n) ) {
    // change inpreds to not include the one under pos
    assert (stack.back().pos != stack.back().choice_set.end());
    assert(IN(*(stack.back().pos), inpreds));
    inpreds.erase(*(stack.back().pos));

    smt::UnorderedTermSet choice_set;
    new_base = GetOneCandidateRemoveInPrev( /*in*/ inpreds, /*out*/ choice_set,  /*IN*/ F_and_T, false);
    if (choice_set.empty()) { // bad attempt : becomes sat
      assert(!IN(*(stack.back().pos), inpreds));
      inpreds.insert( *(stack.back().pos) ); // add it back
      ++ stack.back().pos; // move iterator to next candidate

      while( !stack.empty() && stack.back().pos == stack.back().choice_set.end()) {
        stack.pop_back();
        if (!stack.empty()) {
          assert(!IN(*(stack.back().pos), inpreds));
          inpreds.insert( *(stack.back().pos) );
          ++ stack.back().pos;
        }
      }; // backtrack
      if (stack.empty()) {
        assert(inpreds.size() == init_preds_n); // we should have been add/remove properly
        return;
      }
    } else {
      // make the output
      cands.push_back(AssembleCandFromUnsatCore(new_base, choice_set));
      stack.push_back(stack_state(choice_set));
    }
    // if choice_set is empty, we need to backtrack
    // else push the choice and foreach one remove it from inpreds
  }  // while (get n cands)
} // GetAllCandidates

smt::Term Enumerator::GetOneCandidateRemoveInPrev(const smt::UnorderedTermSet & in, smt::UnorderedTermSet & unsatcore, 
  const smt::Term & F_and_T, bool first_check) {

  unsatcore.clear();
  unsatcore.insert(in.begin(), in.end());
  smt::Term Pre_not_conj = NOT(ANDN_pre(unsatcore));
  smt::Term base = OR( AND(Pre_not_conj, F_and_T) ,to_next_(init_) );
  unsatcore.insert(base);

  D(0, "Enumerate: pred: {}", unsatcore.size());
  unsigned n_iter = 0;
  GlobalTimer.RegisterEventStart("Enum.SMTQuery", n_iter );

  do {

    solver_->push();

    // for(const auto & p: inpreds) {
    //   D(0, "Assert pred: {}, sort: {}", p->to_string(), p->get_sort()->to_string());
    // }
    
    ++ n_iter;
    D(0, "Unsat enum iter #{}, core size {} ", n_iter, unsatcore.size());
    auto res = solver_->check_sat_assuming(unsatcore);
    if (res.is_sat()) {
      // we cannot find a good set of predicates
      if (n_iter != 1) {
        std::cerr << "---------- DUMPING constraints ---------" << unsatcore.size() << std::endl;
        unsigned idx = 0;
        for (const auto & p : unsatcore) {
          std::cerr << ">>> p" << idx << (p == base ? 'b' : ' ')  << " : " << p->to_raw_string() << std::endl;
          idx ++;
        }
      }
      assert (n_iter == 1);

      if (first_check) {
        DebugPredicates(in, base, init_, true); // rm_pre

        std::unordered_set<smt::Term> varset;
        cex_->get_varset(varset);
        bool fail_at_init = check_failed_at_init(F_and_T); // it is okay to not pass /\\ not (/\\ p)
        assert(!fail_at_init); // o.w. we should have catch it earlier

        extract_model_(varset, fail_at_init); // must before pop
      }
      // will replace var to its prime and then use the next part
      // inside it will store the model to a necesary place
      solver_->pop();

      GlobalTimer.RegisterEventEnd("Enum.SMTQuery", n_iter );
      unsatcore.clear();
      return nullptr; // no good candidates
    }

    auto old_size = unsatcore.size();
    unsatcore.clear();
    solver_->get_unsat_core(unsatcore);
    solver_->pop();

    assert (unsatcore.size() <= old_size);
    assert (!unsatcore.empty());
    assert(IN(base, unsatcore)); // otherwise just the conjunction of preds are unsat
    // if dump
    for(const auto & p: unsatcore) {
      if (p == base)
        D(0, "Unsat base: (F/\\T)\\/INIT' ");
      else
        D(0, "Unsat pred: {}", p->to_raw_string());
    }
    
    if (unsatcore.size() == old_size) {
      D(0, "Unsat enum done, iter {}, core size {}", n_iter, unsatcore.size());
      break;
    } // else continue to shrink

    // remove the base term and change it to a new one
    unsatcore.erase(base);

    Pre_not_conj = NOT(ANDN_pre(unsatcore)); // in unsatcore are all cand(s')
    base = OR( AND(Pre_not_conj, F_and_T) ,to_next_(init_) );

    unsatcore.insert(base);
    
  } while(GlobalAPdrConfig.UNSAT_CORE_RUN_MULITTIMES);

  GlobalTimer.RegisterEventEnd("Enum.SMTQuery", n_iter );

  assert(IN(base, unsatcore));
  unsatcore.erase(base);
  assert(!unsatcore.empty());
  return base;
} // GetOneCandidate


template <class T> smt::Term Enumerator::ANDN_pre(const T & prime_p)
{
    smt::Term ret = nullptr;
    for (const auto & p : prime_p) {
      const smt::Term & t = per_cex_info_.pred_next_to_pred_curr.at(p);
      if (ret == nullptr)
        ret = t;
      else
        ret = AND(ret, t);
    }
    assert(ret);
    return ret;
  }


} // namespace unsat_enum

} // namespace cosa
