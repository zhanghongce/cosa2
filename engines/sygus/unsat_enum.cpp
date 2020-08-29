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

// --------------------  eval_val ----------------

eval_val::eval_val(const std::string & val) {
  assert(val.find("#b") == 0);
  size_t pos = 2;
  for(; pos < val.length() ; ++ pos) {
    if ( val.at(pos) != '0' )
      break;
  }
  if (pos == val.length()) {
    // result 0
    type = type_t::NUM;
    nv = 0;
  } else {
    try {
      nv = ::cosa::sygus::StrToULongLong(val.substr(pos), 2);
      type = type_t::NUM;      
    } catch (...) {
      type = type_t::STR;
      sv = val.substr(pos);
    }
  }
} // eval_val::eval_val

bool eval_val::operator<(const eval_val &r) const {
  if (type == type_t::NUM && r.type == type_t::STR)
    return true;
  if (type == type_t::STR && r.type == type_t::NUM)
    return false;
  if (type == type_t::NUM)
    return nv < r.nv;
  // both str
  if (sv.length() < r.sv.length())
    return true;
  if (sv.length() > r.sv.length())
    return false;
  for(size_t pos = 0; pos < sv.length(); ++ pos) {
    if (sv.at(pos) == '0' && r.sv.at(pos) == '1')
      return true;
    if (sv.at(pos) == '1' && r.sv.at(pos) == '0')
      return false;
  }
  return false; // equal both string, same length and save val
}


Enumerator::cex_term_map_t  Enumerator::cex_term_map_;
  
void Enumerator::ClearCache() {
  cex_term_map_.clear();
}

// ----------------------------------------------------------------
//
//                         Enumerator
//
//                        Main Functions
//
// ----------------------------------------------------------------


Enumerator::Enumerator(
    to_next_t to_next_func,
    smt::SmtSolver & btor_solver,
    //smt::SmtSolver & msat_solver,
    const smt::Term & T_btor, const smt::Term & Init_btor, const smt::Term & Fprev_btor,
    const std::vector<Model *> & cexs,
    VarTermManager & var_term_extractor
    ):
      to_next_(to_next_func),
      solver_(btor_solver),
      trans_(T_btor), init_(Init_btor), prev_(Fprev_btor),
      cexs_(cexs), 
      per_cex_info_(setup_cex_info(var_term_extractor))
{
  if(per_cex_info_.predicates_nxt.empty()){
    terms_to_predicates();
  }
} // Enumerator::Enumerator

PerCexInfo & Enumerator::setup_cex_info(VarTermManager & var_term_extractor) {
  assert (cexs_.size() == 1);
  auto cex_ptr = cexs_.at(0);
  auto cex_term_map_pos = cex_term_map_.find(cex_ptr);
  if (cex_term_map_pos != cex_term_map_.end()) {
    return cex_term_map_pos->second;
  }

  cex_term_map_.insert(
    std::make_pair(cex_ptr, 
      PerCexInfo( var_term_extractor.GetAllTermsForVarsInModel(cex_ptr) )));

  PerCexInfo & per_cex_info = cex_term_map_.at(cex_ptr);

  GlobalTimer.RegisterEventStart("Enum.TermEval", 0);
  unsigned nterm = 0;

  // then evalute the terms on the cex
  solver_->push();
  solver_->assert_formula( cex_ptr->to_expr_btor(solver_) );
  auto res = solver_->check_sat();
  assert (res.is_sat());

  for (auto & width_term_const_pair : per_cex_info.varset_info.terms) {
    for (auto && t: width_term_const_pair.second.terms) {
      per_cex_info.terms_val_under_cex.insert(
        std::make_pair( t, eval_val( solver_->get_value(t)->to_raw_string() )));
      ++ nterm;
    }
    for (auto && c : width_term_const_pair.second.constants) {
      per_cex_info.terms_val_under_cex.insert(
        std::make_pair( c, c->to_raw_string() ));
      ++ nterm;
    }
  } // eval terms on cex

  solver_->pop();

  GlobalTimer.RegisterEventEnd("Enum.TermEval", nterm);
  // finally return it
  return per_cex_info;
} // setup_cex_info

void Enumerator::terms_to_predicates() {

#if TERM_TABLE_DEBUG_LVL >= 1
  
  for (auto && w_term_cnst_pair : per_cex_info_.varset_info.terms) {
    auto width = w_term_cnst_pair.first;
    const PerWidthInfo & terms_consts = w_term_cnst_pair.second;

    auto nt = terms_consts.terms.size();
    auto nc = terms_consts.constants.size();

    std::cout << "[Width = " << width << "] "
              << "[#Term = " << nt
              << ", #Consts = " << nc << "]\n";
    
    std::cout << "  C : ";
#if TERM_TABLE_DEBUG_LVL < 2
    if (nc == 0)
      std::cout << " (none) " << std::endl;
    else if (nc == 1)
      std::cout << ((terms_consts.constants.at(0))->to_string()) << " (1) "<< std::endl;
    else
      std::cout << (terms_consts.constants.front()->to_string()) << " .. "
                << (terms_consts.constants.back()->to_string()) <<  " (" << nc << ")" << std::endl;
#else
    for (auto && t : terms_consts.constants)
      std::cout << t->to_raw_string() << ", ";
    std::cout << " (" << nc << ")\n";
#endif
    
    std::cout << "  T : ";
#if TERM_TABLE_DEBUG_LVL < 2
    if (nc == 0)
      std::cout << " (none) " << std::endl;
    else if (nc == 1)
      std::cout << ((terms_consts.terms.at(0))->to_string()) << " (1) "<< std::endl;
    else
      std::cout << (terms_consts.terms.front()->to_string()) << " .. "
                << (terms_consts.terms.back()->to_string()) <<  " (" << nt << ")" << std::endl;
#else
    for (auto && t : terms_consts.terms)
      std::cout << t->to_raw_string() << ", ";
    std::cout << " (" << nt << ")\n";
#endif
    
  }
#endif

  GlobalTimer.RegisterEventStart("Enum.PredGen", per_cex_info_.predicates_nxt.size() );

  auto & preds = per_cex_info_.predicates_nxt;
  auto & next_to_curr = per_cex_info_.pred_next_to_pred_curr;
  for (auto && w_term_cnst_pair : per_cex_info_.varset_info.terms) {
    const PerWidthInfo & terms_consts = w_term_cnst_pair.second;
    // const - term
    for (const auto & c: terms_consts.constants) {
      const auto & cval = per_cex_info_.terms_val_under_cex.at(c);
      for (const auto & t: terms_consts.terms) {
        const auto & tval = per_cex_info_.terms_val_under_cex.at(t);
        
        auto pred_curr = (cval == tval) ? EQ(c, t) : NEQ(c, t);
        if (pred_curr->is_value())
          continue;
        auto pred_next = to_next_(pred_curr);
        next_to_curr.insert(std::make_pair(pred_next, pred_curr));
        preds.push_back(pred_next);
      }
    } // end of c-t
    
    const auto & terms = terms_consts.terms;
    auto sz = terms.size();
    for (size_t idx1 = 0; idx1 < sz; ++idx1 ) {
      const auto & t1 = terms.at(idx1);
      const auto & tval1 = per_cex_info_.terms_val_under_cex.at( t1 );
      for (size_t idx2 = idx1+1; idx2 < sz; ++idx2) {
        const auto & t2 = terms.at(idx2);
        const auto & tval2 = per_cex_info_.terms_val_under_cex.at( t2 );
        auto pred_curr = (tval1 == tval2) ? EQ(t1, t2) : NEQ(t1, t2);
        if (pred_curr->is_value())
          continue;
        auto pred_next = to_next_(pred_curr);
        next_to_curr.insert(std::make_pair(pred_next, pred_curr));
        preds.push_back(pred_next);
      }
    } // end of t-t
  } // end of w_term_cnst_pair

  GlobalTimer.RegisterEventEnd("Enum.PredGen", per_cex_info_.predicates_nxt.size() );

} // terms_to_predicates

// solver_->assert_formula(base_term);
// have base term in const smt::Term & base_term, 


smt::Term Enumerator::GetCandidate() {
  // (F/\T)\/INIT'
  // assert the predicates
  // get unsat core
  smt::Term base_term = OR( AND(prev_, trans_) ,to_next_(init_) );

  smt::TermVec inpreds (per_cex_info_.predicates_nxt.begin(), per_cex_info_.predicates_nxt.end());
  inpreds.push_back(base_term);

  D(0, "Enumerate: pred: {}", per_cex_info_.predicates_nxt.size());
  unsigned n_iter = 0;
  GlobalTimer.RegisterEventStart("Enum.SMTQuery", n_iter );

  do {

    solver_->push();

    // for(const auto & p: inpreds) {
    //   D(0, "Assert pred: {}, sort: {}", p->to_string(), p->get_sort()->to_string());
    // }
    
    ++ n_iter;
    D(0, "Unsat enum iter #{}, core size {} ", n_iter, inpreds.size());
    auto res = solver_->check_sat_assuming(inpreds);
    if (res.is_sat()) {
      // we cannot find a good set of predicates
#ifdef DEBUG
      DebugPredicates(inpreds, base_term, init_);
      assert (n_iter == 1);
#endif
      // debug  here
      solver_->pop();

      GlobalTimer.RegisterEventEnd("Enum.SMTQuery", n_iter );
      return nullptr; // no good candidates
    }
    smt::UnorderedTermSet unsat_core;
    solver_->get_unsat_core(unsat_core);
    solver_->pop();

    assert (unsat_core.size() <= inpreds.size());
    assert (!unsat_core.empty());
    for(const auto & p: unsat_core) {
      if (p == base_term)
        D(0, "Unsat base: (F/\\T)\\/INIT' ");
      else
        D(0, "Unsat pred: {}", p->to_raw_string());
    }
    
    if (unsat_core.size() == inpreds.size()) {
      D(0, "Unsat enum done, iter {}, core size {}", n_iter, unsat_core.size());
      break;
    } // else continue

    inpreds.clear();
    inpreds.insert(inpreds.begin(), unsat_core.begin(), unsat_core.end());
  } while(GlobalAPdrConfig.UNSAT_CORE_RUN_MULITTIMES);

  GlobalTimer.RegisterEventEnd("Enum.SMTQuery", n_iter );

  if (n_iter <= 2) { 
    // the second time is the same as first time
    // in case of GlobalAPdrConfig.UNSAT_CORE_RUN_MULITTIMES
    // n_iter == 1, this is also no iter
    GlobalTimer.RegisterEventCount("Enum.UnsatNoIter", 1);
  } else 
    GlobalTimer.RegisterEventCount("Enum.UnsatIter", 1);

  bool base_term_in = false;
  smt::Term ret = nullptr;
  for (const auto & t : inpreds) {
    if (t == base_term)
      base_term_in = true;
    else {
      auto t_curr = per_cex_info_.pred_next_to_pred_curr.at(t);
      if (ret == nullptr)
        ret = t_curr;
      else
        ret = AND(ret, t_curr);
    }
  }
  assert (base_term_in);
  assert (ret != nullptr);
  return NOT(ret);

} // GetCandidate

void Enumerator::DebugPredicates(const smt::TermVec & inpreds, const smt::Term & base, const smt::Term & init) {

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
  D(0, "INIT : {} ", solver_->get_value(init)->to_string());
  D(0, "( F /\\ T ) \\/ (INIT') : {} ", solver_->get_value(base)->to_string());

  std::unordered_set<smt::Term> varset;
  cexs_.at(0)->get_varset(varset);
  Model m(solver_, varset);
  // for all vars get the model
  D(0, "The model is: {}", m.to_string() );
  D(0, "The cex model related to this is: {}", cexs_.at(0)->to_string() );

  assert (base_term_in);

  // -----------------------------------------------------------------
  // see if any p can block m
  solver_->pop();
  solver_->push();
  solver_->assert_formula(m.to_expr_btor(solver_));
  auto res = solver_->check_sat();
  assert(res.is_sat());
  
  D(0, "-------------------------------");
  unsigned idx =0;
  smt::TermVec preds_to_try;
  for (const auto & p : inpreds) {
    if (p == base) {
      continue;
    } else {
      auto t_curr = per_cex_info_.pred_next_to_pred_curr.at(p);
      auto pred_res = solver_->get_value(t_curr)->to_int();
      if (pred_res == 1) {
        preds_to_try.push_back(NOT(t_curr));
        D(0, "NOT({}) on s: {} ", t_curr->to_raw_string(), "False");
        idx ++;
      }
    }
  }
  D(0, "-------------Total : {} ------------------", idx);

  // see if /\ not(p) will have something there
  // -----------------------------------------------------------------
  solver_->pop();
  solver_->push();
  
  res = solver_->check_sat_assuming(preds_to_try);
  D(0,"AND of (not p) sat? : {}", res.is_sat());
  if (res.is_unsat()) {
    smt::UnorderedTermSet unsatcore;
    solver_->get_unsat_core(unsatcore);
    D(0, "-------------Unsat core : {} ------------------", unsatcore.size());
    for (const auto & p : unsatcore)
      D(0, "{}", p->to_raw_string());
    D(0, "-----------------------------------------------", unsatcore.size());    
  }


} // DebugPredicates

    

} // namespace sat_enum

} // namespace cosa
