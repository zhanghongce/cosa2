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
#include "ast_knob/term_score.h"

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

#define TERM_TABLE_DEBUG_LVL 0

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
      if (width <= 1 && cidx >= 1)
        break; // you don't need a != 1 and a == 0, you only need to keep 1 value
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
    // D(0, "Assert : {}", p->to_string() );
  }
  auto res = solver_->check_sat();
  solver_->pop();
  return res.is_unsat();
}


static void insert_preds_score_descending(const smt::UnorderedTermSet & initial_core, 
  std::list<smt::Term> & pred_sets, std::list<unsigned> & pred_scores)
{ 
  std::vector<std::pair<unsigned, smt::Term>> score_vec;
  for (const auto & t : initial_core) {
    auto score = TermScore::GetScore(t);
    score_vec.push_back(std::make_pair(score, t));
  }
  std::sort(score_vec.begin(),score_vec.end());
  for (auto pos = score_vec.rbegin(); pos != score_vec.rend(); ++ pos) {
    pred_sets.push_back(pos->second);
    pred_scores.push_back(pos->first);
  }
} // insert_preds_score_descending


void Enumerator::GetOneCandidate(smt::TermVec & cands, bool iterative_reduction, bool mus_traverse_reduction) {

  //let's first get sat/unsat and initial unsat core
  smt::Term F_and_T = AND(prev_, trans_);
  smt::Term base_term = OR( F_and_T ,to_next_(init_) );
  smt::UnorderedTermSet initial_core; // base term is already removed from it
  
  if (!GetInitialUnsatCore(base_term, F_and_T, initial_core))
    return;
  assert (!initial_core.empty());

  if (iterative_reduction) {
    unsigned prev_unsat_core_size = initial_core.size();
    D(0, "[IterativeReduction] Initial core size {}",prev_unsat_core_size);
    do {
      smt::UnorderedTermSet core_out;
      MinimizeUnsatCore(base_term, initial_core, core_out);
      initial_core.swap(core_out); // let's avoid copying: initial_core = core_out
      if (initial_core.size() == prev_unsat_core_size)
        break;
      prev_unsat_core_size = initial_core.size();
    } while(true);
    D(0, "[IterativeReduction] End core size {}",prev_unsat_core_size);
  }

  if (!mus_traverse_reduction) {
    cands.push_back(AssembleCandFromUnsatCore(base_term, initial_core));
    return;
  }


  std::list<smt::Term> pred_sets;
  std::list<unsigned> pred_scores;

  insert_preds_score_descending(initial_core, pred_sets, pred_scores);
  assert(pred_scores.size() == pred_sets.size());
  DebugRegAllpred(pred_sets, pred_scores);

  auto pred_pos = pred_sets.begin(); auto score_pos = pred_scores.begin();
  while ( pred_pos != pred_sets.end() ) {
    // warning, the size of pred_sets will shrink
    DebugRegSelRemove(*pred_pos, "Try Remove");
    smt::UnorderedTermSet unsatcore;
    pred_pos = GetUnsatCoreWithout(base_term, pred_sets, pred_pos, /*output*/ unsatcore ) ;
    if ( ! unsatcore.empty() ) { // still unsat
      CheckAndRemove( 
        /*output*/ pred_sets, /*inout*/ pred_pos, 
         /*output*/ pred_scores,  /*inout*/ score_pos,  /* input */  unsatcore);
      // they themselves should have been removed, and the later part will also be removed
      assert(pred_scores.size() == pred_sets.size());
    } else {// else do nothing
     ++ pred_pos; ++ score_pos;
    }
    DebugRegResult(pred_sets);
    // because we cannot remove this one
  } // from beginning to end
  // now we should collect and form the pred

  cands.push_back(AssembleCandFromUnsatCore(base_term, pred_sets));
} // GetOneCandidateViaMUS


// base term should already been removed
smt::Term Enumerator::AssembleCandFromUnsatCore(const smt::Term & base_term, 
  const std::list<smt::Term> & unsatcore) {
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


// base term should already been removed
smt::Term Enumerator::AssembleCandFromUnsatCore(const smt::Term & base_term, 
  const smt::UnorderedTermSet & unsatcore) {
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


void Enumerator::DebugPredicates(const smt::TermVec & inpreds, const smt::Term & base, const smt::Term & init, bool rm_pre) {

#if 0
  bool base_term_in = false;
  for (const auto & p : inpreds) {
    if (p == base) {
      base_term_in = true;
    } else {
      auto t_curr = per_cex_info_.pred_next_to_pred_curr.at(p);
      D(0, "{} on s': {} ", t_curr->to_raw_string(), solver_->get_value(p)->to_string());
    }
  }
#endif

  // finally print base and init
  D(0, "INIT' : {} ", solver_->get_value(to_next_(init))->to_string());
  const char * info = rm_pre ? "( not (/\\p) /\\ F /\\ T ) \\/ (INIT') : {} " : "( F /\\ T ) \\/ (INIT') : {} " ;
  D(0, info, solver_->get_value(base)->to_string());

} // DebugPredicates


// true means still unsat
bool Enumerator::GetInitialUnsatCore(const smt::Term & base_term, const smt::Term & F_and_T, 
  smt::UnorderedTermSet & initial_core) 
{
  solver_->push();
  solver_->assert_formula(base_term);
  auto res = solver_->check_sat_assuming_vector(per_cex_info_.predicates_nxt);
  if (res.is_sat()) {
    DebugPredicates(per_cex_info_.predicates_nxt, base_term, init_, false);

    std::unordered_set<smt::Term> varset;
    cex_->get_varset(varset);
    bool fail_at_init = check_failed_at_init(F_and_T);
    extract_model_(varset, fail_at_init); // must before pop

    solver_->pop();
    return false;
  }
  solver_->get_unsat_core(initial_core);
  solver_->pop();
  return true;
} // GetInitialUnsatCore

void Enumerator::MinimizeUnsatCore(const smt::Term & base_term,
  const smt::UnorderedTermSet & core_in, smt::UnorderedTermSet & core_out)
{
  solver_->push();
  solver_->assert_formula(base_term);
  auto res = solver_->check_sat_assuming(core_in);
  assert(res.is_unsat());
  solver_->get_unsat_core(core_out);
  solver_->pop();
} // MinimizeUnsatCore

std::list<smt::Term>::iterator Enumerator::GetUnsatCoreWithout(const smt::Term & base_term, 
  std::list<smt::Term> & pred_sets, std::list<smt::Term>::iterator pred_pos, 
  /*output*/ smt::UnorderedTermSet & unsatcore )
{
    solver_->push();
    solver_->assert_formula(base_term);
    
    smt::Term term_to_remove = *pred_pos;
    auto pos_after = pred_sets.erase(pred_pos);
    auto res = solver_->check_sat_assuming_list(pred_sets);
    auto new_pos = pred_sets.insert(pos_after, term_to_remove);
    assert(!res.is_unknown());
    
    if (res.is_unsat())
      solver_->get_unsat_core(unsatcore);

    solver_->pop();
    return new_pos;
} // GetUnsatCoreWithout


void Enumerator::CheckAndRemove(
  std::list<smt::Term> & pred_sets, std::list<smt::Term>::iterator & pred_pos,
  std::list<unsigned> & pred_scores, std::list<unsigned>::iterator & score_pos, 
  const smt::UnorderedTermSet & unsatcore)
{
  auto pred_iter = pred_sets.begin(); // pred_pos;
  auto score_iter = pred_scores.begin(); // score_pos
  auto pred_pos_new = pred_sets.begin();
  auto score_pos_new = pred_scores.begin();

  bool reached = false;
  bool next_pos_found = false;
  while( pred_iter != pred_sets.end() ) {
    assert(score_iter != pred_scores.end());

    if (pred_iter == pred_pos) {
      assert (!reached);
      assert (score_iter == score_pos);
      reached = true;
    }
    
    if (unsatcore.find(*pred_iter) == unsatcore.end()) {
      assert (reached);
      pred_iter = pred_sets.erase(pred_iter);
      score_iter = pred_scores.erase(score_iter);
    } else {
      if (reached && ! next_pos_found) {
        pred_pos_new = pred_iter;
        score_pos_new = score_iter;
        next_pos_found = true;
      }
      ++ pred_iter; ++ score_iter;
    }
  }
  assert(reached);
  if (! next_pos_found) {
    assert (pred_iter == pred_sets.end() && score_iter == pred_scores.end());
    pred_pos_new = pred_iter;
    score_pos_new = score_iter;
  }
  pred_pos = pred_pos_new;
  score_pos = score_pos_new;
} // CheckAndRemove


//---------------------- DEBUG PURPOSE----------------------------------------------

#ifdef DEBUG

void Enumerator::DebugRegAllpred(const std::list<smt::Term> & inpreds, const std::list<unsigned> & scores) {
  unsigned idx = 0;
  pred_to_numbers.clear();
  auto pos = scores.begin();
  for (const auto & t : inpreds) {
    pred_to_numbers.emplace(t,idx++);
    D(0, "{}: Score: {} expr: {}", idx-1, *pos, t->to_raw_string());
    ++pos;
  }
  D(0,"Total pred: #{}", idx);
}

void Enumerator::DebugRegSelRemove(const smt::Term & sel, const std::string & action) {
  auto pos = pred_to_numbers.find(sel);
  assert(pos != pred_to_numbers.end());
  std::cout << "  -> " << action << " no. " << pos->second << std::endl;
}

void Enumerator::DebugRegResult(const std::list<smt::Term> & inpreds) {
  std::cout << "     result : {" ;
  for (const auto & p : inpreds) {
    auto pos = pred_to_numbers.find(p);
    assert(pos != pred_to_numbers.end());
    std::cout << pos->second << ", ";
  }
  std::cout << "}" << std::endl;
}

#else

void Enumerator::DebugRegAllpred(const smt::UnorderedTermSet & inpreds) {
}

void Enumerator::DebugRegSelRemove(const smt::Term & sel, const std::string & action) {
}

void Enumerator::DebugRegResult(const smt::UnorderedTermSet & res) {
}

#endif



} // namespace unsat_enum

} // namespace cosa
