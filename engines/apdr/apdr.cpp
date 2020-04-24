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
 ** \brief APDR core agorithm
 **
 ** 
 **/


#include "apdr.h"
#include "config.h"

#include "../sygus/container_shortcut.h"

#include "utils/logger.h"

#include <cassert>
#include <queue>

// some helper functions
#define TERM_TRUE    (solver_->make_term(true))
#define NOT(x)       (solver_->make_term(smt::Not, (x)))
#define EQ(x, y)     (solver_->make_term(smt::BVComp, (x), (y)))
#define AND(x, y)    (solver_->make_term(smt::And, (x), (y)))
#define OR(x, y)     (solver_->make_term(smt::Or, (x), (y)))
#define IMPLY(x, y)  (solver_->make_term(smt::Implies, (x), (y)))

// some helper functions
#define TERM_TRUE_msat    (itp_solver_->make_term(true))
#define NOT_msat(x)       (itp_solver_->make_term(smt::Not, (x)))
#define EQ_msat(x, y)     (itp_solver_->make_term(smt::BVComp, (x), (y)))
#define AND_msat(x, y)    (itp_solver_->make_term(smt::And, (x), (y)))
#define OR_msat(x, y)     (itp_solver_->make_term(smt::Or, (x), (y)))
#define IMPLY_msat(x, y)  (itp_solver_->make_term(smt::Implies, (x), (y)))

namespace cosa {

// ---------------------------------------------------------------------

#define DEBUG 1
#ifdef DEBUG
  #define D(...) logger.log( __VA_ARGS__ )
#else
  #define D(x) do {} while (0)
#endif

// -----------------------------------------------------------------------

APDR::APDR(const Property & p, smt::SmtSolver & s, smt::SmtSolver & itp_solver,
    const std::unordered_set<smt::Term> & keep_vars,
    const std::unordered_set<smt::Term> & remove_vars) :
  Prover(p,s), keep_vars_(keep_vars), remove_vars_(remove_vars),
  partial_model_getter(s), itp_solver_(itp_solver),
  to_itp_solver_(itp_solver_), to_btor_(solver_)
  // cache the transition and init condition formula -- trans/init
  // no need actually.
  // - itp_solver_trans_term_(to_itp_solver_.transfer_term(ts_.trans())),
  // - itp_solver_init_term_(to_itp_solver_.transfer_term(ts_.init()))
  { 
    for (auto && v : keep_vars_)
      keep_vars_nxt_.insert(ts_.next(v));
    for (auto && v : remove_vars_)
      remove_vars_nxt_.insert(ts_.next(v));
  }

void APDR::initialize() {
  // cache partial model getter
  partial_model_getter.CacheNode(ts_.init());
  // create the cache of next vars in 
  for (const auto & nxt : ts_.state_updates()) {
    partial_model_getter.CacheNode(nxt.second);
  }

  // cache msat expression
  init_msat_nxt = to_itp_solver_.transfer_term(ts_.next(ts_.init()));
  T_msat = to_itp_solver_.transfer_term(ts_.trans());

  // build frames
  frames.push_back(frame_t()); // F0 = [init]
  frames.back().push_back(
    new_lemma(
      ts_.init(), to_itp_solver_.transfer_term(ts_.init()),
      NULL, Lemma::ORIGIN_FROM_INIT) );
  frames.push_back(frame_t()); // F1 = []
}

APDR::~APDR() { }


void APDR::cut_vars_cur(std::unordered_set<smt::Term> & v) {
  auto pos = v.begin();
  while(pos != v.end()) {
    if ( !ts_.is_curr_var(*pos) ||
         (!keep_vars_.empty() && !IN(*pos, keep_vars_)) ||
        (IN(*pos, remove_vars_)))
      pos = v.erase(pos);
    else
      pos = ++pos;
  }
}

void APDR::put_vars_nxt(const std::unordered_set<smt::Term> & vs, std::unordered_set<smt::Term> & out) {
  for (auto && v: vs ) {
    if ( !ts_.is_next_var(v) ||
         (!keep_vars_nxt_.empty() && !IN(v, keep_vars_nxt_)) ||
        (IN(v, remove_vars_nxt_)))
        continue;
    out.insert(v);
  }
}


bool APDR::is_valid(const smt::Term & e) {
  solver_->push();
  solver_->assert_formula(NOT(e));
  auto result = solver_->check_sat();
  solver_->pop();
  return !(result.is_sat());
}

bool APDR::is_sat(const smt::Term & e)  {
  solver_->push();
  solver_->assert_formula(NOT(e));
  auto result = solver_->check_sat();
  solver_->pop();
  return !(result.is_sat());
}

Model * APDR::get_not_valid_model(const smt::Term & e) {
  solver_->push();
  solver_->assert_formula(NOT(e));
  auto result = solver_->check_sat();
  if (!result.is_sat()) {
    solver_->pop();
    return NULL;
  }
  Model * m = new_model();
  partial_model_getter.GetPartialModel(e, m->cube, true);
  solver_->pop();
  return m;
}

// this function is only used in recursive block
// in checking the same cycle solve
Model * APDR::solve(const smt::Term & formula) {
  assert(ts_.only_curr(formula)); // TO REMOVE DEBUG
  solver_->push();
  solver_->assert_formula(formula);
  auto result = solver_->check_sat();
  if (result.is_sat()) {
    varset_t varset;
    partial_model_getter.GetVarList(formula, varset, true);
    cut_vars_cur(varset);
    Model * m = new_model(varset);
    solver_->pop();
    return m;
  } // else
  solver_->pop();
  return NULL;
}

// ----------- frame handling -------------

smt::Term APDR::frame_prop_btor(unsigned fidx) const {
  assert(fidx < frames.size());
  auto & lemmas = frames.at(fidx);
  if(lemmas.size() == 0)
    return TERM_TRUE;
  if(lemmas.size() == 1)
    return lemmas.at(0)->expr();
  smt::Term e = lemmas.at(0)->expr();
  for (auto lp_pos = lemmas.begin() + 1; lp_pos != lemmas.end() ; ++ lp_pos)
    e = AND(e, (*lp_pos)->expr() );
  return e;
}


smt::Term APDR::frame_prop_msat(unsigned fidx) const {
  assert(fidx < frames.size());
  auto & lemmas = frames.at(fidx);
  if(lemmas.size() == 0)
    return TERM_TRUE_msat;
  if(lemmas.size() == 1)
    return lemmas.at(0)->expr_msat();
  smt::Term e = lemmas.at(0)->expr_msat();
  for (auto lp_pos = lemmas.begin() + 1; lp_pos != lemmas.end() ; ++ lp_pos)
    e = AND_msat(e, (*lp_pos)->expr_msat() );
  return e;
}


bool APDR::frame_and_fc_implies(unsigned fidx, FrameCache &fc, const smt::Term &prop) {
  return is_valid(IMPLY(AND(frame_prop_btor(fidx), fc.conjoin_frame_for_props_btor(fidx)), prop));
}

bool APDR::frame_implies(unsigned fidx, const smt::Term &prop) {
  return is_valid(IMPLY(frame_prop_btor(fidx), prop));
}

Model * APDR::frame_not_implies_model(unsigned fidx, const smt::Term &prop) {
  return get_not_valid_model(IMPLY(frame_prop_btor(fidx), prop));
}

bool APDR::frame_compatible_w(unsigned fidx, const smt::Term &prop) {
  return is_sat(AND(frame_prop_btor(fidx), prop));
}

smt::Term APDR::get_inv() const {
  return frame_prop_btor(frames.size() - 1);
}

// ----------- frame checks -------------
bool APDR::is_last_two_frames_inductive() {
  auto fn = frames.size();
  if (fn > 1) {
    if (is_valid(IMPLY(frame_prop_btor(fn-1), frame_prop_btor(fn-2))))
      return true;
  }
  return false;
}

// inv = get_inv()
bool APDR::is_safe_inductive_inv(const smt::Term & inv) {
  assert (ts_.no_next(inv));
  auto inv_prime = ts_.next(inv);

  if(! is_valid( IMPLY(ts_.init(), inv) ))
    return false;
  if(! is_valid( IMPLY(AND(inv, ts_.trans()), inv_prime) ))
    return false;
  if(! is_valid( IMPLY(inv, property_.prop())))
    return false;
  return true;
}

// Fi /\ T => F'i+1
void APDR::sanity_check_imply() {
  assert (frames.size() > 1);
  smt::Term T = ts_.trans();
  for (size_t fidx = 1; fidx < frames.size(); ++ fidx) {
    auto next_frame = ts_.next( frame_prop_btor(fidx) );
    assert ( is_valid(
      IMPLY(AND(frame_prop_btor(fidx-1), T), next_frame)
    ) );
  }
}

// Fi => Fi+1
void APDR::sanity_check_frame_monotone() {
  assert (frames.size() > 1);
  for (size_t fidx = 1; fidx < frames.size(); ++ fidx) {
    assert ( is_valid(
      IMPLY(frame_prop_btor(fidx-1), frame_prop_btor(fidx))
    ));
  }
}

void APDR::dump_frames(std::ostream & os) const {
  os << "---------- Frames DUMP ----------" << std::endl;
  for (size_t fidx = 0; fidx < frames.size() ; ++ fidx) {
    os << "Frame : " << fidx << std::endl;
    const auto & frame = frames.at(fidx);
    auto push_pos = get_with_default(frames_pushed_idxs_map, fidx, 0);
    size_t lidx;
    // dump lemmas
    for ( lidx = 0; lidx < frame.size() ; ++ lidx) {
      char ptr = (push_pos == lidx) ? '*' : ' ';
      os << "  " << ptr << " l" << lidx <<  " : " << frame.at(lidx)->expr->to_string() << std::endl;
    }
    if (lidx == push_pos)
      os << "    all tried to push" << std::endl;
    // dump cexs
    os << "  CEX blocked :" << std::endl;
    for ( lidx = 0; lidx < frame.size() ; ++ lidx) {
      char ptr = (push_pos == lidx) ? '*' : ' ';
      os << "  " << ptr << " l" << lidx <<  " : " << * (frame.at(lidx)->cex()) << std::endl;
    }
    if (lidx == push_pos)
      os << "    all tried to push" << std::endl;
    
    if (IN(fidx, unblockable_fact)) {
      const auto & facts = unblockable_fact.at(fidx);
      os << "  facts # : " << facts.size() << std::endl;
      for (size_t cidx = 0; cidx < facts.size() ; ++ cidx) {
        os << "    f" << cidx << ": " << *(facts.at(cidx)) << std::endl;
      }
    } // if there are unblocked facts
  } // for each frame
  os << "---------- END Frames DUMP ----------" << std::endl;
} // dump_frames

void APDR::_add_lemma(Lemma * lemma, unsigned fidx) {
  if (fidx == frames.size())
    frames.push_back(frame_t());
  assert (fidx < frames.size());
  frames.at(fidx).push_back(lemma);
}

void APDR::_add_pushed_lemma(Lemma * lemma, unsigned start, unsigned end) {
  Lemma * l_prev = lemma->copy(*this);
  l_prev->pushed = true;
  for (size_t fidx = start; fidx <= end; ++ fidx)
    _add_lemma(l_prev, fidx);
}

void APDR::_add_fact(Model * fact, unsigned fidx) {
  if (!IN(fidx, unblockable_fact))
    unblockable_fact.insert(std::make_pair(fidx, facts_t()));
  assert (!FIND_IN(fact, unblockable_fact.at(fidx)));
  unblockable_fact.at(fidx).push_back(fact);
}

// ----------- TRANS - related  -------------------
//  you may want to have the interpolant here
//  used in recursive_block  and  get_bad_state_from_property_invalid_after_trans
//  use frame_prop_list for prevF !!!
//  --------------------------------------------------------------
//  NOTE:
//        to be used as get_pre_post_state_from_property_invalid_after_trans:
//        init = None, findItp = False, get_post_state = True

// 1. T is by default the transition relation
// -- please note this could be different for btor/msat
// 2. Variables will be by default trans.variables (for btor)
// 3. init will be by default the init (will need to trans to msat)
// 

APDR::solve_trans_result APDR::solveTrans(
  unsigned prevFidx, const smt::Term & prop_btor, bool remove_prop_in_prev_frame,
  bool use_init, bool findItp, bool get_post_state, FrameCache * fc ) {

  auto prevF_btor = frame_prop_btor(prevFidx);
  if (remove_prop_in_prev_frame)
    prevF_btor = AND(prevF_btor, prop_btor);
  if (fc && fc->has_lemma_at_frame(prevFidx)) {
    prevF_btor = AND(prevF_btor, fc->conjoin_frame_for_props_btor(prevFidx));
  }

  auto prop_no_nxt_btor = ts_.next_to_expr( ts_.next( prop_btor ) ); // to get rid of next vars
  auto F_to_check = AND(prevF_btor, NOT(prop_no_nxt_btor));
  if (use_init) {
    F_to_check = OR(F_to_check,
      // INIT(V) /\ not(P(V))
      AND( ts_.init() , NOT(prop_btor) )
      );
  }

  D(3,"      [solveTrans] Property: {} , v=>v', useinit: {}", prop_btor->to_string(), use_init  );
  D(3,"      [solveTrans] formula : {}", F_to_check->to_string());

  solver_->push();
  solver_->assert_formula(F_to_check);
  auto result = solver_->check_sat();
  if (result.is_sat()) {
    // now let's get the partial model
    std::unordered_set<smt::Term> varlist;
    std::unordered_set<smt::Term> post_varlist;
    partial_model_getter.GetVarList(F_to_check, varlist, true);
    cut_vars_cur(varlist);
    if (get_post_state)
      put_vars_nxt( varlist , post_varlist);
    Model * pre_ex = new_model(varlist);
    Model * post_ex = get_post_state ? new_model(post_varlist) : NULL;
    solver_->pop();
    return solve_trans_result(pre_ex, post_ex, smt::Term(NULL));
  } // else unsat
  solver_->pop();
  if (!findItp)
    return solve_trans_result(NULL, NULL, smt::Term(NULL));
  // else unsat and findItp

  auto prevF_msat = frame_prop_msat(prevFidx);
  auto prop_msat = to_itp_solver_.transfer_term(prop_btor);
  auto prop_msat_nxt = to_itp_solver_.transfer_term(ts_.next(prop_btor));

  // auto init_msat_nxt = to_itp_solver_.transfer_term(ts_.next(ts_.init()));
  // auto T_msat = to_itp_solver_.transfer_term(ts_.trans());

  if (remove_prop_in_prev_frame)
    prevF_msat = AND_msat(prevF_msat, prop_msat);
  if (fc && fc->has_lemma_at_frame(prevFidx)) {
    prevF_msat = AND_msat(prevF_msat, fc->conjoin_frame_for_props_msat(prevFidx));
  }
  
  smt::Term A_msat;
  smt::Term B_msat;
  if (use_init) {
    A_msat = OR_msat( AND_msat(prevF_msat, T_msat), init_msat_nxt  );
    B_msat = NOT_msat(prop_msat_nxt);
  } else {
     A_msat = AND_msat(prevF_msat, T_msat);
     B_msat = NOT_msat(prop_msat_nxt);
  }

  D(3,"      [solveTrans] Itp A: {}", A_msat->to_string());
  D(3,"      [solveTrans] Itp B: {}", B_msat->to_string());


  smt::Term itp_msat;
  itp_solver_->get_interpolant(A_msat,B_msat,itp_msat);
  // translate back to btor and map back msat
  smt::Term itp_btor = to_btor_.transfer_term(itp_msat);
  assert(ts_.only_next(itp_btor));

  D(3,"      [solveTrans] get itp: {}", ts_.curr(itp_btor)->to_string());

  // transfer it back to current vars
  return solve_trans_result(NULL, NULL,ts_.curr(itp_btor));
} // solveTrans


// used in check_property, check_init_failed
// not in push_lemma, because we also want the pre-&post-states
Model * APDR::get_bad_state_from_property_invalid_after_trans (
  const smt::Term & prop_btor, unsigned idx, bool use_init
) {
  assert(idx >= 0);
  D(2, "    [F{} -> prop]", idx);
  auto trans_result = solveTrans(
    idx, prop_btor,
    /*remove_prop_in_prev*/ false, use_init,
    /*find itp*/ false, /*post state*/ false, /*fc*/ NULL );
  return trans_result.pre_ex;
}

bool APDR::do_recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin) {
  std::priority_queue<fcex_t, std::vector<fcex_t>, fcex_queue_comparator> priorityQueue;

  smt::Term prop_btor = cube->to_expr(solver_);

  D(2, "      [block] Try @F{} : {}", idx, cube->to_string());

  if (frame_implies(idx, prop_btor)) {
    D(3, "      [block] already blocked by F{}", idx);
    return true; // already blocked
  }
  
  priorityQueue.push(std::make_pair(idx, cube));
  while(!priorityQueue.empty()) {
    auto head = priorityQueue.top();
    unsigned fidx = head.first;
    Model * cex = head.second;
    if (fidx == 0) { // 
      auto init_model = solve(AND(ts_.init(), cex->to_expr(solver_)));
      assert (init_model != NULL);

      D(3, "      [block] CEX found!");
      // cex found
      return false;
    }

    auto prop_btor_cex = cex->to_expr(solver_);
    // check at F Fidx-1 -> F idx 
    auto trans_result = solveTrans(fidx-1, prop_btor_cex, pdr_config::RM_CEX_IN_PREV,
      true /*use_init*/, true /*itp*/, false /*post state*/, NULL /*no fc*/ );

    D(3, "      [block] check at F{} -> F{} : {}", fidx-1, fidx, prop_btor_cex->to_string());

    if (trans_result.pre_ex == NULL) {
      // unsat -- no reachable
      Lemma * lemma = new_lemma(trans_result.itp, to_itp_solver_.transfer_term(trans_result.itp),
        cex, cex_origin);
      _add_lemma(lemma, fidx);
      _add_pushed_lemma(lemma, 1, fidx -1 );
      priorityQueue.pop();
    } else {
      priorityQueue.push(std::make_pair(fidx-1, trans_result.pre_ex));
      D(3, "      [block] push to queue, F{} : {}", fidx-1,  trans_result.pre_ex->to_string());
    }
  } //  while there is cube to block
  // block succeeded
  D(2, "      [block] succeed, return.");
  return true;
}

// use frame cache & add new lemmas to the frame_cache
bool APDR::try_recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin,
  FrameCache & frame_cache) {

  D(2, "      [block-try] Try @F{} : {}", idx, cube->to_string());

  std::priority_queue<fcex_t, std::vector<fcex_t>, fcex_queue_comparator> priorityQueue;

  smt::Term prop_btor = cube->to_expr(solver_);
  if (frame_and_fc_implies(idx, frame_cache, prop_btor)) {
    D(3, "      [block-try] already blocked by F{}", idx);
    return true; // already blocked
  }
  
  priorityQueue.push(std::make_pair(idx, cube));
  while(!priorityQueue.empty()) {
    auto head = priorityQueue.top();
    unsigned fidx = head.first;
    Model * cex = head.second;
    if (fidx == 0) { // 
      auto init_model = solve(AND(ts_.init(), cex->to_expr(solver_)));
      assert (init_model != NULL);
      D(3, "      [block-try] CEX found!");
      // cex found
      return false;
    }

    auto prop_btor_cex = cex->to_expr(solver_);
    // check at F Fidx-1 -> F idx 
    auto trans_result = solveTrans(fidx-1, prop_btor_cex, pdr_config::RM_CEX_IN_PREV,
      true /*use_init*/, true /*itp*/, false /*post state*/, & frame_cache );

    D(3, "      [block-try] check at F{} -> F{} : {}", fidx-1, fidx, prop_btor_cex->to_string());

    if (trans_result.pre_ex == NULL) {
      // unsat -- no reachable
      Lemma * lemma = new_lemma(trans_result.itp, to_itp_solver_.transfer_term(trans_result.itp),
        cex, cex_origin);
      frame_cache._add_lemma(lemma, fidx);
      frame_cache._add_pushed_lemma(lemma, 1, fidx -1 );
      priorityQueue.pop();
    } else {
      priorityQueue.push(std::make_pair(fidx-1, trans_result.pre_ex));
      D(3, "      [block-try] push to queue, F{} : {}", fidx-1,  trans_result.pre_ex->to_string());
    }
  } //  while there is cube to block
  // block succeeded
  D(2, "      [block-try] succeed, return.");
  return true;
} // APDR::try_recursive_block


// ----------- PROCEDURES -------------------
bool APDR::check_init_failed() { // will use the prop specified by property
  Model * failed_m = frame_not_implies_model(0, property_.prop());
  if (failed_m) {
    D(1, "Property failed at init.");
    return true; // failed
  }
  failed_m = 
    get_bad_state_from_property_invalid_after_trans(property_.prop(), 0 /*idx*/, true /*use_init*/ );
  if (failed_m) {
    D(1, "Property failed at init--T-->P'.");
    return true;
  }
  return false;
}

ProverResult APDR::check_until(int k) {
  assert (k>=0);

  if (check_init_failed())
    return ProverResult(FALSE);

  for (unsigned step = 0; step < k; ++step) {
    // removable checks
    #ifdef DEBUG
      sanity_check_frame_monotone();
      sanity_check_imply();
    #endif
    D(1, "Total Frames: {}, L {} ", frames.size(), frames.back().size());
    Model * cube = get_bad_state_from_property_invalid_after_trans(
      property_.prop(), frames.size() -1  /*idx*/ , false /*use_init*/ );
    D(1, "[Checking property] Get cube: {} @F{}", cube ? cube->to_string() : "None", frames.size() -1);
    if (cube) {
      if (! do_recursive_block(cube, frames.size() -1 , Lemma::LemmaOrigin::ORIGIN_FROM_PROPERTY)) {
        D(1, "[Checking property] Bug found at step {}", frames.size());
        return ProverResult(FALSE);
      } else {
        D(1, "[Checking property] Cube blocked : {}", cube->to_string());
      }
    } else {
      if (is_last_two_frames_inductive()) {
        D(1, "[Checking property] The system is safe, frame : {}", frames.size());
        return ProverResult(TRUE);
      } else {
        D(1, "[Checking property] Adding frame {} ...", frames.size());
        frames.push_back(frame_t());
        push_lemma_from_the_lowest_frame();
        if (is_last_two_frames_inductive()) { // if we are lucky to have pushed all
          D(1, "[Checking property] The system is safe, frame : {}", frames.size());
          return ProverResult(TRUE);
        }
      } // adding a frame
    } // no bad state found at this point
  } // step k
  return ProverResult(UNKNOWN);
}

void APDR::push_lemma_from_the_lowest_frame() {

}


} // namespace cosa
