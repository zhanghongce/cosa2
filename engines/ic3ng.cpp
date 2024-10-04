/*********************                                                  */
/*! \file ic3bits.cpp
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bit-level IC3 implementation that splits bitvector variables
**        into the individual bits for bit-level cubes/clauses
**        However, the transition system itself still uses bitvectors
**/

#include "utils/logger.h"
#include "engines/ic3ng.h"
#include "engines/ic3ng-support/debug.h"
#include "utils/container_shortcut.h"
#include "utils/sygus_ic3formula_helper.h"

#include "smt-switch/printing_solver.h"

namespace pono
{
    
IC3ng::IC3ng(const Property & p, const TransitionSystem & ts,
            const smt::SmtSolver & s,
            PonoOptions opt) :
  Prover(p, ts, s, opt), 
  debug_fout("debug.smt2"),
  partial_model_getter(s)
  // bitwuzla can accept non-literal to reduce anyway
  {     
    initialize();
  }

IC3ng::~IC3ng() { }

void IC3ng::check_ts() {
  // check if there are arrays or uninterpreted sorts and fail if so
  if (!ts_.is_functional())
    throw PonoException(
      "IC3ng only supports functional transition systems.");
    // check if there are arrays or uninterpreted sorts and fail if so
  for (const auto & vec : { ts_.statevars(), ts_.inputvars() }) {
    for (const auto & st : vec) {
      smt::SortKind sk = st->get_sort()->get_sort_kind();
      if (sk == smt::ARRAY) {
        throw PonoException("IC3ng does not support arrays yet");
      } else if (sk == smt::UNINTERPRETED) {
        throw PonoException(
            "IC3ng does not support uninterpreted sorts yet.");
      }
    }
  }
  // requires all input variables become state variables
  if (!ts_.inputvars().empty()) {
    throw PonoException("IC3ng requries promoting input variables to state variables.");
  }
  // maybe you don't need to use ts.constraints. Because they are already conjuncted to init
  // and trans
  if (!can_sat(ts_.init())) {
    throw PonoException("constraint is too tight that conflicts with init.");
  }
  if (!can_sat(smart_and(smt::TermVec({ts_.init(), ts_.trans()})))) {
    throw PonoException("constraint is too tight that conflicts with init and trans");
  }

}

void IC3ng::initialize() {
  if (initialized_) {
    return;
  }

  if(!options_.promote_inputvars_) {
    throw PonoException("IC3ng must be used together with --promote-inputvars");
  }

  // solver_ = smt::create_printing_solver(solver_, &debug_fout, smt::PrintingStyleEnum::DEFAULT_STYLE);

  boolsort_ = solver_->make_sort(smt::BOOL);
  solver_true_ = solver_->make_term(true);
  Prover::initialize();
  check_ts();

  // 1. build related information
  // all input will be promoted to statevar anyway
  actual_statevars_ = ts_.statevars();
  const auto & all_state_vars = ts_.statevars();
  const auto & s_updates = ts_.state_updates();
  for (const auto & sv : all_state_vars) {
    if (!IN(sv, s_updates)) {
      no_next_vars_.insert(sv);
      no_next_vars_nxt_.insert(ts_.next(sv));
      actual_statevars_.erase(sv);
    }
    else
      nxt_state_updates_.emplace(ts_.next(sv), s_updates.at(sv));
  }

  has_assumptions = false;
  assert(!nxt_state_updates_.empty());

  smt::TermVec constraints_curr_var_;  
  for (const auto & c_initnext : ts_.constraints()) {
    // if (!c_initnext.second)
    //  continue; // should not matter
    has_assumptions = true;
    assert(ts_.no_next(c_initnext.first));
    // if (no_next) {
    constraints_curr_var_.push_back(c_initnext.first);
    // translate input_var to next input_var
    // but the state var ...
    // we will get to next anyway
    constraints_curr_var_.push_back(
      next_trans_replace(ts_.next(c_initnext.first)));
    // } // else skip
  }
  all_constraints_ = has_assumptions ? smart_and(constraints_curr_var_) : solver_true_;
  bad_next_trans_subst_ = next_trans_replace(ts_.next(bad_)); // bad_ is only available after Prover's initialize()
  init_prime_ = ts_.next(ts_.init());

  // 2. set up the label system

  frames.clear();
  frame_labels_.clear();
  // first frame is always the initial states
  
  append_frame();
  add_lemma_to_frame(new_lemma(ts_.init(), NULL, LCexOrigin::FromInit()), 0);
  append_frame();
  add_lemma_to_frame(new_lemma(all_constraints_, NULL,  LCexOrigin::FromConstraint()), 1);
  add_lemma_to_frame(new_lemma(smart_not(bad_), NULL, LCexOrigin::FromProperty()), 1);

  // set semantics of TS labels
  assert(!init_label_);
  // frame 0 label is identical to init label
  init_label_ = frame_labels_[0];
}

void IC3ng::append_frame()
{
  assert(frame_labels_.size() == frames.size());

  frame_labels_.push_back(
      solver_->make_symbol("__frame_label_" + std::to_string(frames.size()),
                           solver_->make_sort(smt::BOOL)));
  frames.push_back({});
}

void IC3ng::add_lemma_to_frame(Lemma * lemma, unsigned fidx) {
  assert (fidx < frames.size());
  frames.at(fidx).push_back(lemma);

  solver_->assert_formula(
      solver_->make_term(smt::Implies, frame_labels_.at(fidx), lemma->expr()));

}


ic3_rel_ind_check_result IC3ng::rel_ind_check( unsigned prevFidx, 
  const smt::Term & bad_next_trans_subst_,
  Model * cex_to_block,
  bool get_pre_state
  ) {
  
  auto bad_next_to_assert = cex_to_block ? 
    // NOTE: this is next state, you should not use NOT here
    next_trans_replace( ts_.next( cex_to_block->to_expr(solver_) ) ) :
    bad_next_trans_subst_   ; // p(T(s))

  solver_->push();
  assert_frame(prevFidx);
  if (cex_to_block) // you need to use NOT here
    solver_->assert_formula( smart_not(cex_to_block->to_expr(solver_)) );
  solver_->assert_formula(bad_next_to_assert);
  auto result = solver_->check_sat();
  if (result.is_unsat()) {
    solver_->pop();
    return ic3_rel_ind_check_result(false, NULL);
  } // now is sat
  if (!get_pre_state) {
    solver_->pop();
    return ic3_rel_ind_check_result(true, NULL);
  } // now get the state

  // predecessor generalization is implemented through partial model
  std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> varlist_slice;
  std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> input_asts_slices = {
    {bad_next_to_assert, { {0,0} }}
  };
  if (has_assumptions)
    input_asts_slices.emplace(all_constraints_, std::vector<std::pair<int,int>>({ {0,0} }));
    
  partial_model_getter.GetVarListForAsts_in_bitlevel(input_asts_slices, varlist_slice);
  // after this step varlist_slice may contain 
  // 1. current state var , 2. current input var
  // 3. next input var (it should not contain next state var)
  // if there is no assumption, we can remove 2&3
  // if there is assumption, we can only remove 3
  
  cut_vars_curr(varlist_slice, !has_assumptions); // // if we don't have assumptions we can cut current input
  Model * prev_ex = new_model(varlist_slice);
  solver_->pop();

  // must after pop
  //if(has_assumptions)
  //  CHECK_MODEL(solver_, prop_no_nxt_btor, 0, prev_ex);

  return ic3_rel_ind_check_result(true, prev_ex); 
} // end of solveTrans




// if blocked return true
// else false

// < Model * cube, unsigned idx, LCexOrigin cex_origin >
// should have already been put into the queue
bool IC3ng::recursive_block_all_in_queue() {
  // queue not empty
  if(proof_goals.empty())
    return true;

  unsigned prior_round_frame_no =  proof_goals.top()->fidx;

  while(!proof_goals.empty()) {
    fcex_t * fcex = proof_goals.top();

    D(2, "[recursive_block] Try to block {} @ F{}", fcex->cex->to_string(), fcex->fidx);
    // if we arrive at a new frame, eager push from prior frame
    if (fcex->fidx > prior_round_frame_no) {
      D(2,"Eager push from {} --> {}", prior_round_frame_no, fcex->fidx);
      for (unsigned idx = prior_round_frame_no; idx < fcex->fidx; ++idx)
        eager_push_lemmas(idx); // push from prior frame, in case of multiple frames
    }
    prior_round_frame_no = fcex->fidx;

    if (frame_implies(fcex->fidx, smart_not(fcex->cex->to_expr(solver_)))) {
      proof_goals.pop();
      D(2, "[recursive_block] F{} -> not(cex)", fcex->fidx);
      continue;
    }
    if (fcex->fidx == 0) {
      // generally should fail
      // check that it has intersection with init
      // and the chain is actually all reachable (by creating an unroller)
      
      D(2, "[recursive_block] Cannot block @0");
      sanity_check_cex_is_correct(fcex);
      return false;
    } // else check if reachable from prior frame
    auto reachable_from_prior_frame =  rel_ind_check(fcex->fidx-1, nullptr, fcex->cex, true);
    if(!reachable_from_prior_frame.not_hold) {
      // unsat/unreachable
      // TODO make a lemma, to explain why F(i) /\ T => not MODEL
      
      D(2, "[recursive_block] Not reachable from F{}", fcex->fidx-1);
      inductive_generalization(fcex->fidx-1, fcex->cex, fcex->cex_origin);
      proof_goals.pop();
      continue;
    } // else push queue
    Model * pre_model = reachable_from_prior_frame.prev_ex;
    proof_goals.new_proof_goal(fcex->fidx-1, pre_model, fcex->cex_origin.to_prior_frame(), fcex);
    
    D(2, "[recursive_block] reachable, traceback to F{}", fcex->fidx-1);
  } // end of while proof_goal is not empty
  proof_goals.clear(); // clear the model buffer, required by proof_goals class
  return true;
} // recursive_block_all_in_queue


// ( ( not(S) /\ F /\ T ) \/ init_prime ) /\ ( S )

void IC3ng::inductive_generalization(unsigned fidx, Model *cex, LCexOrigin origin) {

  auto F = get_frame_formula(fidx);
  auto T = get_trans_for_vars(cex->get_varset_noslice()); // find the update F for vars in set...
  auto F_and_T = smart_and<smt::TermVec>({F,T});


  smt::TermVec conjs;
  cex->to_expr_conj(solver_, conjs);
  auto cex_expr = smart_not(smart_and(conjs));
  // TODO: sort conjs

  smt::TermList conjs_nxt;
  std::unordered_map<smt::Term, size_t> conjnxt_to_idx_map;
  size_t old_size = conjs.size();
  for (size_t idx = 0; idx < old_size; ++idx) {
    conjs_nxt.push_back(ts_.next(conjs.at(idx)));
    conjnxt_to_idx_map.emplace(conjs_nxt.back(), idx);
  }

  smt::Term base = 
    smart_or<smt::TermVec>(
      {smart_and<smt::TermVec>(  {cex_expr, F_and_T} ) , init_prime_ } );
  
  do{
    if (old_size > conjs_nxt.size()) {
      smt::TermVec remaining_conjs;
      for (const auto & c : conjs_nxt)
        remaining_conjs.push_back(conjs.at(conjnxt_to_idx_map.at(c)));
      cex_expr = smart_not(smart_and(remaining_conjs));
      old_size = conjs_nxt.size();
      base = smart_or<smt::TermVec>(
        { smart_and<smt::TermVec>(  {cex_expr, F_and_T} ) , init_prime_ } );
    }

    solver_->push();
    syntax_analysis::reduce_unsat_core_to_fixedpoint(base, conjs_nxt, solver_);
    solver_->pop();
    D(2, "[ig] core size: {} => {}", old_size, conjs_nxt.size());

    if (old_size > conjs_nxt.size()) {
      smt::TermVec remaining_conjs;
      for (const auto & c : conjs_nxt)
        remaining_conjs.push_back(conjs.at(conjnxt_to_idx_map.at(c)));
      cex_expr = smart_not(smart_and(remaining_conjs));
      old_size = conjs_nxt.size();
      base = smart_or<smt::TermVec>(
        { smart_and<smt::TermVec>(  {cex_expr, F_and_T} ) , init_prime_ } );
    }

    solver_->push();
    syntax_analysis::reduce_unsat_core_linear_rev(base, conjs_nxt, solver_);
    solver_->pop();

  } while(old_size > conjs_nxt.size());

  auto lemma = new_lemma(cex_expr, cex, origin);
  add_lemma_to_frame(lemma,fidx+1);
  D(2,"[ig] F{} get lemma:{}", fidx+1, lemma->to_string());
}


ProverResult IC3ng::step(int i)
{
  if (i <= reached_k_) {
    return ProverResult::UNKNOWN;
  }

  if (reached_k_ < 1) {
    if(check_init_failed())
      return ProverResult::FALSE;
    D(1, "[Checking property] init passed");
    
    reached_k_ = 1;
    return ProverResult::UNKNOWN;
  }

  // `last_frame_reaches_bad` will add to proof obligation
  while (last_frame_reaches_bad()) {
    size_t nCube = proof_goals.size();
    if(! recursive_block_all_in_queue() )
      return ProverResult::FALSE;
    D(1, "[step] Blocked {} CTI on F{}", nCube, frames.size()-1);
  }
  
  append_frame();
  D(1, "[step] Extend to F{}", frames.size()-1);

  // TODO: print cubes?  

  // recursive block should have already pushed everything pushable to the last frame
  // so, we can simply push from the previous last frame
  //  should return true if all pushed
  //  should push necessary cex to the queue
  auto old_fsize = (++frames.rbegin())->size();
  if ( push_lemma_to_new_frame() ) {
    validate_inv();
    return ProverResult::TRUE;
  }
  
  auto new_fsize = (frames.rbegin())->size();
  D(1, "[step] Pushed {}/{} Lemmas to F{}", new_fsize, old_fsize, frames.size()-1 );
  D(1, "[step] Added {} CTI on F{} ", proof_goals.size(), frames.size()-1 );

  // new proof obligations may be added
  if (!recursive_block_all_in_queue())
    return ProverResult::FALSE;

  ++reached_k_;
  
  return ProverResult::UNKNOWN;
} // end of step


ProverResult IC3ng::check_until(int k) {
  initialize();
  assert(initialized_);

  ProverResult res;
  int i = reached_k_ + 1;
  assert(reached_k_ + 1 >= 0);
  while (i <= k) {
    res = step(i);
    if (res == ProverResult::FALSE) {
      // currently no abstraction
      return res;
    } else {
      ++i;
    }

    if (res != ProverResult::UNKNOWN) {
      return res;
    }
  }

  return ProverResult::UNKNOWN;
}


/**
 * This function should check F[-1] /\ P
 * Need to consider assumptions!
 * Need to insert the model into proof_goals
*/
bool IC3ng::last_frame_reaches_bad() {
  // use relative inductive check?
  auto result = rel_ind_check(frames.size()-1, bad_next_trans_subst_, NULL, true);
  if (!result.not_hold) 
    return false;
  proof_goals.new_proof_goal(frames.size()-1, result.prev_ex, LCexOrigin::MustBlock(1), NULL);
  // else
  return true;
}


} // namespace pono
