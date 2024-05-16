#pragma once

#include "engines/ic3ng.h"

namespace pono {

// can_sat is used to ensure SAT[init] and SAT[init/\T]
bool IC3ng::can_sat(const smt::Term & t) {
  solver_->push();
  solver_->assert_formula(t);
  auto res = solver_->check_sat();
  solver_->pop();
  return res.is_sat();
}

void IC3ng::cut_vars_curr(std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> & v, bool cut_curr_input) {
  auto pos = v.begin();
  if (!cut_curr_input) { // then we only cut next input
    while(pos != v.end()) {
      // if has assumption
      // will not remove input var
      if(!ts_.is_curr_var(pos->first)) {
        // assert it must be an input var
        assert(no_next_vars_nxt_.find(pos->first) != no_next_vars_nxt_.end());
        pos = v.erase(pos);
      } else
        ++pos;
    }
  } else { // if no assumption, will not keep input, erase everything but current var
    while(pos != v.end()) {
      if (actual_statevars_.find(pos->first) == actual_statevars_.end()) {
        // if it is not a state variable, then remove
        assert(no_next_vars_.find(pos->first) != no_next_vars_.end() ||
               no_next_vars_nxt_.find(pos->first) != no_next_vars_nxt_.end());
        pos = v.erase(pos);
      } else
        ++pos;
    }
  } // else : no assumption
} // end of cut_vars_curr



  // recursive block should have already pushed everything pushable to the last frame
  // so, we can simply push from the previous last frame
  //  should return true if all pushed
  //  should push necessary cex to the queue
bool IC3ng::push_lemma_to_new_frame() {
  auto prev_fidx = frames.size()-2;
  const auto & prev_frame = frames.at(prev_fidx);
  bool all_pushed = true;
  for (Lemma * l : prev_frame) {
    auto bad_nxt_tr_subst_ =  next_trans_replace(ts_.next(l->expr()));
    auto result = rel_ind_check(prev_fidx,  bad_nxt_tr_subst_, NULL, false);
    if(result.not_hold) {
      all_pushed = false;
      if (l->origin().is_must_block())
        proof_goals.new_proof_goal(prev_fidx+1, l->cex(), l->origin());
    }
  } // end for all lemmas
  if (all_pushed) {
    // if all pushed, then make the invariant
    smt::TermVec all_lemmas;
    all_lemmas.reserve(prev_frame.size());
    for (Lemma * l : prev_frame)
      all_lemmas.push_back(l->expr());
    invar_ = smart_and(all_lemmas);
  }
  return all_pushed;
} // end of push_lemma_to_new_frame



void IC3ng::validate_inv() {

  // check init /\ not(inv)  should be UNSAT
  //       inv /\ not(replace(nxt(inv)))    UNSAT
  //       inv /\ not(prop)            UNSAT

  assert(invar_);

  solver_->push();
  solver_->assert_formula(ts_.init());
  solver_->assert_formula(smart_not(invar_));
  auto res = solver_->check_sat();
  solver_->pop();
  if (res.is_unsat())
    throw PonoException("Unsound inductive invariant. Implementation Error!");
  
  solver_->push();
  solver_->assert_formula(invar_);
  solver_->assert_formula(smart_not(next_trans_replace(ts_.next(invar_))));
  auto res = solver_->check_sat();
  solver_->pop();
  if (res.is_unsat())
    throw PonoException("Unsound inductive invariant. Implementation Error!");

  solver_->push();
  solver_->assert_formula(invar_);
  solver_->assert_formula(bad_);
  auto res = solver_->check_sat();
  solver_->pop();
  if (res.is_unsat())
    throw PonoException("Unsound inductive invariant. Implementation Error!");
} // end of validate_inv


} // end of namespace pono
