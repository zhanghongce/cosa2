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
  frame_t remaining_lemmas;
  for (Lemma * l : prev_frame) {
    auto bad_nxt_tr_subst_ =  next_trans_replace(ts_.next(l->expr()));
    auto result = rel_ind_check(prev_fidx,  bad_nxt_tr_subst_, NULL, false);
    if(result.not_hold) {
      all_pushed = false;
      remaining_lemmas.push_back(l);
      if (l->origin().is_must_block())
        proof_goals.new_proof_goal(prev_fidx+1, l->cex(), l->origin());
    } else {
      add_lemma_to_frame(l, prev_fidx+1);
    }
  } // end for all lemmas
  frames.at(prev_fidx).swap(remaining_lemmas); // directly swap

  if (all_pushed) {
    const auto & last_frame = frames.at(prev_fidx+1);
    // if all pushed, then make the invariant
    smt::TermVec all_lemmas;
    all_lemmas.reserve(last_frame.size());
    for (Lemma * l : last_frame)
      all_lemmas.push_back(l->expr());
    invar_ = smart_and(all_lemmas);
  }
  return all_pushed;
} // end of push_lemma_to_new_frame


void IC3ng::eager_push_lemmas(unsigned fidx) {
  auto prev_fidx = fidx;
  const auto & prev_frame = frames.at(prev_fidx);
  frame_t remaining_lemmas;
  for (Lemma * l : prev_frame) {
    auto bad_nxt_tr_subst_ =  next_trans_replace(ts_.next(l->expr()));
    auto result = rel_ind_check(prev_fidx,  bad_nxt_tr_subst_, NULL, false);
    if(result.not_hold) {
      remaining_lemmas.push_back(l);
      if (l->origin().is_must_block())
        proof_goals.new_proof_goal(prev_fidx+1, l->cex(), l->origin());
    } else {
      add_lemma_to_frame(l, prev_fidx+1);
    }
  } // end for all lemmas
  frames.at(prev_fidx).swap(remaining_lemmas); // directly swap
} // end of eager_push_lemmas


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
  if (!res.is_unsat())
    throw PonoException("Unsound inductive invariant. Implementation Error!");
  
  solver_->push();
  solver_->assert_formula(invar_);
  solver_->assert_formula(smart_not(next_trans_replace(ts_.next(invar_))));
  res = solver_->check_sat();
  solver_->pop();
  if (!res.is_unsat())
    throw PonoException("Unsound inductive invariant. Implementation Error!");

  solver_->push();
  solver_->assert_formula(invar_);
  solver_->assert_formula(bad_);
  res = solver_->check_sat();
  solver_->pop();
  if (!res.is_unsat())
    throw PonoException("Unsound inductive invariant. Implementation Error!");
} // end of validate_inv


void IC3ng::sanity_check_cex_is_correct(fcex_t * cex_at_cycle_0) {
  assert(cex_at_cycle_0);
  // check consecution of the cexs
  std::vector<Model *> cexs;
  const fcex_t * ptr = cex_at_cycle_0;
  while(ptr) {
    assert(ptr->fidx == cexs.size());
    cexs.push_back(ptr->cex);
    ptr = ptr->next;
  }
  auto cex_length = cexs.size();
  solver_->push();
  solver_->assert_formula(unroller_.at_time(ts_.init(), 0)); // init @ 0
  for(size_t t = 0; t < cex_length; ++t) {
    solver_->assert_formula(unroller_.at_time(ts_.trans(), t));
    solver_->assert_formula(unroller_.at_time(cexs[t]->to_expr(solver_), t));
    auto res = solver_->check_sat();
    if (!res.is_sat())
      throw PonoException("Unsound counterexample. IMPLEMENTATION ERROR!");
  }
  solver_->pop();
} // end of sanity_check_cex_is_correct

} // end of namespace pono
