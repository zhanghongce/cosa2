#include "utils/logger.h"
#include "engines/ic3ng.h"
#include "engines/ic3ng-support/debug.h"

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



  //  should return true if all pushed
  //  should push necessary cex to the queue
bool IC3ng::push_lemma_to_new_frame() {
  for (unsigned prev_fidx = lowest_frame_touched_; prev_fidx < frames.size()-1; ++prev_fidx) {
    
    bool is_last_push = (prev_fidx == frames.size()-2);
    const auto & prev_frame = frames.at(prev_fidx);
    bool all_pushed = true;
    frame_t remaining_lemmas;
    for (Lemma * l : prev_frame) {
      // you do not need to check, we assume this by default
      if (l->origin().is_constraint()) {
        add_lemma_to_frame(l, prev_fidx+1);
        continue;
      }

      auto bad_nxt_tr_subst_ = smart_not( next_trans_replace(ts_.next(l->expr())));
      auto result = rel_ind_check(prev_fidx,  bad_nxt_tr_subst_, NULL, false);
      if(result.not_hold) {
        all_pushed = false;
        remaining_lemmas.push_back(l);
        assert(! (l->origin().is_the_property())); // property should always pushable
                                                  // otherwise we should not arrive at this step
        
        // if it is not the last frame to push, we should have already tried to push that
        // which should have generated some new lemmas to block that
        if (is_last_push && l->origin().is_must_block())
          proof_goals.new_proof_goal(prev_fidx+1, l->cex(), l->origin());
      } else {
        add_lemma_to_frame(l, prev_fidx+1);
      }
    } // end for all lemmas
    frames.at(prev_fidx).swap(remaining_lemmas); // directly swap

    if (all_pushed) {
      invar_ = get_frame_formula(prev_fidx+1);
      return true; // we can stop early
    }
  }
  return false;
} // end of push_lemma_to_new_frame


smt::Term IC3ng::get_trans_for_vars(const smt::UnorderedTermSet & vars) {
  smt::TermVec updates;
  for (const auto & v : vars) {
    updates.push_back(
      solver_->make_term(
        smt::Equal,
        ts_.next(v),
        ts_.state_updates().at(v)));
  }
  return smart_and(updates);
}

smt::Term IC3ng::get_frame_formula(unsigned fidx) {
  assert(fidx < frames.size());
  smt::TermVec all_lemmas;
  // you must go through all later frames!!!
  for (size_t curr_fidx = fidx; curr_fidx < frames.size(); ++ curr_fidx ) {
    const auto & the_frame = frames.at(curr_fidx);
    // if all pushed, then make the invariant
    for (Lemma * l : the_frame)
      all_lemmas.push_back(l->expr());
  }
  return smart_and(all_lemmas);
}

void IC3ng::eager_push_lemmas(unsigned fidx, unsigned start_lemma_id) {
  auto prev_fidx = fidx;
  const auto & prev_frame = frames.at(prev_fidx);
  frame_t remaining_lemmas;
  assert(start_lemma_id < prev_frame.size());
  for (size_t lidx = start_lemma_id; lidx < prev_frame.size(); lidx++) {
    Lemma * l = prev_frame.at(lidx);
    assert(!(l->origin().is_the_property()));
    assert(!(l->origin().is_constraint()));
    auto bad_nxt_tr_subst_ =  smart_not( next_trans_replace(ts_.next(l->expr())));
    auto result = rel_ind_check(prev_fidx,  bad_nxt_tr_subst_, NULL, false);
    if(result.not_hold) {
      remaining_lemmas.push_back(l);
      if (l->origin().is_must_block())
        proof_goals.new_proof_goal(prev_fidx+1, l->cex(), l->origin());
    } else {
      add_lemma_to_frame(l, prev_fidx+1);
    }
  }
  auto & mod_prev_frame = frames.at(prev_fidx);
  for (size_t lidx = 0; lidx < remaining_lemmas.size(); ++lidx) {
    mod_prev_frame.at(lidx + start_lemma_id) = remaining_lemmas.at(lidx);
  }
  mod_prev_frame.resize(start_lemma_id+remaining_lemmas.size());
} // end of eager_push_lemmas


void IC3ng::validate_inv() {

  // check init /\ not(inv)  should be UNSAT
  //       inv /\ not(replace(nxt(inv)))    UNSAT
  //       inv /\ not(prop)            UNSAT

  assert(invar_);
  D(2,"[Checking invar] {}", invar_->to_string());
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


void IC3ng::assert_frame(unsigned fidx) {
  assert(fidx < frame_labels_.size());
  for (unsigned idx = 0; idx < frame_labels_.size(); ++idx) {
    if (idx >= fidx) {// Fi -> Fi+1
      solver_->assert_formula(frame_labels_.at(idx));
    } else { // to disable other frames
      solver_->assert_formula(smart_not(frame_labels_.at(idx)));
    }
  }
}

bool IC3ng::frame_implies(unsigned fidx, const smt::Term & expr) {
  solver_->push();
  assert_frame(fidx);
  solver_->assert_formula(smart_not(expr));
  auto r = solver_->check_sat();
  solver_->pop();
  return r.is_unsat();
}


bool IC3ng::check_init_failed() {
  solver_->push();
    solver_->assert_formula(init_label_); // init contains assumptions already
    solver_->assert_formula(bad_);
    auto r1 = solver_->check_sat();
  solver_->pop();
  if(r1.is_sat())
    return true;
  
  solver_->push();
    solver_->assert_formula(init_label_); // init contains assumptions already
    // solver_->assert_formula(constraint_label_); // already added from frame[0]
    solver_->assert_formula(bad_next_trans_subst_); // T is inside bad_next_trans_subst_
    r1 = solver_->check_sat();
  solver_->pop();
  if(r1.is_sat())
    return true;
  return false;
}


std::string IC3ng::print_frame_stat() const {
  std::string output = "F[" + std::to_string(frames.size()) + "] ";
  if (frames.size() < 20) {
    for (auto && f : frames)
      output += std::to_string(f.size()) + ' ';
    return output;
  } else {
    for(unsigned idx = 0; idx < 10; ++ idx)
      output += std::to_string(frames.at(idx).size()) + ' ';
    output += "...";
    for(unsigned idx = frames.size()-10; idx < frames.size(); ++ idx)
      output += std::to_string(frames.at(idx).size()) + ' ';
  }
  return output;
}


} // end of namespace pono
