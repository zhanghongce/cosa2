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
}

} // end of namespace pono
