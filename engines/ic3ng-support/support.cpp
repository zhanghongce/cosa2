#pragma once

#include "engines/ic3ng.h"

namespace pono {

bool IC3ng::can_sat(const smt::Term & t) {
  solver_->push();
  solver_->assert_formula(t);
  auto res = solver_->check_sat();
  solver_->pop();
  return res.is_sat();
}

} // end of namespace pono
