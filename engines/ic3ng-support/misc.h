#pragma once

#include "smt-switch/smt.h"

namespace pono {
// some useful utilities

  smt::Term bool_to_bv(const smt::Term & t, smt::SmtSolver & solver_);

  smt::Term bv_to_bool(const smt::Term & t, smt::SmtSolver & solver_);

  
}
