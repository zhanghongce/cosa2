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
 ** \brief bv bool converter
 **
 **
 **/
 
#pragma once

#include "smt-switch/smt.h"

namespace cosa {
    
 // for msat as it is not happy with bvcomp as bool
smt::Term bv_to_bool_msat(const smt::Term & t, const smt::SmtSolver & itp_solver_ );

 // states should be bitvectors
smt::Term bool_to_bv_msat(const smt::Term & t, const smt::SmtSolver & itp_solver_ );

} // namespace cosa

