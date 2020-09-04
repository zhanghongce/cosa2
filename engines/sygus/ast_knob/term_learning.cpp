/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term Learning from Cexs
 **
 ** 
 **/
 
#include "var_term_manager.h"
#include "engines/apdr/config.h"
#include "utils/container_shortcut.h"
#include "utils/multitimer.h"

namespace cosa {

namespace unsat_enum {

// return learned new terms
unsigned TermLearner::learn_terms_from_cex(Model * pre, Model * post, /*OUTPUT*/  PerVarsetInfo & varset_info ) {
  // you will need the full model of pre !
  
} // learn_terms_from_cex


} // namespace unsat_enum

} // namespace cosa

