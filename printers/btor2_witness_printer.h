/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann, Ahmed Irfan
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include <iterator>
#include <map>
#include <sstream>
#include <vector>

#include "smt-switch/smt.h"
#include "frontends/btor2_encoder.h"

#include "utils/logger.h"

namespace pono {

/// print a counterexample trace to stdout
void print_witness_btor(const BTOR2Encoder & btor_enc,
                        const std::vector<smt::UnorderedTermMap> & cex);

}  // namespace pono
