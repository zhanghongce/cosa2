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
 ** \brief Header for information to control SyGuS from APDR side
 **
 ** 
 **/
 
#pragma once

#include "smt-switch/smt.h"
#include "unordered_set"

namespace cosa {

struct ApdrSygusHelper {
  unsigned fidx;
  smt::Term itp_btor;
  std::unordered_set<smt::Term> itp_vars;
  unsigned max_var_width;
  unsigned conj_depth_threshold_for_internal_sygus;
  // std::unordered_set<smt::Term> vars;

  void SetItpForCurrentRound(const smt::Term & itp, unsigned fidx_prev);
};

} // namespace cosa


