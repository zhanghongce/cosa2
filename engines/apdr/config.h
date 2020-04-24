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
 ** \brief APDR header
 **
 ** 
 **/
 
#pragma once

namespace cosa {

namespace pdr_config {
  const unsigned MAX_FRAME   = 10000000;
  const bool     USE_ITP_IN_PUSHING = false;
  const bool     DEBUG = true;
  const bool     DEBUG_PRINT = true;
  const bool     USE_SYGUS = false;
  const bool     RM_CEX_IN_PREV = true;
  const bool     USE_FACT_IN_SYGUS = false;
  const unsigned ENHANCE_GIVEUP_THRESHOLD_FAILED = 2;
  const unsigned ENHANCE_GIVEUP_THRESHOLD_TRIALS = 3;        // 2/3
  const unsigned CEX_INVALID_ITP_GUESS_THRESHOLD_FAILED = 4; // 4/5
  const unsigned CEX_INVALID_ITP_GUESS_THRESHOLD_TRIALS = 5;
  const unsigned long long STRENGTHEN_EFFORT_FOR_PROP = 10000;
}; // namespace pdr_config


}; // namespace cosa
