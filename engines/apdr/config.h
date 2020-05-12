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

#include "sig_apdr_if.h"

#include <vector>

namespace cosa {

  struct APdrConfig {
    unsigned MAX_FRAME   = 10000000;

    // SyGuS related
    bool     USE_SYGUS_REPAIR = false;
    bool     USE_SYGUS_REPAIR_LEMMA_MAY_BLOCK = true;
    bool     USE_FACT_IN_SYGUS_REPAIR = false;
    bool     USE_SYGUS_LEMMA_GEN = false;

    // later we may introduce the possiblity to avoid
    // msat's interpolant, but not now
    const bool USE_ITP = true; 

    // SAT(p? /\ T /\ not p'), or
    // SAT(      T /\ not p')
    const bool RM_CEX_IN_PREV = true;

    // lemma pushing in general
    unsigned ENHANCE_GIVEUP_THRESHOLD_FAILED = 2;
    unsigned ENHANCE_GIVEUP_THRESHOLD_TRIALS = 3;        // 2/3
    unsigned CEX_INVALID_ITP_GUESS_THRESHOLD_FAILED = 4; // 4/5
    unsigned CEX_INVALID_ITP_GUESS_THRESHOLD_TRIALS = 5;

    bool BLOCK_CTG = true;
    bool BLOCK_CTG_MAY_BLOCK_LEMMA = true;
    // lemma strengthening method: CTG blocking (may blocking)
    unsigned STRENGTHEN_EFFORT_FOR_MUST_BLOCK = 50; //10000;

    // 
    unsigned STRENGTHEN_EFFORT_FOR_MAY_BLOCK = 10; //1000; // has no use
    const bool  TRY_STRENGTHEN_LEMMA_MAY_BLOCK = true; // if the above is false -- this should be true
      // otherwise, the cex is blockable and you do nothing? -- not right

    bool COI_CACHING_ENABLE = true;
    bool MSAT_INTERPOLANT_ENABLE = true;

    // ------------- SyGuS Configuration ---------------------------------

    bool SYGUS_EXPAND_VALUES = false;
    bool SYGUS_USE_TRANS = true;
    bool SYGUS_USE_INIT = true;
    bool SYGUS_USE_FACT = true;

    // ------------- STATISTICS tracking ---------------------------------
    bool STAT_ITP_STRICTLY_STRONG_CHECK = true;
    uint64_t STAT_ITP_CHECK_COUNT = 0;
    uint64_t STAT_ITP_STRONG_COUNT = 0;

    // ------------- STATUS tracking ---------------------------------
    enum APDR_WORKING_STATE_T { 
      IDLE = 0,
      INITCACHE, 
      CHECK_UNTIL,
      GETTING_BAD_FOR_PROP, 
      BLOCKING_BAD_FOR_PROP, 
      PUSHING_ALL,
      PUSH_A_FRAME,
      PUSH_FIRST_TRY_ALL, PUSH_TRY_CEX, PUSH_TRY_SYGUS,
      PUSH_TRY_BLOCK_CTG,
      SOLVE_TRANS,
      RECURSIVE_BLOCK_TRY,
      RECURSIVE_BLOCK_DO };
    
    typedef std::pair<APDR_WORKING_STATE_T, unsigned> APDR_STACK_STATE_T;
    APDR_STACK_STATE_T APDR_WORKING_STATE;

    std::vector<APDR_STACK_STATE_T> APDR_WORKING_STATE_STACK = {{IDLE,0}};

    // ------------- STATUS tracking ---------------------------------
    SignalPDRInterface * ApdrInterface = NULL;

  };

  extern APdrConfig GlobalAPdrConfig;

}; // namespace cosa
