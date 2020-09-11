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
#include <map>

namespace cosa {

  struct APdrConfig {
    unsigned MAX_FRAME   = 10000000;
    // Partial model gen
    bool CACHE_PARTIAL_MODEL_CONDITION = false;

    // SyGuS related

    // SAT(c? /\ T /\ not c'), or
    // SAT(      T /\ not c')
    const bool RM_CEX_IN_PREV = true;


    bool MSAT_INTERPOLANT_ENABLE = true;
    
    bool UNSATCORE_FIXPOINT_REDUCTION = true;
    bool UNSATCORE_MUS_REDUCTION = true;
    unsigned UNSAT_CORE_MULTI = 1; // 0 : all , you may want different things for may/must
    bool SUBSUME_NO_PUSH_RETRY = true; // if a cex is subsume, its lemma will not be retried

    // ------------- TERM Generation  ---------------------------------
    unsigned TERM_EXTRACT_DEPTH = 0; // 2; depth == 0 means all possible sol
    unsigned INITIAL_TERM_WIDTH = 8; // (-1 to disable this)
    unsigned INITIAL_TERM_INC   = 8;
    unsigned ACCUMULATED_TERM_BOUND = 0; // let's try 0 first

    
    // ------------- SyGuS Configuration ---------------------------------

    enum LEMMA_GEN_MODE_T {
      ITP_ONLY = 1,
      ITP_VAR_EXTRACT = 2,
      ITP_SYNTAX_EXTRACT = 4,
      ITP_VAR_AND_SYNTAX_EXTRACT = 6, // 2 + 4
      SYGUS_ONLY = 8,
      ITP_AND_SYGUS_NO_SYNTAX_UPDATE = 9 // 8 + 1   
    } LEMMA_GEN_MODE = ITP_ONLY;


    // ------------- STATUS tracking ---------------------------------
    enum Apdr_working_state_t { 
      IDLE = 0,
      SOLVE_TRANS,
      SOLVE_TRANS_LEMMA,
      RECURSIVE_BLOCK,
      CHECK_UNTIL,
      PUSH_A_FRAME,
      PUSH_EAGER,
      MAKE_NEW_TERM,
      MAKE_NEW_TERM_ROUND }; // definition of functionnames in config.cpp
    
    const static std::vector<std::string> function_names;

    std::map<Apdr_working_state_t, unsigned> Apdr_function_invocation_count;

    std::vector<Apdr_working_state_t> Apdr_working_state_stack;

    void Apdr_function_tracing_stack_push(Apdr_working_state_t f) {
      Apdr_working_state_stack.push_back(f);
      if (Apdr_function_invocation_count.find(f) == Apdr_function_invocation_count.end())
        Apdr_function_invocation_count[f] = 0;
      ++ Apdr_function_invocation_count[f];
    }

    const std::string & Apdr_function_tracing_func_str(Apdr_working_state_t f) {
      return function_names.at((unsigned) (f));
    }

    Apdr_working_state_t Apdr_function_tracing_stack_pop() {
      Apdr_working_state_t ret = Apdr_working_state_stack.back();
      Apdr_working_state_stack.pop_back();
      return ret;
    }

    // ------------- STATUS tracking ---------------------------------
    SignalPDRInterface * ApdrInterface = NULL;

  };

  extern APdrConfig GlobalAPdrConfig;

}; // namespace cosa
