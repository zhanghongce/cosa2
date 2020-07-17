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
 ** \brief A dummy transition system to hold msat ts
 **
 **
 **/
 
 
#pragma once

#include "ts.h"

#include <unordered_map>
 

namespace cosa {
 
class TransferredTransitionSystem : public TransitionSystem {
 
  protected:
    //smt::SmtSolver & from_solver_;
    smt::TermTranslator & translater_;
    std::unordered_map<smt::Term,smt::Term> symbol_map_ex2in; // external_to_internal
    std::unordered_map<smt::Term,smt::Term> symbol_map_in2ex; // external_to_internal

   
  public:
    TransferredTransitionSystem( const TransitionSystem & ts, 
      //smt::SmtSolver from_solver,
      smt::SmtSolver & to_solver,
      smt::TermTranslator & translator );
   
    void setup_reverse_translator(smt::TermTranslator &) const;
  
 }; // class DummyTransitionSystem
 

} // namespace cosa

