/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Makai Mann, Florian Lonsing
 ** This file is part of the pono project.
 ** Copyright (c) 2019, 2021, 2022 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#pragma once

#include "engines/prover.h"

namespace pono {

class BtorSim : public Prover
{
public:
  BtorSim(const Property & p, const TransitionSystem & ts,
      const smt::SmtSolver & solver,
      PonoOptions opt = PonoOptions());

  ~BtorSim();

  typedef Prover super;

  void initialize() override;

  ProverResult check_until(int k) override;

 protected:
  smt::Term base_formula;

};  // class BtorSim

}  // namespace pono
