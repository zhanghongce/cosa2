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
 ** \brief To BTOR to CHC
 **
 **
 **/

#pragma once

#include "prop.h"
#include "smt-switch/smt.h"
#include "ts.h"

#include <iostream>
#include <string>
#include <unordered_map>

namespace cosa {

class ChcPrinter{

protected:
  const TransitionSystem & ts_;
  const Property & property_;

  const smt::UnorderedTermSet & states_;
  const smt::UnorderedTermSet & next_states_;
  const smt::UnorderedTermSet & inputs_;
  const smt::UnorderedTermSet & next_inputs_;

  std::string primal_var_def_;
  std::string prime_var_def_;
  std::string input_var_def_;

  std::string trans_def_;
  std::string trans_use_;
  std::string init_def_;
  std::string init_use_;
  std::string property_def_;
  std::string property_use_;
  std::string inv_var_type_;
  std::string inv_var_prime_use_;
  
  std::string state_arg_def_;
  std::string state_arg_use_;

  std::unordered_map<std::string, std::string> state_to_next_map_;


public:
  ChcPrinter (const Property & p);

  void Export(std::ostream & os) const;

}; // class ChcPrinter

} // namespace cosa
