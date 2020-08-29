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
 ** \brief Variable to Terms Cache
 **
 ** 
 **/

#pragma once

#include "smt-switch/smt.h"
#include "engines/sygus/partial_model.h"

#include <map>

namespace cosa {

namespace unsat_enum {

struct PerWidthInfo {
 std::vector<smt::Term> terms;
 std::vector<smt::Term> constants;
};

struct PerVarsetInfo {
  std::map<unsigned, PerWidthInfo> terms;
  std::unordered_set<std::string> terms_strings;
};

class VarTermManager{
  
public:
  VarTermManager() {}
  void RegisterTermsToWalk(const smt::Term & t) { terms_to_check_.push_back(t); } // register the init by var and also trans by var, and property
  
  // this includes Constant Terms (will be inserted)
  const PerVarsetInfo & GetAllTermsForVarsInModel(Model * m);

protected:
  std::unordered_set<std::string> constants_strings_;
  std::map<unsigned, std::vector<smt::Term>> width_to_constants_;  
  std::unordered_map<std::string, PerVarsetInfo> terms_cache_; // include constants here
  
  std::vector<smt::Term> terms_to_check_;
  // from vars strings to the terms
  
}; // class VarTermManager

} // namespace unsat_enum

} // namespace cosa
