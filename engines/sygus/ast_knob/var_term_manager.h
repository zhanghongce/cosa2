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

#include "common.h"

#include <map>

namespace cosa {

namespace unsat_enum {

class VarTermManager{
public:
  // type definition
  typedef std::unordered_map<std::string, PerVarsetInfo> terms_cache_t;
public:
  VarTermManager() {}
  void RegisterTermsToWalk(const smt::Term & t) { terms_to_check_.push_back(t); } // register the init by var and also trans by var, and property
  
  
  // this includes Constant Terms (will be inserted)
  const PerVarsetInfo & GetAllTermsForVarsInModel(Model * m);
  unsigned GetMoreTerms(Model * pre, Model * post); // return delta terms

protected:
  std::unordered_set<std::string> constants_strings_;
  std::map<unsigned, std::vector<smt::Term>> width_to_constants_;  
  terms_cache_t terms_cache_; // include constants here
  
  std::vector<smt::Term> terms_to_check_;
  // from vars strings to the terms

protected:
  // 1. ----------------------------------------------
  // helps with the insertions
  void insert_from_constmap(const PerVarsetInfo::width_term_map_t & w_c_map) ;
  unsigned insert_from_termsmap_w_width(
    const std::map<unsigned, smt::TermVec> & terms /*IN*/, PerVarsetInfo & term_cache_item /*OUT*/ , 
    unsigned width_bound_low /*IN*/, unsigned width_bound_high /*IN*/) ;

  // 2. ----------------------------------------------
  // helps with the Terms
  const PerVarsetInfo & VarTermManager::SetupTermsForVar(
    Model * m, const std::string & canonical_string);
    
}; // class VarTermManager

} // namespace unsat_enum

} // namespace cosa
