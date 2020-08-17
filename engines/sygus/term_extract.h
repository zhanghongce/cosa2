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
 ** \brief Term extractor
 **
 ** 
 **/
  
#pragma once

#include "walker.h"

namespace cosa {
  
namespace policy_sat_enum {

class TermExtractor : public Walker {
public:
  enum class node_type_t {IN, OUT};
  struct node_info_t {
    node_type_t node_type;
    unsigned level;
    node_info_t() : node_type(node_type_t::OUT), level(0) {}
  };
  
  TermExtractor(const std::unordered_set<smt::Term> & varset) :
    related_vars_(varset) { }
  
protected:
  std::unordered_map<smt::Term, node_info_t> walked_nodes_;
  const std::unordered_set<smt::Term> & related_vars_; // we will also bring in unrelated vars
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;

}; // class TermExtractor

} // namespace policy_sat_enum

}  // namespace cosa

