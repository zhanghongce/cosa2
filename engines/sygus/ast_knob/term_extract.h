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
 ** \brief Term extractor
 **
 ** 
 **/
  
#pragma once

#include "walker.h"

#include <map>

namespace cosa {
  
namespace unsat_enum {

class TermExtractor : public Walker {
public:
  // ----------- TYPE --------------- //
  struct node_info_t {
    bool in;
    unsigned level;
    node_info_t() : in(false), level(0) {}
  };
  
  
  // ----------- CONSTRUCTOR --------------- //
  TermExtractor(const std::unordered_set<smt::Term> & varset, bool collect_constants, unsigned level) :
    related_vars_(varset), collect_constants_(collect_constants), level_(level) { }
    
  const std::map<unsigned, std::vector<smt::Term>> & GetTerms() const { return width_to_terms_; }
  const std::map<unsigned, std::vector<smt::Term>> & GetConstants() const { return width_to_constants_; }
  
  // public method inherited: WalkDFS (*) /BFS
  
protected:
  std::unordered_map<smt::Term, node_info_t> walked_nodes_;
  const std::unordered_set<smt::Term> & related_vars_; // we will also bring in unrelated vars
  bool collect_constants_;
  unsigned level_;
  
  std::map<unsigned, std::vector<smt::Term>> width_to_terms_;
  std::map<unsigned, std::vector<smt::Term>> width_to_constants_;
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;

}; // class TermExtractor


} // namespace unsat_enum

}  // namespace cosa

