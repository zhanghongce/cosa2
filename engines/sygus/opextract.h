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
 ** \brief Operator extractor
 **
 ** 
 **/
 
#pragma once

#include "walker.h"
#include "syntax.h"

namespace cosa {


// we'd better extract from msat's term
// btor's mixing bool and 1-width bv will
// create problems
class OpExtractor : public Walker {

public:
  sygus::SyntaxStructure & 
    GetSyntaxConstruct() {
      return constructs; }

protected:
  std::unordered_set<smt::Term> walked_nodes_;
  std::unordered_set<smt::Term> all_symbols_;
  sygus::SyntaxStructure constructs;
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;


}; // class OpExtractor


// ------------- VarExtractor ------------- //
// you can use get_free_symbols, actually

}  // namespace cosa




