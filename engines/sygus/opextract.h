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

namespace cosa {


struct BvConstructs {
  struct concat_t  {uint64_t width1,width2;};
  struct extract_t {uint64_t input_width, h, l; };
  struct rotate_t  {smt::PrimOp op; uint64_t param; };
  struct extend_t  {smt::PrimOp op; uint64_t param, input_width; };

  std::unordered_set<std::string> symbol_names;
  // let's use to_string to fill it? so we hope we don't need to add | ourselves
  std::unordered_set<std::string> constants; // let's convert it to string
  std::unordered_set<smt::PrimOp> op_unary; // unary operators
  std::unordered_set<smt::PrimOp> op_comp;  // comparators
  // set of (width1, width2)
  std::unordered_set<concat_t> op_concat;
  // set of (input_width, h, l)
  std::unordered_set<extract_t> op_extract;
  // set of (op, param)
  std::unordered_set<rotate_t> op_rotate;
  // set of (op, param, input_width)
  std::unordered_set<extend_t> op_extend;

}; // class BvConstructs

// we'd better extract from msat's term
// btor's mixing bool and 1-width bv will
// create problems
class OpExtractor : public Walker {

protected:
  std::unordered_set<smt::Term> walked_nodes_;
  std::unordered_set<smt::Term> all_symbols_;
  std::unordered_map<uint64_t, BvConstructs> constructs;
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;


}; // class OpExtractor


}  // namespace cosa




