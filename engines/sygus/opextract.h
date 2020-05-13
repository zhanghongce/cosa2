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

namespace sygus {

  std::string name_sanitize(const std::string &); 
  std::string name_desanitize(const std::string &s);

  struct concat_t  {
    uint64_t width1; uint64_t width2;
    concat_t(uint64_t w1, uint64_t w2) :
      width1(w1), width2(w2) { }
  };
  struct extract_t {
    uint64_t input_width, h, l;
    extract_t(uint64_t iw, uint64_t _h, uint64_t _l) :
      input_width(iw), h(_h), l(_l) { }
  };
  struct rotate_t  {
    smt::PrimOp op; uint64_t param;
    rotate_t(smt::PrimOp _op, uint64_t _param) :
      op(_op), param(_param) { }
  };
  struct extend_t  {
    smt::PrimOp op; uint64_t extw, input_width;
    extend_t(smt::PrimOp _op, uint64_t _extw, uint64_t _iw) :
      op(_op), extw(_extw), input_width(_iw) { }
  };

  class concat_hash {
  public:
    size_t operator() (const concat_t & t) const;
  }; 
  class extract_hash {
  public:
    size_t operator() (const extract_t & t) const;
  }; 
  class rotate_hash {
  public:
    size_t operator() (const rotate_t & t) const;
  }; 
  class extend_hash {
  public:
    size_t operator() (const extend_t & t) const;
  }; 


  bool operator==(const concat_t & a,  const concat_t & b);
  bool operator==(const extract_t & a, const extract_t & b);
  bool operator==(const rotate_t & a,  const rotate_t & b);
  bool operator==(const extend_t & a,  const extend_t & b);

  struct BvConstructs {
    std::unordered_set<std::string> symbol_names;
    // let's use to_string to fill it? so we hope we don't need to add | ourselves
    std::unordered_set<std::string> constants; // let's convert it to string
    std::unordered_set<smt::PrimOp> op_unary;  // unary operators: (_ bv x) -> (_ bv x)
    std::unordered_set<smt::PrimOp> op_binary; // binary operators: (_ bv x) x (_ bv x) -> (_ bv x)
    std::unordered_set<smt::PrimOp> op_comp;  // comparators: (_ bv x) x (_ bv x) -> bool
    // set of (width1, width2)
    std::unordered_set<concat_t, concat_hash> op_concat;
    // set of (input_width, h, l)
    std::unordered_set<extract_t, extract_hash> op_extract;
    // set of (op, param)
    std::unordered_set<rotate_t, rotate_hash> op_rotate;
    // set of (op, param, input_width)
    std::unordered_set<extend_t, extend_hash> op_extend;

    // default constructor
    BvConstructs() {}

  }; // class BvConstructs

  typedef std::unordered_map<uint64_t, sygus::BvConstructs> SyntaxStructureT;

} //namespace sygus

// we'd better extract from msat's term
// btor's mixing bool and 1-width bv will
// create problems
class OpExtractor : public Walker {

public:
  const sygus::SyntaxStructureT & 
    GetSyntaxConstruct() const {
      return constructs; }
  
  void RemoveUnusedWidth();

protected:
  std::unordered_set<smt::Term> walked_nodes_;
  std::unordered_set<smt::Term> all_symbols_;
  sygus::SyntaxStructureT constructs;
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;


}; // class OpExtractor


// ------------- VarExtractor ------------- //
// you can use get_free_symbols, actually

}  // namespace cosa




