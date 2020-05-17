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
 ** \brief SMT-LIB2 property parser
 **
 ** 
 **/
 
#pragma once

#include "smtlib2parser.h"
#include "core/ts.h"

namespace cosa {
 
/// \brief the class for parsing a smt-lib2 property, assertion/assumption
/// an instance must be kept alive while using the term

class Smtlib2PropertyParser : public Smtlib2Parser {
public:
  typedef std::vector<smt::Term> ArgListT;
  typedef std::pair<ArgListT, smt::Term> FuncDefT;
  typedef std::unordered_map<std::string,FuncDefT> FuncDefTableT;

public:
  Smtlib2PropertyParser(
    smt::SmtSolver & solver,
    TransitionSystem & ts);
    
  virtual ~Smtlib2PropertyParser();
  
  // return false if failed, ow, succ
  bool ParsePropertyFromFile(const std::string& fname);
  
  const smt::TermVec & propvec() const { return propvec_; };
  
protected:
  // override the (define-fun function)
  // this function receives the transition result
  void virtual define_function(const std::string& func_name,
                       const std::vector<TermPtrT> & args,
                       SortPtrT ret_type, TermPtrT func_body) override;
  

  virtual TermPtrT make_function(const std::string& name, SortPtrT sort,
     const std::vector<int>& idx, const std::vector<TermPtrT>& args ) override;
  
  virtual void * push_quantifier_scope() override;
  virtual void * pop_quantifier_scope() override;
  
  // the property vector
  smt::TermVec propvec_;
  
  TransitionSystem & ts_;

  FuncDefTableT func_def_table_;
  
}; // class Smtlib2PropertyParser

} // namespace cosa

