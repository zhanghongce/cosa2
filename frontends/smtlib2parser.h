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
 ** \brief SMT-LIB2 expression parser
 **
 ** 
 **/


#pragma once

extern "C" {
#include "smtparser/smtlib2abstractparser.h"
#include "smtparser/smtlib2abstractparser_private.h"
}

#include "smt-switch/smt.h"

namespace cosa {

class Smtlib2Parser;


/// \brief the class for parsing a smt-lib2 expr
/// an instance must be kept alive while using the term
class Smtlib2Parser {

public:
  typedef std::unordered_map<std::string, smt::Term> symbol_table_t;
  typedef std::vector<symbol_table_t> symbols_stack_t;
  typedef std::unordered_map<std::string, smt::Sort> sort_table_t;

protected:
  const symbol_table_t& symbol_table_;

  smtlib2_abstract_parser* parser_wrapper;
  // actually we maybe don't need to cache terms
  smt::SmtSolver & solver_;

  // quantifier term stack
  symbols_stack_t quantifier_def_stack;
  sort_table_t sort_table;
  std::vector<smt::Term> term_allocation_table;

  smt::Term * parse_result_term;

public:
  Smtlib2Parser(
    smt::SmtSolver & solver,
    const symbol_table_t& symbol_table);
    
  virtual ~Smtlib2Parser();
  /// no copy constructor
  Smtlib2Parser(const Smtlib2Parser&) = delete;
  /// no assignment
  Smtlib2Parser& operator=(const Smtlib2Parser&) = delete;
  
  // if unsat --> add the (assert ...)
  smt::Term ParseInvResultFromFile(const std::string& fname);
  // parse from a string: assume we have the (assert ...) there
  smt::Term ParseSmtResultFromString(const std::string& text);


  // ------------------------------------------------------------------------
  
  // we probably don't need to make sort
  smt::Sort * make_bv_sort(uint64_t w);
  smt::Sort * make_sort(const std::string& name, const std::vector<int>& idx);
  void declare_quantified_variable(const std::string& name, smt::Sort * sort);

  void * push_quantifier_scope();
  void * pop_quantifier_scope();
  
  /*internal use*/ smt::Term * search_quantified_var_stack_and_symbol_table(const std::string& name) const;

  smt::Term * make_function(const std::string& name, smt::Sort *sort,
    const std::vector<int>& idx, const std::vector<smt::Term *>& args );
  
  smt::Term * make_number(const std::string& rep, int width, int base);

  /// this function receives the final assert result
  void assert_formula(smt::Term * term);
  /// this function receives the final result
  void define_function(const std::string& func_name,
                       const std::vector<smt::Term *> & args,
                       smt::Sort * ret_type, smt::Term * func_body);


#define DECLARE_OPERATOR(name)                                                 \
  smt::Term * mk_##name(const std::string& symbol, smt::Sort* sort,       \
                        const std::vector<int> & idx,                     \
                        const std::vector<smt::Term *> & args)


  // I hope it will expand lexically
  DECLARE_OPERATOR(true);
  DECLARE_OPERATOR(false);

  DECLARE_OPERATOR(and);
  DECLARE_OPERATOR(or);
  DECLARE_OPERATOR(not);
  DECLARE_OPERATOR(implies);
  DECLARE_OPERATOR(eq);
  DECLARE_OPERATOR(ite);
  DECLARE_OPERATOR(xor);
  DECLARE_OPERATOR(nand);
  DECLARE_OPERATOR(concat);
  DECLARE_OPERATOR(bvnot);
  DECLARE_OPERATOR(bvand);
  DECLARE_OPERATOR(bvnand);
  DECLARE_OPERATOR(bvor);
  DECLARE_OPERATOR(bvnor);
  DECLARE_OPERATOR(bvxor);
  DECLARE_OPERATOR(bvxnor);
  DECLARE_OPERATOR(bvult);
  DECLARE_OPERATOR(bvslt);
  DECLARE_OPERATOR(bvule);
  DECLARE_OPERATOR(bvsle);
  DECLARE_OPERATOR(bvugt);
  DECLARE_OPERATOR(bvsgt);
  DECLARE_OPERATOR(bvuge);
  DECLARE_OPERATOR(bvsge);
  DECLARE_OPERATOR(bvcomp);
  DECLARE_OPERATOR(bvneg);
  DECLARE_OPERATOR(bvadd);
  DECLARE_OPERATOR(bvsub);
  DECLARE_OPERATOR(bvmul);
  DECLARE_OPERATOR(bvudiv);
  DECLARE_OPERATOR(bvsdiv);
  DECLARE_OPERATOR(bvsmod);
  DECLARE_OPERATOR(bvurem);
  DECLARE_OPERATOR(bvsrem);
  DECLARE_OPERATOR(bvshl);
  DECLARE_OPERATOR(bvlshr);
  DECLARE_OPERATOR(bvashr);
  DECLARE_OPERATOR(extract);
  DECLARE_OPERATOR(bit2bool);
  DECLARE_OPERATOR(repeat);
  DECLARE_OPERATOR(zero_extend);
  DECLARE_OPERATOR(sign_extend);
  DECLARE_OPERATOR(rotate_left);
  DECLARE_OPERATOR(rotate_right);

#undef DECLARE_OPERATOR

}; // class Smtlib2Parser


} // namespace cosa


