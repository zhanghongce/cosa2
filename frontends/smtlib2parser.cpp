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


#include "smtlib2parser.h"
#include "smtlib2parser_callback_fn.h"

#include "utils/exceptions.h"
#include "utils/logger.h"
#include "utils/container_shortcut.h"

#include <fstream>
#include <sstream>

namespace cosa {

// when construct, use msat 
// so we will not have trouble later
// and msat's sort can be safely removed
// so we can safely destruct the buffers
Smtlib2Parser::Smtlib2Parser(
  smt::SmtSolver & solver,
  const std::unordered_map<std::string, smt::Term>& symbol_table) : 
    symbol_table_(symbol_table),
    parser_wrapper(new smtlib2_abstract_parser()),
    solver_(solver)
{
  if (!parser_wrapper)
    throw CosaException("Memory allocation failed");

  smtlib2_abstract_parser_init(parser_wrapper, (void *)this);

  parser_wrapper->print_success_ = false;
  
  smtlib2_parser_interface* pi;
  smtlib2_term_parser* tp;

  // parser_wrapper->smtlib2_parser = this;
  /* initialize the term parser and override virtual methods */
  pi = &(parser_wrapper->parent_);
  // pi->set_logic = smtlib2_yices_parser_set_logic;
  // pi->declare_sort = smtlib2_yices_parser_declare_sort;
  // pi->declare_function = smtlib2_yices_parser_declare_function;
  // pi->define_function = smtlib2_yices_parser_define_function;
  // pi->push = smtlib2_yices_parser_push;
  // pi->pop = smtlib2_yices_parser_pop;
  // pi->assert_formula = smtlib2_yices_parser_assert_formula;
  // pi->check_sat = smtlib2_yices_parser_check_sat;
  // pi->annotate_term = smtlib2_yices_parser_annotate_term;
  // pi->set_int_option = smtlib2_yices_parser_set_int_option;
  // pi->get_unsat_core = smtlib2_yices_parser_get_unsat_core;
  // pi->get_assignment = smtlib2_yices_parser_get_assignment;
  // pi->get_value = smtlib2_yices_parser_get_value;
  // pi->make_sort = smtlib2_yices_parser_make_sort;
  // pi->make_function_sort = smtlib2_yices_parser_make_function_sort;
  // pi->make_parametric_sort = smtlib2_yices_parser_make_parametric_sort;
  // pi->define_sort = smtlib2_yices_parser_define_sort;
  // ---------------------------------------------------------
  // pi->push_let_scope = ; pop_let_scope; push_quantifier_scope;
  // pop_quantifier_scope smtlib2_term_parser_push_let_scope // handles
  // automatically smtlib2_term_parser_pop_let_scope // handles automatically
  // smtlib2_abstract_parser_push_quantifier_scope : do nothing
  // smtlib2_abstract_parser_pop_quantifier_scope : do nothing
  //
  // forall (A ())  make_sort -- declare_variable  -- push_quantifier_scope
  //
  //

  pi->assert_formula = proxy_assert_formula;
  pi->define_function = proxy_define_func;
  pi->make_forall_term = proxy_make_forall_term;
  pi->make_exists_term = proxy_make_exists_term;
  pi->push_quantifier_scope = proxy_push_quantifier_scope;
  pi->pop_quantifier_scope = proxy_pop_quantifier_scope;
  pi->make_sort = proxy_make_sort;
  pi->make_parametric_sort = proxy_make_parametric_sort;
  pi->declare_variable = proxy_declare_variable;
  pi->declare_function = proxy_declare_function;
  pi->check_sat = proxy_check_sat;

  tp = parser_wrapper->termparser_; // internal allocated already


  // call back function to apply an uninterpreted function
  // fall through case for handler (operator)
  smtlib2_term_parser_set_function_handler(tp, proxy_mk_function);
  smtlib2_term_parser_set_number_handler(tp, proxy_mk_number);

  smtlib2_term_parser_set_handler(tp, "and" , smt_mk_and); // you need to carry something ...
  smtlib2_term_parser_set_handler(tp, "or"  , smt_mk_or);
  smtlib2_term_parser_set_handler(tp, "not" , smt_mk_not);
  smtlib2_term_parser_set_handler(tp, "=>"  , smt_mk_implies);
  smtlib2_term_parser_set_handler(tp, "="   , smt_mk_eq);
  smtlib2_term_parser_set_handler(tp, "ite" , smt_mk_ite);
  smtlib2_term_parser_set_handler(tp, "xor" , smt_mk_xor);
  smtlib2_term_parser_set_handler(tp, "nand", smt_mk_nand);
  // should we do this?
  smtlib2_term_parser_set_handler(tp, "true",  smt_mk_true);
  smtlib2_term_parser_set_handler(tp, "false", smt_mk_false);

  smtlib2_term_parser_set_handler(tp, "concat", smt_mk_concat);
  smtlib2_term_parser_set_handler(tp, "bvnot" , smt_mk_bvnot);
  smtlib2_term_parser_set_handler(tp, "bvand" , smt_mk_bvand);
  smtlib2_term_parser_set_handler(tp, "bvnand", smt_mk_bvnand);
  smtlib2_term_parser_set_handler(tp, "bvor"  , smt_mk_bvor);
  smtlib2_term_parser_set_handler(tp, "bvnor" , smt_mk_bvnor);
  smtlib2_term_parser_set_handler(tp, "bvxor" , smt_mk_bvxor);
  smtlib2_term_parser_set_handler(tp, "bvxnor", smt_mk_bvxnor);
  smtlib2_term_parser_set_handler(tp, "bvult" , smt_mk_bvult);
  smtlib2_term_parser_set_handler(tp, "bvslt" , smt_mk_bvslt);
  smtlib2_term_parser_set_handler(tp, "bvule" , smt_mk_bvule);
  smtlib2_term_parser_set_handler(tp, "bvsle" , smt_mk_bvsle);
  smtlib2_term_parser_set_handler(tp, "bvugt" , smt_mk_bvugt);
  smtlib2_term_parser_set_handler(tp, "bvsgt" , smt_mk_bvsgt);
  smtlib2_term_parser_set_handler(tp, "bvuge" , smt_mk_bvuge);
  smtlib2_term_parser_set_handler(tp, "bvsge" , smt_mk_bvsge);
  smtlib2_term_parser_set_handler(tp, "bvcomp", smt_mk_bvcomp);
  smtlib2_term_parser_set_handler(tp, "bvneg" , smt_mk_bvneg);
  smtlib2_term_parser_set_handler(tp, "bvadd" , smt_mk_bvadd);
  smtlib2_term_parser_set_handler(tp, "bvsub" , smt_mk_bvsub);
  smtlib2_term_parser_set_handler(tp, "bvmul" , smt_mk_bvmul);
  smtlib2_term_parser_set_handler(tp, "bvudiv", smt_mk_bvudiv);
  smtlib2_term_parser_set_handler(tp, "bvsdiv", smt_mk_bvsdiv);
  smtlib2_term_parser_set_handler(tp, "bvsmod", smt_mk_bvsmod);
  smtlib2_term_parser_set_handler(tp, "bvurem", smt_mk_bvurem);
  smtlib2_term_parser_set_handler(tp, "bvsrem", smt_mk_bvsrem);
  smtlib2_term_parser_set_handler(tp, "bvshl" , smt_mk_bvshl);
  smtlib2_term_parser_set_handler(tp, "bvlshr", smt_mk_bvlshr);
  smtlib2_term_parser_set_handler(tp, "bvashr", smt_mk_bvashr);
  smtlib2_term_parser_set_handler(tp, "extract"    , smt_mk_extract);
  smtlib2_term_parser_set_handler(tp, "bit2bool"   , smt_mk_bit2bool);
  smtlib2_term_parser_set_handler(tp, "repeat"     , smt_mk_repeat);
  smtlib2_term_parser_set_handler(tp, "zero_extend", smt_mk_zero_extend);
  smtlib2_term_parser_set_handler(tp, "sign_extend", smt_mk_sign_extend);
  smtlib2_term_parser_set_handler(tp, "rotate_left", smt_mk_rotate_left);
  smtlib2_term_parser_set_handler(tp, "rotate_right",smt_mk_rotate_right);


  term_allocation_table.push_back(nullptr);
} // 

Smtlib2Parser::~Smtlib2Parser() {
  if (parser_wrapper) {
    smtlib2_abstract_parser_deinit(parser_wrapper);
    delete parser_wrapper;
  }
}

Smtlib2Parser::SortPtrT Smtlib2Parser::make_bv_sort(uint64_t w) {
  std::string sortIdxName = "BV" + std::to_string(w);
  auto bv_pos = sort_table.find(sortIdxName);
  if (bv_pos == sort_table.end()) {
    sort_names.push_back(sortIdxName);
    size_t ptr = sort_names.size()-1;
    sort_table.insert(std::make_pair(sortIdxName, 
      std::make_pair(solver_->make_sort(smt::BV, w), ptr)));
    return ptr;      
  }
  return (bv_pos->second.second);
}

Smtlib2Parser::SortPtrT Smtlib2Parser::make_sort(const std::string& name, const std::vector<int>& idx) {
  if (name == "Bool") {
    auto bool_pos = sort_table.find("Bool");
    if (bool_pos == sort_table.end()) {
      sort_names.push_back("Bool");
      size_t ptr = sort_names.size()-1;
      sort_table.insert(std::make_pair("Bool", 
        std::make_pair(solver_->make_sort(smt::BOOL),ptr)));
      return ptr;
    } else 
      return (bool_pos->second.second);
  } else if (name == "BitVec") {
    assert (idx.size() == 1);
    assert (idx[0] > 0);
    return make_bv_sort(idx[0]);
  }
  throw CosaException("Sort : " + name + " is unknown");
  return 0;
}


Smtlib2Parser::SortPtrT Smtlib2Parser::make_parametric_sort(const std::string& name, const std::vector<SortPtrT>& tpargs) {
  if (name == "Array") {
    if (tpargs.size() == 2) {
      auto sort1 = get_sort(tpargs[0]);
      auto sort2 = get_sort(tpargs[1]);
      if (sort1->get_sort_kind() != smt::BOOL && 
          sort1->get_sort_kind() != smt::BV) {
          throw CosaException("Parametric Array has wrong parameter type");
          return 0;
      }
      if (sort2->get_sort_kind() != smt::BOOL && 
          sort2->get_sort_kind() != smt::BV) {
          throw CosaException("Parametric Array has wrong parameter type");
          return 0;
      }
      auto sort_name("A" + sort1->to_string()+" -> " + sort2->to_string());
      auto sort_pos = sort_table.find(sort_name);
      if (sort_pos == sort_table.end()) {
        sort_names.push_back(sort_name);
        size_t ptr = sort_names.size()-1;
        sort_table.insert(std::make_pair(sort_name, 
          std::make_pair(solver_->make_sort(smt::ARRAY, sort1, sort2),ptr)));
        return ptr;
      } else 
        return (sort_pos->second.second);
    } else {
      throw CosaException("Parametric Array has wrong parameters");
      return 0;
    }
  }
  throw CosaException("Parametric Sort : " + name + " is unknown");
  return 0;
} // make_parametric_sort

smt::Sort Smtlib2Parser::get_sort(SortPtrT sortptr) {
  assert (sortptr < sort_names.size());
  const auto & sort_name = sort_names.at(sortptr);
  auto sort_pos = sort_table.find(sort_name);
  assert (sort_pos != sort_table.end());
  assert (sort_pos->second.second == sortptr);
  return sort_pos->second.first;
}

smt::Term Smtlib2Parser::get_term(TermPtrT termptr) {
  assert (termptr < term_allocation_table.size());
  return term_allocation_table.at(termptr);
}

void Smtlib2Parser::declare_quantified_variable(const std::string& name, SortPtrT sort) {
  assert (!quantifier_def_stack.empty());
  
  // TermPtrT local_def = search_quantified_var_stack(name);
  // we expect we are not using the same name
  // assert (local_def == term_allocation_table.size()); 
  smt::Term t = search_symbol_table(name);

  if (t) {
    assert(t->get_sort() == get_sort(sort));
  } else {
    t = solver_->make_symbol(name, get_sort(sort));
    logger.log(1, "New var " + name + " outside symbol table is defined.");
  }
  // now insert it to the local table

  term_allocation_table.push_back(t);
  quantifier_def_stack.back().insert(std::make_pair(name, term_allocation_table.size()-1));

  // we should not define new vars
  // auto var = solver_->make_symbol(name, *sort);
  // quantifier_def_stack.back().insert(std::make_pair(name, var));
}

void * Smtlib2Parser::push_quantifier_scope() {
  quantifier_def_stack.push_back(symbol_pointer_table_t());
  //throw CosaException("forall/exists not supported.");
  return NULL;
}

void * Smtlib2Parser::pop_quantifier_scope() {
  quantifier_def_stack.pop_back();
  // throw CosaException("forall/exists not supported.");
  return NULL;
}

smt::Term Smtlib2Parser::search_symbol_table(const std::string& name) const {
  // de-sanitize
  std::string name_no_bar = 
    name.length() > 2 && name.front() == '|' && name.back() == '|' ?
    name.substr(1,name.length()-2) : name;
  auto term_pos = symbol_table_.find(name_no_bar);
  if (term_pos != symbol_table_.end())
    return (term_pos->second);
  return NULL;
}

Smtlib2Parser::TermPtrT Smtlib2Parser::search_quantified_var_stack(const std::string& name) const {
  for (auto mp_pos = quantifier_def_stack.rbegin();
       mp_pos != quantifier_def_stack.rend();
       ++mp_pos) { // search from the closest binding
    const symbol_pointer_table_t & symbols = *mp_pos;
    auto term_pos = symbols.find(name);
    if (term_pos != symbols.end())
      return term_pos->second;
  }
  return term_allocation_table.size();
}

Smtlib2Parser::TermPtrT Smtlib2Parser::make_function(const std::string& name, SortPtrT sort,
  const std::vector<int>& idx, const std::vector<TermPtrT>& args ) {
  
  if (args.empty() && idx.empty()) {
    TermPtrT varptr = search_quantified_var_stack(name);
    if (varptr != term_allocation_table.size())
      return varptr;
    throw CosaException("variable : " + name + " is unknown");
    return 0;
  }
  throw CosaException("Function : " + name + " is undefined");
  return 0;
}

Smtlib2Parser::TermPtrT Smtlib2Parser::make_number(const std::string& rep, int width, int base) {
  // it is definitely a bitvector
  SortPtrT sort = make_bv_sort(width);
  assert (sort != sort_names.size());
  term_allocation_table.push_back(solver_->make_term(rep, get_sort(sort), (uint64_t)base));
  return term_allocation_table.size()-1;
}

/// this function receives the final assert result
void Smtlib2Parser::assert_formula(TermPtrT term) {
  throw CosaException("(assert ...) is not implemented");
}

/// this function receives the final result
void Smtlib2Parser::define_function(const std::string& func_name,
                      const std::vector<TermPtrT> & args,
                      SortPtrT ret_type, TermPtrT func_body) {
  // this should be the place we get
  assert(func_name == "INV");
  assert(get_sort(ret_type)->get_sort_kind() == smt::BOOL); // bool functions
  parse_result_term = func_body;
}

// if unsat --> add the (assert ...)
smt::Term Smtlib2Parser::ParseSmtFromFile(const std::string& fname) {
  FILE * fp = fopen(fname.c_str(),"r");
  if (fp == NULL)
    return NULL;


  smtlib2_abstract_parser_parse(parser_wrapper, fp);

  if (parser_wrapper->errmsg_)
    error_msg_ =  parser_wrapper->errmsg_;
  if (parse_result_term >= term_allocation_table.size() )
    return NULL;

  return (get_term(parse_result_term));
}

// parse from a string: assume we have the (assert ...) there
smt::Term Smtlib2Parser::ParseSmtFromString(const std::string& text) {
  auto len = text.size() + 1;
  char* buffer = new char[len];
  strncpy(buffer, text.c_str(), len);
  buffer[len - 1] = '\0'; // to make static analysis happy

  smtlib2_abstract_parser_parse_string(parser_wrapper, buffer);

  delete[] buffer;

  if (parser_wrapper->errmsg_)
    error_msg_ =  parser_wrapper->errmsg_;
  if (parse_result_term >= term_allocation_table.size() )
    return NULL;

  return (get_term(parse_result_term));
}


#define DEFINE_OPERATOR(name)                                                  \
  Smtlib2Parser::TermPtrT Smtlib2Parser::mk_##name(                          \
      const std::string& symbol, SortPtrT sort, const std::vector<int>& idx,  \
      const std::vector<TermPtrT>& args)

#define SORT(x)   ( (get_term(x))->get_sort() )
#define ISBOOL(x) (true)
#define ISBV(x)   (true)
//#define ISBOOL(x) ( SORT(x)->get_sort_kind() == smt::BOOL )
//#define ISBV(x)   ( SORT(x)->get_sort_kind() == smt::BV )

#define CHECK_EMPTY_PARAM(idx, args)                                       \
  assert((idx).empty());                                                   \
  assert((args).empty())

#define CHECK_BV_MULTI_ARG(idx, args)                                      \
  assert((idx).empty());                                                   \
  assert((args).size() >= 2)

#define CHECK_BOOL_MULTI_ARG(idx, args) CHECK_BV_MULTI_ARG(idx, args)

#define CHECK_BOOL_ONE_ARG(idx, args)                                      \
  assert(idx.empty());                                                     \
  assert(args.size() == 1);                                                \
  assert(ISBOOL(args[0]))

#define CHECK_BOOL_TWO_ARG(idx, args)                                      \
  assert((idx).empty());                                                   \
  assert((args).size() == 2);                                              \
  assert(ISBOOL(args[0]));                                                 \
  assert(ISBOOL(args[1]))


#define CHECK_BV_TWO_ARG(idx, args)                                        \
  assert((idx).empty());                                                   \
  assert((args).size() == 2);                                              \
  assert(ISBV(args[0]));            \
  assert(SORT(args[0]) == SORT(args[1]) )         

#define CHECK_BV_COMPARE(idx, args) CHECK_BV_TWO_ARG(idx, args)
          
#define CHECK_BV_ONE_ARG(idx, args)                                        \
  assert(idx.empty());                                                     \
  assert(args.size() == 1);                                                \
  assert(ISBV(args[0]))     

#define CHECK_BV_TWO_ARG_DIFF_WIDTH(idx, args)                             \
  assert((idx).empty());                                                   \
  assert((args).size() == 2);                                              \
  assert(ISBV(args[0]));                                                   \
  assert(ISBV(args[1]));                      

#define MAKE_RESULT(x) do {  term_allocation_table.push_back(x) ;  return (term_allocation_table.size()-1); } while(0)

DEFINE_OPERATOR(true) {
  CHECK_EMPTY_PARAM(idx, args);
  MAKE_RESULT(solver_->make_term(true));
}

DEFINE_OPERATOR(false) {
  CHECK_EMPTY_PARAM(idx, args);
  MAKE_RESULT(solver_->make_term(false));
}

DEFINE_OPERATOR(and) {
  CHECK_BOOL_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  
  for(auto termptr : args) {
    assert (ISBOOL(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::And, argterm));
}

DEFINE_OPERATOR(or) {
  CHECK_BOOL_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBOOL(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::Or, argterm));
}

DEFINE_OPERATOR(not) {
  CHECK_BOOL_ONE_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::Not, get_term(args[0]) ));
}

DEFINE_OPERATOR(implies) {
  CHECK_BOOL_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::Implies, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(eq) {
  assert(idx.empty());
  assert(args.size() == 2); // we don't require they are bv
  assert(SORT(args[0]) == SORT(args[1]));
  
  MAKE_RESULT(solver_->make_term(smt::Equal, get_term (args[0]) , get_term (args[1]) ));
}

DEFINE_OPERATOR(ite)  {
  assert(idx.empty());
  assert(args.size() == 3);
  assert(ISBOOL(args[0]));
  assert(SORT(args[1]) == SORT(args[2]));

  MAKE_RESULT(solver_->make_term(smt::Ite, get_term (args[0]) , get_term (args[1]), get_term (args[2]) ));
}

DEFINE_OPERATOR(xor) {
  CHECK_BOOL_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::Xor, get_term (args[0]) , get_term (args[1]) ));
}

DEFINE_OPERATOR(nand) {
  CHECK_BOOL_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBOOL(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::Not, solver_->make_term(smt::And, argterm)));
}

DEFINE_OPERATOR(concat) {
  assert(idx.empty());
  assert(args.size() >= 2);

  assert(ISBV(args[0]));
  smt::Term prev = get_term(args[0]);
  for (auto pos = args.begin()+1; pos != args.end(); ++pos) {
    assert(ISBV(*pos));
    prev = solver_->make_term(smt::Concat, prev, get_term(*pos));
  }
  MAKE_RESULT(prev);
}

DEFINE_OPERATOR(bvnot) {
  CHECK_BV_ONE_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVNot, get_term(args[0])));
}
DEFINE_OPERATOR(bvneg) {
  CHECK_BV_ONE_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVNeg, get_term(args[0])));
}

DEFINE_OPERATOR(bvand) {
  CHECK_BV_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBV(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::BVAnd, argterm));
}

DEFINE_OPERATOR(bvnand) {
  CHECK_BV_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBV(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::BVNand, argterm));
}

DEFINE_OPERATOR(bvor) {
  CHECK_BV_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBV(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::BVOr, argterm));
}

DEFINE_OPERATOR(bvnor) {
  CHECK_BV_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBV(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::BVNor, argterm));
}

DEFINE_OPERATOR(bvxor) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVXor, get_term (args[0]) , get_term (args[1]) ));
}

DEFINE_OPERATOR(bvxnor) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVXnor, get_term (args[0]) , get_term (args[1]) ));
}

DEFINE_OPERATOR(bvult) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVUlt, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvslt) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSlt,get_term(args[0]) , get_term(args[1]) ));
}


DEFINE_OPERATOR(bvule) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVUle, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvsle) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSle, get_term(args[0]) , get_term(args[1]) ));
}


DEFINE_OPERATOR(bvugt) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVUgt, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvsgt) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSgt, get_term(args[0]) , get_term(args[1]) ));
}


DEFINE_OPERATOR(bvuge) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVUge, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvsge) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSge, get_term(args[0]) , get_term(args[1]) ));
}


DEFINE_OPERATOR(bvcomp) {
  CHECK_BV_COMPARE(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVComp, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvadd) {
  CHECK_BV_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBV(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::BVAdd, argterm));
}

DEFINE_OPERATOR(bvmul) {
  CHECK_BV_MULTI_ARG(idx, args);
  smt::TermVec argterm;
  for(auto termptr : args) {
    assert (ISBV(termptr));
    argterm.push_back(get_term(termptr));
  }
  MAKE_RESULT(solver_->make_term(smt::BVMul, argterm));
}

DEFINE_OPERATOR(bvsub) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSub, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvudiv) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVUdiv, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvsdiv) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSdiv, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvsmod) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSmod, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvurem) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVUrem, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvsrem) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVSrem, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvshl) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVShl, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvlshr) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVLshr, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(bvashr) {
  CHECK_BV_TWO_ARG(idx, args);
  MAKE_RESULT(solver_->make_term(smt::BVAshr, get_term(args[0]) , get_term(args[1]) ));
}

DEFINE_OPERATOR(extract) {
  assert(idx.size() == 2);
  assert(args.size() == 1);
  assert(ISBV(args[0]));  
  assert(idx[0] >= 0 && idx[1] >= 0);

  auto width = SORT(args[0])->get_width();
  uint64_t left = idx[0], right = idx[1];
  assert (left < width);
  assert (right < width);

  MAKE_RESULT(solver_->make_term(smt::Op(smt::Extract,left, right), get_term(args[0])  ));
}

DEFINE_OPERATOR(bit2bool)  {
  assert(idx.size() == 1);
  assert(args.size() == 1);
  assert(ISBV(args[0]));  
  assert(idx[0] >= 0);
  auto width = SORT(args[0])->get_width();
  uint64_t sel = idx[0];
  assert (sel < width);
  MAKE_RESULT(solver_->make_term(smt::Op(smt::Extract, sel, sel), get_term(args[0])  ));
}

DEFINE_OPERATOR(repeat) {
  assert(idx.size() == 1);
  assert(args.size() == 1);
  assert(ISBV(args[0]));  
  assert(idx[0] >= 0);

  MAKE_RESULT(solver_->make_term(smt::Op(smt::Repeat, idx[0]), get_term(args[0])  ));
}


DEFINE_OPERATOR(zero_extend) {
  assert(idx.size() == 1);
  assert(args.size() == 1);
  assert(ISBV(args[0]));  
  assert(idx[0] >= 0);

  MAKE_RESULT(solver_->make_term(smt::Op(smt::Zero_Extend, idx[0]), get_term(args[0])  ));
}

DEFINE_OPERATOR(sign_extend) {
  assert(idx.size() == 1);
  assert(args.size() == 1);
  assert(ISBV(args[0]));  
  assert(idx[0] >= 0);

  MAKE_RESULT(solver_->make_term(smt::Op(smt::Sign_Extend, idx[0]), get_term(args[0])  ));
}

DEFINE_OPERATOR(rotate_left) {
  assert(idx.size() == 1);
  assert(args.size() == 1);
  assert(ISBV(args[0]));  
  assert(idx[0] >= 0);

  MAKE_RESULT(solver_->make_term(smt::Op(smt::Rotate_Left, idx[0]), get_term(args[0])  ));
}

DEFINE_OPERATOR(rotate_right) {
  assert(idx.size() == 1);
  assert(args.size() == 1);
  assert(ISBV(args[0]));  
  assert(idx[0] >= 0);

  MAKE_RESULT(solver_->make_term(smt::Op(smt::Rotate_Right, idx[0]), get_term(args[0])  ));
}

#undef DEFINE_OPERATOR



} // namespace cosa
