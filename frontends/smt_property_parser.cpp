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
 
#include "smt_property_parser.h"


#include "utils/exceptions.h"
#include "utils/logger.h"

namespace cosa {

Smtlib2PropertyParser::Smtlib2PropertyParser(
  smt::SmtSolver & solver,
  TransitionSystem & ts) : 
    Smtlib2Parser(solver, ts.symbols()), ts_(ts) {
}

// do nothing
Smtlib2PropertyParser::~Smtlib2PropertyParser() {  } 

bool Smtlib2PropertyParser::ParsePropertyFromFile(const std::string& fname) {
  logger.log(2, "Parsing smt-lib2 property file: " + fname);

  FILE * fp = fopen(fname.c_str(),"r");
  if (fp == NULL)
    return false;
  
  smtlib2_abstract_parser_parse(parser_wrapper, fp);

  if (parser_wrapper->errmsg_) {
    error_msg_ =  parser_wrapper->errmsg_;
    return false;
  }
  return true;
}

void Smtlib2PropertyParser::define_function(const std::string& func_name,
                   const std::vector<TermPtrT> & args,
                   SortPtrT ret_type, TermPtrT func_body) {
                   
  if (func_name.find("assumption") == 0) {
    // this is an assumption add to ts's constraint
    ts_.add_constraint(get_term(func_body));
  } else if (func_name.find("assertion") == 0) {
    // add to prop_vec
    propvec_.push_back(get_term(func_body));
  } else { // add to term table so we can reference it
    ArgListT arglist;
    for (auto termptr : args)
      arglist.push_back(get_term(termptr));
    
    func_def_table_.emplace(func_name, 
      std::make_pair(arglist, get_term(func_body)));
  }
}

Smtlib2PropertyParser::TermPtrT Smtlib2PropertyParser::make_function(const std::string& name, SortPtrT sort,
  const std::vector<int>& idx, const std::vector<TermPtrT>& args ) {
  
  if (args.empty() && idx.empty()) {
    TermPtrT varptr = search_quantified_var_stack(name);
    if (varptr != term_allocation_table.size())
      return varptr;
  }
  auto func_def_pos = func_def_table_.find(name);
  if (func_def_pos != func_def_table_.end()) {

    ArgListT arglist;
    for (auto termptr : args)
      arglist.push_back(get_term(termptr));

    auto ret_term = func_def_pos->second.second;
    const ArgListT & func_args = func_def_pos->second.first;
    // check sort matching
    if (func_args.size() != arglist.size())
      throw CosaException("Function : " + name + " is used without correct argument.");
    smt::UnorderedTermMap arg_map;
    for (auto arg_pos = func_args.begin(); arg_pos != func_args.end(); ++ arg_pos) {
      const auto & arg_new = arglist.at(arg_pos - func_args.begin());
      if ( (*arg_pos)->get_sort() != arg_new->get_sort() )
        throw CosaException("Function : " + name + " is used without correct argument.");
      arg_map.emplace(*arg_pos, arg_new);
    }
    auto term_after_subst = solver_->substitute(ret_term, arg_map);
    term_allocation_table.push_back(term_after_subst);
    return term_allocation_table.size() -1 ;
  }
  // 
  throw CosaException("Function/Variable : " + name + " is undefined");
  return 0;
}

void * Smtlib2PropertyParser::push_quantifier_scope() {
  return Smtlib2Parser::push_quantifier_scope();
}
void * Smtlib2PropertyParser::pop_quantifier_scope() {
  return Smtlib2Parser::pop_quantifier_scope();
}
  
 
} // namespace cosa
