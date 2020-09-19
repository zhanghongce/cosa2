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
 ** \brief To BTOR to CHC
 **
 **
 **/

#include "chc_printer.h"
#include "utils/str_util.h"
#include "engines/sygus/ast_knob/syntax.h"

namespace cosa {

/*

(define-fun INIT (() () () ()) )

*/


static std::string body_paranthesis_auto(const std::string & in) {
  std::string body(in);
  sygus::StrTrim(body);
  if (! ( body.front() == '(' && body.back() == ')' ) )
    body = "(" + body + ")";
  return body;
}

/*

  std::string var_type_; // (type1 type2 type3 ...)

  std::string var_use_; // n1 n2 n3 ...
  std::string var_prime_use_; // n1' n2' n3'

  std::string primal_declare_;       // ((name type) (name type))
  std::string primal_prime_declare_; // ((name type) (name type) and prime variables)

*/

ChcPrinter::ChcPrinter (const Property & p):
  ts_(p.transition_system()), property_(p),
  states_(ts_.states()), next_states_(ts_.next_states()), inputs_(ts_.inputs()), next_inputs_(ts_.next_inputs())
{
  std::vector<std::string> var_type_list;

  std::vector<std::string> var_use_list;
  std::vector<std::string> var_prime_use_list;

  std::vector<std::string> primal_declare_list;
  std::vector<std::string> prime_declare_list;

  for (const auto &s : states_) {
    auto name = sygus::name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    primal_declare_list.push_back("("+name + " " + sort+")");
    var_use_list.push_back(name);
    var_type_list.push_back(sort);

    auto name_next = sygus::name_sanitize(ts_.next(s)->to_string());
    prime_declare_list.push_back("("+name_next + " " + sort+")");
    var_prime_use_list.push_back(name_next);
  }
  for (const auto &s : inputs_) {
    auto name = sygus::name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    primal_declare_list.push_back("("+name + " " + sort+")");
    var_use_list.push_back(name);
    var_type_list.push_back(sort);

    auto name_next = sygus::name_sanitize(ts_.next(s)->to_string());
    prime_declare_list.push_back("("+name_next + " " + sort+")");
    var_prime_use_list.push_back(name_next);
  }

  var_type_ = "("+sygus::Join(var_type_list, " ")+")";
  var_use_ = sygus::Join(var_use_list, " ");
  var_prime_use_ = sygus::Join(var_prime_use_list, " ");
  primal_declare_ = "("+sygus::Join(primal_declare_list, " ") + ")";
  primal_prime_declare_ = "("+sygus::Join(primal_declare_list, " ") + " " + sygus::Join(prime_declare_list, " ") + ")";
  

} // ChcPrinter::ChcPrinter



/*
%INIT%
%TRANS%
%P%

%S%
%SP%
%I% (IP)

%INVvartype%
%INVvaruseprime%

%INITvaruse%
%Tvaruse%
%Pvaruse%
*/

static std::string syntax_constraints_template = R"**(

(set-logic HORN)
(declare-fun INV %vartype% Bool)

(assert (forall %allvardecl% (=> %init% (INV %varuse%))))

(assert (forall %allvardecl% (=> (and (INV %varuse%) %trans%) (INV %varuseprime%))))

(assert (forall %allvardecl% (=> (and (INV %varuse%) (not %prop%)) false)))

(check-sat)
)**";

void ChcPrinter::Export(std::ostream & os) const {
  
  auto trans_ = body_paranthesis_auto(ts_.trans()->to_string());
  auto init_ = body_paranthesis_auto(ts_.init()->to_string());
  auto prop_ = body_paranthesis_auto(property_.prop()->to_string());

  os << 
    sygus::ReplaceAll(sygus::ReplaceAll(
    sygus::ReplaceAll(sygus::ReplaceAll(
    sygus::ReplaceAll(sygus::ReplaceAll(
    sygus::ReplaceAll(sygus::ReplaceAll(
      syntax_constraints_template, 
      "%vartype%", var_type_),
      "%primalvardecl%", primal_declare_), // not used 
      "%allvardecl%", primal_prime_declare_),
      "%init%", init_),
      "%trans%", trans_),
      "%prop%", prop_),
      "%varuse%", var_use_),
      "%varuseprime%", var_prime_use_);

} // ChcPrinter::Export

} // namespace cosa
