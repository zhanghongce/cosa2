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


ChcPrinter::ChcPrinter (const Property & p):
  ts_(p.transition_system()), property_(p),
  states_(ts_.states()), next_states_(ts_.next_states()), inputs_(ts_.inputs()), next_inputs_(ts_.next_inputs())
{
  std::vector<std::string> arg_lists_init_;
  std::vector<std::string> arg_lists_trans_;
  std::vector<std::string> arg_lists_call_init_;
  std::vector<std::string> arg_lists_call_trans_;
  std::vector<std::string> arg_inv_type_;
  std::vector<std::string> arg_inv_prime_use_;

  for (const auto &s : states_) {
    auto name = sygus::name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    primal_var_def_ += "(declare-var " + name + " " + sort + ")\n";
    arg_lists_init_.push_back("("+name + " " + sort+")");
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_init_.push_back(name);
    arg_lists_call_trans_.push_back(name);
    arg_inv_type_.push_back(sort);

    auto name_next = sygus::name_sanitize(ts_.next(s)->to_string());
    arg_inv_prime_use_.push_back(name_next);
    state_to_next_map_.emplace(name, name_next);
  }
  for (const auto &s : inputs_) {
    auto name = sygus::name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    input_var_def_ += "(declare-var " + name + " " + sort + ")\n";
    arg_lists_init_.push_back("("+name + " " + sort+")");
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_init_.push_back(name);
    arg_lists_call_trans_.push_back(name);

    arg_inv_type_.push_back(sort);

    auto name_next = sygus::name_sanitize(ts_.next(s)->to_string());
    arg_inv_prime_use_.push_back(name_next);
    state_to_next_map_.emplace(name, name_next);
  }

  for (const auto &s : next_states_) {
    auto name = sygus::name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    prime_var_def_ += "(declare-var " + name + " " + sort + ")\n";
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_trans_.push_back(name);
  }

  for (const auto &s : next_inputs_) {
    auto name = sygus::name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    input_var_def_ += "(declare-var " + name + " " + sort + ")\n";
    //arg_lists_init_.push_back("("+name + " " + sort+")");
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    //arg_lists_call_init_.push_back(name);
    arg_lists_call_trans_.push_back(name);
  }

  trans_def_ = "(define-fun Trans \n    (" + sygus::Join(arg_lists_trans_, " ") +")\n    Bool\n     "
    + body_paranthesis_auto(ts_.trans()->to_string()) + ")";
  trans_use_ = "(Trans " + sygus::Join(arg_lists_call_trans_, " ") + ")";

  // (define-fun Fprev (state_arg_def_) Bool (...))
  // (Fprev )
  state_arg_def_ = sygus::Join(arg_lists_init_, " ");
  state_arg_use_ = sygus::Join(arg_lists_call_init_, " ");

  init_def_ = "(define-fun Init \n    (" + state_arg_def_ +")\n     Bool\n     "
    + body_paranthesis_auto(ts_.init()->to_string()) + ")";
  init_use_ = "(Init " + state_arg_use_ + ")";

  property_def_ = "(define-fun P \n   (" + state_arg_def_ + ")\n    Bool\n     "
    +  body_paranthesis_auto(property_.prop()->to_string()) + ")";
  property_use_ = "(P " + state_arg_use_ + ")";

  inv_var_type_ =  "(" + sygus::Join(arg_inv_type_, " ") + ")";
  inv_var_prime_use_ = sygus::Join(arg_inv_prime_use_, " ");

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

;----------------------------------------
;  CHC generated from BTOR
;  Generated by COSA2 (Pono)
;----------------------------------------

(set-option :fp.engine spacer)

%INIT%
%TRANS%
%P%

%S%
%SP%
%I%

(declare-rel INV %INVvartype%)
(declare-rel fail ())

(rule (=> 
  %inituse%
  (INV  %INVvaruse%)))

(rule (=> (and
  (INV  %INVvaruse%)
  %tuse%)
  (INV  %INVvaruseprime%)))

(rule (=> (and
  (INV %INVvaruse%) 
  (not %Puse%))
  fail))

(query fail :print-certificate true)

)**";

void ChcPrinter::Export(std::ostream & os) const {

  os << 
    sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(
    sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(sygus::ReplaceAll(
      syntax_constraints_template, 

      "%INIT%"           , init_def_          ) ,
      "%TRANS%"          , trans_def_         ) ,
      "%P%"              , property_def_      ) ,
      "%S%"              , primal_var_def_    ) ,
      "%SP%"             , prime_var_def_     ) ,
      "%I%"              , input_var_def_     ) ,
      "%INVvartype%"     , inv_var_type_      ) ,
      "%INVvaruse%"      , state_arg_use_     ) ,
      "%INVvaruseprime%" , inv_var_prime_use_ ) ,
      "%inituse%"        , init_use_          ) ,
      "%tuse%"           , trans_use_         ) ,
      "%Puse%"           , property_use_      ) ;

} // ChcPrinter::Export

} // namespace cosa