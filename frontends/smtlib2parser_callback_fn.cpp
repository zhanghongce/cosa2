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
 ** \brief SMT-LIB2 callback functions
 **
 ** 
 **/
 
#include "smtlib2parser_callback_fn.h"
#include "smtlib2parser.h"

#include "utils/exceptions.h"

#include <vector>

namespace cosa {

typedef Smtlib2Parser::TermPtrT TermPtrT;
typedef Smtlib2Parser::SortPtrT SortPtrT;

// make vector
template <class T> std::vector<T> make_vector(smtlib2_vector* iv) {
  std::vector<T> ret;
  if (!iv)
    return ret;

  auto l = SMTLIB2_VECTOR_SIZE(iv);
  intptr_t* ptr = SMTLIB2_VECTOR_ARRAY(iv);
  for (decltype(l) idx = 0; idx < l; ++idx)
    ret.push_back((T)(ptr[idx]));
  return ret;
}

// ------------------ CALL BACK FUNCTIONS ------------- //

#define PARSER(x) ((Smtlib2Parser *)(((smtlib2_abstract_parser*)x)->termparser_->ctx_))

smtlib2_term proxy_push_quantifier_scope(smtlib2_parser_interface* p) {
  return (smtlib2_term)(PARSER(p)->push_quantifier_scope());
}

smtlib2_term proxy_pop_quantifier_scope(smtlib2_parser_interface* p) {
  return (smtlib2_term)(PARSER(p)->pop_quantifier_scope());
}

// we will treat everything as an assert, although it does nothing
void proxy_assert_formula(smtlib2_parser_interface* parser, smtlib2_term term) {
  // here it should be where we get our result
  PARSER(parser)->assert_formula((TermPtrT) term);
}

void proxy_define_func(smtlib2_parser_interface* parser, const char* name,
                       smtlib2_vector* params, smtlib2_sort sort,
                       smtlib2_term term) {

  auto idxv = make_vector<size_t>(params);
  PARSER(parser)->define_function(name, idxv, (SortPtrT) sort, (TermPtrT) term );
  // check the idxv (params) type
}

// the special function dealing with the final term in a forall term
smtlib2_term proxy_make_forall_term(smtlib2_parser_interface* parser,
                                    smtlib2_term term) {
  throw CosaException("forall in smt-lib2 parsing is not supported yet.");
  return term;
}

// the special function dealing with the final term in an exists term
smtlib2_term proxy_make_exists_term(smtlib2_parser_interface* parser,
                                    smtlib2_term term) {
  throw CosaException("exists in smt-lib2 parsing is not supported yet.");
  return term;
}

/*

a_sort :
  SYMBOL
  {
      $$ = parser->make_sort(parser, $1, NULL);
      free($1);
  }
| '(' TK_UNDERSCORE SYMBOL int_list ')'
  {
      $$ = parser->make_sort(parser, $3, $4);
      smtlib2_vector_delete($4);
      free($3);
  }
| '(' SYMBOL sort_list ')'
  {
      $$ = parser->make_parametric_sort(parser, $2, $3);
      smtlib2_vector_delete($3);
      free($2);
  }
;

*/

smtlib2_sort proxy_make_sort(smtlib2_parser_interface* p, const char* sortname,
                             smtlib2_vector* index) {
  auto idxv = make_vector<int>(index);
  smtlib2_sort ret =
      (smtlib2_sort)(PARSER(p)->make_sort(sortname, idxv));
  return ret;
  // free((void *)sortname);
  // if(index)
  //   smtlib2_vector_delete(index);
  // free the content?
}

void proxy_declare_variable(smtlib2_parser_interface* p, const char* name,
                            smtlib2_sort sort) {
  PARSER(p)->declare_quantified_variable(name, (SortPtrT)sort);
  // free((void *)name);
}

void proxy_declare_function(smtlib2_parser_interface* p, const char* name,
                            smtlib2_sort sort) {
  throw CosaException("declare-fun in smt-lib2 parsing is not supported yet.");
}

void proxy_check_sat(smtlib2_parser_interface* p) {
  // do nothing
}

smtlib2_term proxy_mk_function(smtlib2_context ctx, const char* symbol,
                               smtlib2_sort sort, smtlib2_vector* index,
                               smtlib2_vector* args) {
  auto idxv = make_vector<int>(index);
  auto argsv = make_vector<TermPtrT>(args);

  smtlib2_term ret = (smtlib2_term)(
      ((Smtlib2Parser*)ctx)->make_function(symbol, (SortPtrT)sort, idxv, argsv));
  // free(symbol);
  // if(index)
  //   smtlib2_vector_delete(index);
  // if(args)
  //   smtlib2_vector_delete(args);
  return ret;
}

smtlib2_term proxy_mk_number(smtlib2_context ctx, const char* rep,
                             unsigned int width, unsigned int base) {
  smtlib2_term ret =
      (smtlib2_term)( (smtlib2_term)(((Smtlib2Parser*)ctx)->make_number(rep, width, base)));
  // free(rep);
  return ret;
}

// ------------------ OPERATORS ------------- //

#define SMTLIB2_VERILOG_DEFHANDLER(name)                                       \
  smtlib2_term smt_mk_##name(smtlib2_context ctx, const char* symbol,   \
                                    smtlib2_sort sort, smtlib2_vector* idx,    \
                                    smtlib2_vector* args) {                    \
    auto idxv = make_vector<int>(idx);                                         \
    auto argsv = make_vector<TermPtrT>(args);                         \
    smtlib2_term ret = (smtlib2_term)(                                         \
        ((Smtlib2Parser*)ctx)->mk_##name(symbol, (SortPtrT)sort, idxv, argsv));    \
    return ret;                                                                \
  }

// handle the operators
SMTLIB2_VERILOG_DEFHANDLER(true);
SMTLIB2_VERILOG_DEFHANDLER(false);

SMTLIB2_VERILOG_DEFHANDLER(and);
SMTLIB2_VERILOG_DEFHANDLER(or);
SMTLIB2_VERILOG_DEFHANDLER(not);
SMTLIB2_VERILOG_DEFHANDLER(implies);
SMTLIB2_VERILOG_DEFHANDLER(eq);
SMTLIB2_VERILOG_DEFHANDLER(ite);
SMTLIB2_VERILOG_DEFHANDLER (xor);
SMTLIB2_VERILOG_DEFHANDLER(nand);
SMTLIB2_VERILOG_DEFHANDLER(concat);
SMTLIB2_VERILOG_DEFHANDLER(bvnot);
SMTLIB2_VERILOG_DEFHANDLER(bvand);
SMTLIB2_VERILOG_DEFHANDLER(bvnand);
SMTLIB2_VERILOG_DEFHANDLER(bvor);
SMTLIB2_VERILOG_DEFHANDLER(bvnor);
SMTLIB2_VERILOG_DEFHANDLER(bvxor);
SMTLIB2_VERILOG_DEFHANDLER(bvxnor);
SMTLIB2_VERILOG_DEFHANDLER(bvult);
SMTLIB2_VERILOG_DEFHANDLER(bvslt);
SMTLIB2_VERILOG_DEFHANDLER(bvule);
SMTLIB2_VERILOG_DEFHANDLER(bvsle);
SMTLIB2_VERILOG_DEFHANDLER(bvugt);
SMTLIB2_VERILOG_DEFHANDLER(bvsgt);
SMTLIB2_VERILOG_DEFHANDLER(bvuge);
SMTLIB2_VERILOG_DEFHANDLER(bvsge);
SMTLIB2_VERILOG_DEFHANDLER(bvcomp);
SMTLIB2_VERILOG_DEFHANDLER(bvneg);
SMTLIB2_VERILOG_DEFHANDLER(bvadd);
SMTLIB2_VERILOG_DEFHANDLER(bvsub);
SMTLIB2_VERILOG_DEFHANDLER(bvmul);
SMTLIB2_VERILOG_DEFHANDLER(bvudiv);
SMTLIB2_VERILOG_DEFHANDLER(bvsdiv);
SMTLIB2_VERILOG_DEFHANDLER(bvsmod);
SMTLIB2_VERILOG_DEFHANDLER(bvurem);
SMTLIB2_VERILOG_DEFHANDLER(bvsrem);
SMTLIB2_VERILOG_DEFHANDLER(bvshl);
SMTLIB2_VERILOG_DEFHANDLER(bvlshr);
SMTLIB2_VERILOG_DEFHANDLER(bvashr);
SMTLIB2_VERILOG_DEFHANDLER(extract);
SMTLIB2_VERILOG_DEFHANDLER(bit2bool);
SMTLIB2_VERILOG_DEFHANDLER(repeat);
SMTLIB2_VERILOG_DEFHANDLER(zero_extend);
SMTLIB2_VERILOG_DEFHANDLER(sign_extend);
SMTLIB2_VERILOG_DEFHANDLER(rotate_left);
SMTLIB2_VERILOG_DEFHANDLER(rotate_right);

#undef SMTLIB2_VERILOG_DEFHANDLER

} // namespace cosa


