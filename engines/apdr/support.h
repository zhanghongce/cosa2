
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
 ** \brief Apdr Macros (should only be included in .cpp)
 **
 ** 
 **/
 
#pragma once

#include "config.h"
#include "utils/multitimer.h"

#define DEBUG
#ifdef DEBUG
  #define D(...) logger.log( __VA_ARGS__ )
  #define INFO(...) D(0, __VA_ARGS__)
#else
  #define D(...) do {} while (0)
  #define INFO(...) logger.log(1, __VA_ARGS__)
#endif

// for signal
#define SIGNAL_DUMP 1

// if we have the var assignment in the model
// then ast must be the value
#define TEST_PARTIAL_MODEL
#ifdef TEST_PARTIAL_MODEL                                 
  #define CHECK_MODEL(solver, ast, exp_val, model)            \
    do {                                                      \
      (solver)->push();                                       \
      smt::Term v_assign = (model)->to_expr_btor(solver);            \
      if (exp_val)                                            \
        solver->assert_formula(NOT(ast));                     \
      else    /*expect ast 0*/                                \
        solver->assert_formula((ast));                        \
      solver->assert_formula(v_assign);                       \
      auto check_res = solver->check_sat();                   \
      if (!check_res.is_unsat())                              \
        logger.log(0, "bad model {},\nit cannot ensure {}\n to be {}", (model)->to_string(), (ast)->to_string(), (exp_val)  );    \
      assert( check_res.is_unsat() );                         \
      solver->pop();                                          \
    } while(0)                                                
#else
  #define CHECK_MODEL(solver, ast, exp_val, model) do {} while(0)
#endif      

#ifdef DEBUG
  #define CHECK_PROP_FAIL(x) sanity_check_prop_fail(x)
#else
  #define CHECK_PROP_FAIL(x) do {} while(0)
#endif


// some helper functions
#define TERM_TRUE    (solver_->make_term(true))
#define NOT(x)       (solver_->make_term(smt::Not, (x)))
#define EQ(x, y)     (solver_->make_term(smt::Equal, (x), (y)))
#define AND(x, y)    (solver_->make_term(smt::And, (x), (y)))
#define OR(x, y)     (solver_->make_term(smt::Or, (x), (y)))
#define IMPLY(x, y)  (solver_->make_term(smt::Implies, (x), (y)))
#define IFF(x, y)    (solver_->make_term(smt::Iff, (x), (y)))

// some helper functions
#define TERM_TRUE_msat    (itp_solver_->make_term(true))
#define NOT_msat(x)       (itp_solver_->make_term(smt::Not,     (x)))
// #define EQ_msat(x, y)     (itp_solver_->make_term(smt::Equal, (x), (y)))
#define AND_msat(x, y)    (itp_solver_->make_term(smt::And,     (x), (y)))
#define OR_msat(x, y)     (itp_solver_->make_term(smt::Or,      (x), (y)))
#define IMPLY_msat(x, y)  (itp_solver_->make_term(smt::Implies, (x), (y)))


// ------------------- TRACING ------------- //
// this is full tracing
#define PUSH_STACK(x)   \
  do { \
    GlobalAPdrConfig.Apdr_function_tracing_stack_push((x)); \
    GlobalTimer.RegisterEventStart( GlobalAPdrConfig.Apdr_function_tracing_func_str(x) , 0); \
   } while(0)

#define POP_STACK    \
  do { \
    auto x = GlobalAPdrConfig.Apdr_function_tracing_stack_pop(); \
    GlobalTimer.RegisterEventEnd( GlobalAPdrConfig.Apdr_function_tracing_func_str(x) , 1); \
  } while (0)
