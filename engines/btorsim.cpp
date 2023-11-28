/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Makai Mann, Florian Lonsing
 ** This file is part of the pono project.
 ** Copyright (c) 2019, 2021, 2022 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "btorsim.h"
#include "utils/logger.h"

#include "smt-switch/utils.h"

#include "smt/available_solvers.h"

#include <fstream>

using namespace smt;

namespace pono {

BtorSim::BtorSim(const Property & p, const TransitionSystem & ts,
         const SmtSolver & solver, PonoOptions opt)
  : super(p, ts, solver, opt)
{
  engine_ = Engine::BTOR_SIM;
}

BtorSim::~BtorSim() {}

void BtorSim::initialize()
{
  if (initialized_) {
    return;
  }

  super::initialize();

  // NOTE: for any engine; There's an implicit assumption that this solver is only used for
  // model checking once Otherwise there could be conflicting assertions to
  // the solver or it could just be polluted with redundant assertions in the
  // future we can use solver_->reset_assertions(), but it is not currently
  // supported in boolector
  logger.log(2, "BTOR_SIM adding init constraint for step 0");
  solver_->assert_formula(unroller_.at_time(ts_.init(), 0));
  base_formula = unroller_.at_time(ts_.init(), 0);
}

ProverResult BtorSim::check_until(int k)
{
  initialize();

  //NOTE: there is a corner case where an instance is trivially
  //unsatisfiable, i.e., safe, when the conjunction of initial state
  //predicate and transition (+ any constraints) is already unsat. We
  //could also check this using unsat core functionality of solver (if
  //supported), and check if bad state predicate is in core

  Term no_reset_assumption;
  if (!options_.reset_name_.empty()) {
    std::string reset_name = options_.reset_name_;
    bool negative_reset = false;
    if (reset_name.at(0) == '~') {
      reset_name = reset_name.substr(1, reset_name.length() - 1);
      negative_reset = true;
    }
    Term reset_symbol = ts_.lookup(reset_name);
    if (!negative_reset) {
      SortKind sk = reset_symbol->get_sort()->get_sort_kind();
      reset_symbol = (sk == BV) ? solver_->make_term(BVNot, reset_symbol)
                                : solver_->make_term(Not, reset_symbol);
    }
    no_reset_assumption = reset_symbol;
    logger.log(0, "no-reset condition:" + no_reset_assumption->to_string());
  }


  logger.log(1, "unrolling to:" + std::to_string(k));
  for (int i = 0; i <= k; i ++) {
    if (i > 0) {
      auto t = unroller_.at_time(ts_.trans(), i - 1);
      solver_->assert_formula(t);
      base_formula = solver_->make_term(smt::And, base_formula, t);
    }
    // need to assume no reset in every cycle
    if( no_reset_assumption != nullptr ) {
      auto t = unroller_.at_time(no_reset_assumption, i);
      solver_->assert_formula(t);
      base_formula = solver_->make_term(smt::And, base_formula, t);
    }
  }
  logger.log(1,"Check SAT #1");
  auto res = solver_->check_sat();
  // must be SAT

  logger.log(1, "SAT of init /\\ trans:" + res.to_string());
  if(!res.is_sat())
   throw PonoException("Unexpected unsat result in BMC unrolling");

  // add input random constraints
  TermVec inp_assumps;
  for (int i = 0; i <= k; i ++) {
    for (const auto inpv : ts_.inputvars()) {
      if(inpv->to_string() == options_.reset_name_)
        continue;
      auto sk = inpv->get_sort()->get_sort_kind();
      int val;
      if (sk == smt::SortKind::BOOL)
        val = random() % 2;
      else {
        if (sk != smt::SortKind::BV) continue;
        auto width = inpv->get_sort()->get_width();
        int max = pow(2,width);
        val = random() % max;
      }
      auto smtval = solver_->make_term(val, inpv->get_sort());
      auto inp_constraint = solver_->make_term(smt::Equal, 
        unroller_.at_time(inpv, i), smtval);  // inpv@i == smtval
      inp_assumps.push_back(inp_constraint);
    }
  }

  logger.log(1, "got inp constraint size:" + std::to_string( inp_assumps.size()) );
  auto r2 = solver_->check_sat_assuming(inp_assumps);
  logger.log(1, "init/\\trans/\\inp-constraint:" + r2.to_string());
  if (r2.is_unsat()) {
    // random input has a conflict with the assumptions, then try to remove some inputs
    auto reducer_solver = create_reducer_for(SolverEnum::BTOR, Engine::BMC, false);
    UnsatCoreReducer reducer(reducer_solver);
    TermVec inp_assumps_reduced;
    TermVec no_conflict_assumpts;
    reducer.reduce_assump_unsatcore(base_formula, inp_assumps, inp_assumps_reduced, &no_conflict_assumpts);

    logger.log(1, "after reduction, got "+ std::to_string( no_conflict_assumpts.size() )+ " no-conflict input assumptions");
    for (const auto & asmpt : no_conflict_assumpts)
      solver_->assert_formula(asmpt);
    r2 = solver_->check_sat();
    assert(r2.is_sat());
  }


  reached_k_ = k;
  compute_witness();

  std::ofstream fout("simtrace.txt");
  for (int i = 0; i <= reached_k_ + 1; ++i) {
    for (const auto &v : ts_.statevars()) {
      const Term &vi = unroller_.at_time(v, i);
      const Term &r = solver_->get_value(vi);
      fout << v->to_string() << ": "<< r->to_string() << ", ";
    }
    fout << std::endl;
  }

  return ProverResult::UNKNOWN;
}

  
}  // namespace pono
