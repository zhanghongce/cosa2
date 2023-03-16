/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Ahmed Irfan, Makai Mann, Florian Lonsing
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#include "engines/prover.h"

#include <cassert>
#include <climits>
#include <functional>
#include <fstream>

#include "core/rts.h"
#include "modifiers/static_coi.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/partial_model.h"
#include "frontends/property_if.h"

using namespace smt;
using namespace std;

namespace pono {

Prover::Prover(const Property & p,
               const TransitionSystem & ts,
               const smt::SmtSolver & s,
               PonoOptions opt)
    : initialized_(false),
      solver_(s),
      to_prover_solver_(s),
      orig_property_(p),
      orig_ts_(ts),
      ts_(ts, to_prover_solver_),
      unroller_(ts_),
      bad_(solver_->make_term(
          smt::PrimOp::Not,
          ts_.solver() == orig_property_.solver()
              ? orig_property_.prop()
              : to_prover_solver_.transfer_term(orig_property_.prop(), BOOL))),
      options_(opt),
      engine_(Engine::NONE)
{
}

Prover::~Prover() {}

void Prover::initialize()
{
  if (initialized_) {
    return;
  }

  reached_k_ = -1;

  if (!ts_.only_curr(bad_)) {
    throw PonoException("Property should not contain inputs or next state variables");
  }

  initialized_ = true;
}

ProverResult Prover::prove()
{
  return check_until(INT_MAX);
}

bool Prover::witness(std::vector<UnorderedTermMap> & out)
{
  if (!witness_.size()) {
    throw PonoException(
        "Recovering witness failed. Make sure that there was "
        "a counterexample and that the engine supports witness generation.");
  }

  function<Term(const Term &, SortKind)> transfer_to_prover_as;
  function<Term(const Term &, SortKind)> transfer_to_orig_ts_as;
  TermTranslator to_orig_ts_solver(orig_ts_.solver());
  if (solver_ == orig_ts_.solver()) {
    // don't need to transfer terms if the solvers are the same
    transfer_to_prover_as = [](const Term & t, SortKind sk) { return t; };
    transfer_to_orig_ts_as = [](const Term & t, SortKind sk) { return t; };
  } else {
    // need to add symbols to cache
    UnorderedTermMap & cache = to_orig_ts_solver.get_cache();
    for (const auto &v : orig_ts_.statevars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }
    for (const auto &v : orig_ts_.inputvars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }

    transfer_to_prover_as = [this](const Term & t, SortKind sk) {
      return to_prover_solver_.transfer_term(t, sk);
    };
    transfer_to_orig_ts_as = [&to_orig_ts_solver](const Term & t, SortKind sk) {
      return to_orig_ts_solver.transfer_term(t, sk);
    };
  }

  bool success = true;

  // Some backends don't support full witnesses
  // it will still populate state variables, but will return false instead of
  // true
  for (const auto & wit_map : witness_) {
    out.push_back(UnorderedTermMap());
    UnorderedTermMap & map = out.back();

    for (const auto &v : orig_ts_.statevars()) {
      const SortKind &sk = v->get_sort()->get_sort_kind();
      const Term &pv = transfer_to_prover_as(v, sk);
      map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
    }

    for (const auto &v : orig_ts_.inputvars()) {
      const SortKind &sk = v->get_sort()->get_sort_kind();
      const Term &pv = transfer_to_prover_as(v, sk);
      try {
        map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
      }
      catch (std::exception & e) {
        success = false;
        break;
      }
    }

    if (success) {
      for (const auto &elem : orig_ts_.named_terms()) {
        const SortKind &sk = elem.second->get_sort()->get_sort_kind();
        const Term &pt = transfer_to_prover_as(elem.second, sk);
        try {
          map[elem.second] = transfer_to_orig_ts_as(wit_map.at(pt), sk);
        }
        catch (std::exception & e) {
          success = false;
          break;
        }
      }
    }
  }

  return success;
}

size_t Prover::witness_length() const { return reached_k_ + 1; }

Term Prover::invar()
{
  if (!invar_)
  {
    throw PonoException("Failed to return invar. Be sure that the property was proven "
                        "by an engine the supports returning invariants.");
  }
  return to_orig_ts(invar_, BOOL);
}

Term Prover::to_orig_ts(Term t, SortKind sk)
{
  if (solver_ == orig_ts_.solver()) {
    // don't need to transfer terms if the solvers are the same
    return t;
  } else {
    // need to add symbols to cache
    TermTranslator to_orig_ts_solver(orig_ts_.solver());
    UnorderedTermMap & cache = to_orig_ts_solver.get_cache();
    for (const auto &v : orig_ts_.statevars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
      const Term &nv = orig_ts_.next(v);
      cache[to_prover_solver_.transfer_term(nv)] = v;
    }
    for (const auto &v : orig_ts_.inputvars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }
    // TODO: need a to add UFs to the cache also
    return to_orig_ts_solver.transfer_term(t, sk);
  }
}

Term Prover::to_orig_ts(Term t)
{
  return to_orig_ts(t, t->get_sort()->get_sort_kind());
}

bool Prover::compute_witness()
{
  // TODO: make sure the solver state is SAT
  if (options_.compute_dynamic_coi_upon_cex_) {
    smt::UnorderedTermSet varset;
    if (options_.use_ilang_coi_constraint_file_) {
      recursive_dynamic_COI_using_ILA_info(varset);
    } else {
      compute_dynamic_COI_from_term(bad_, reached_k_+1, varset);
    }
    std::ofstream fout("COI.txt");
    for (const auto & v : varset)
      fout << v->to_string() << std::endl;

    if(options_.dynamic_coi_check_) {
      UnorderedTermSet all_inputs = ts_.inputvars();
      for (const auto & inpv : ts_.statevars()) {
        if (ts_.state_updates().find(inpv) == ts_.state_updates().end())
          all_inputs.insert(inpv);
      }
      record_coi_info(varset, all_inputs,  reached_k_ + 1 );
    }
  }


  for (int i = 0; i <= reached_k_ + 1; ++i) {
    witness_.push_back(UnorderedTermMap());
    UnorderedTermMap & map = witness_.back();

    for (const auto &v : ts_.statevars()) {
      Term vi = unroller_.at_time(v, i);
      Term r = solver_->get_value(vi);
      map[v] = r;
    }

    // early stop
    if (options_.witness_first_state_only_)
      return true;

    for (const auto &v : ts_.inputvars()) {
      Term vi = unroller_.at_time(v, i);
      Term r = solver_->get_value(vi);
      map[v] = r;
    }

    for (const auto &elem : ts_.named_terms()) {
      Term ti = unroller_.at_time(elem.second, i);
      map[elem.second] = solver_->get_value(ti);
    }
  }

  return true;
}


bool Prover::check_coi() {
  if(!options_.compute_dynamic_coi_upon_cex_) {
    std::cout << "NO COI computed." << std::endl;
    return true;
  }
  if(!options_.dynamic_coi_check_) {
    std::cout << "check is not enabled." << std::endl;
    return true;
  }

  auto another_solver_ = create_solver(BTOR, true, false, true);
  TermTranslator tt_(another_solver_);
  TermTranslator tt_back_(solver_);
  auto add_formula = [&another_solver_, &tt_](const Term & t) -> void {
    another_solver_->assert_formula(tt_.transfer_term(t)); };
  auto get_model = [&another_solver_, &tt_, &tt_back_](const Term & t) -> Term {
    return tt_back_.transfer_term(
      another_solver_->get_value(tt_.transfer_term(t))); };
  
  // add_formula(unroller_.at_time(ts_.init(), 0));
  for (int k = 0; k<=reached_k_+1; ++k) {
    add_formula(unroller_.at_time(ts_.trans(), k));
  }

  // this includes initial svs and input variables along the way
  for (const auto & var_val_pair : all_coi_values) {
    add_formula(solver_->make_term(Equal, var_val_pair.first, var_val_pair.second));
  }
  
  add_formula(unroller_.at_time(solver_->make_term(Not, bad_), reached_k_+1));
  auto result = another_solver_->check_sat();
  if(result.is_sat()) {
    
    
    for (int i = 0; i <= reached_k_ + 1; ++i) {
      coi_failure_witness_.push_back(UnorderedTermMap());
      UnorderedTermMap & map = coi_failure_witness_.back();

      for (const auto &v : ts_.statevars()) {
        Term vi = unroller_.at_time(v, i);
        Term r = get_model(vi);
        map[v] = r;
      }

      for (const auto &v : ts_.inputvars()) {
        Term vi = unroller_.at_time(v, i);
        Term r = get_model(vi);
        map[v] = r;
      }

      for (const auto &elem : ts_.named_terms()) {
        Term ti = unroller_.at_time(elem.second, i);
        map[elem.second] = get_model(ti);
      }
    }
    return false;
  } 
  return true;
}

static const bool restrict_RTL_vars_only_in_ILA_RTL_rfcheck = true;

void Prover::record_coi_info(const smt::UnorderedTermSet &sv, const smt::UnorderedTermSet &inp, int bnd) {
  // store all values on sv @ 0 , and all inp vars @ 0...k
  for (const auto & v : sv) {
    auto sv_name = v->to_string();
    if (restrict_RTL_vars_only_in_ILA_RTL_rfcheck && (sv_name.find("ILA.") == 0 || (sv_name.find("__auxvar") == 0 && sv_name.find("recorder") != sv_name.npos) ))  {
      logger.log(0,"[COI check] removing sv {}", sv_name);
      continue;
    }
    auto timed_v = unroller_.at_time(v, 0);
    auto value = solver_->get_value(timed_v);
    all_coi_values.emplace(timed_v, value);
  }
  for (int k = 0; k<=bnd+1; ++k) {
    for (const auto & inpv : inp) {
      auto timed_v = unroller_.at_time(inpv, k);
      auto value = solver_->get_value(timed_v);
      all_coi_values.emplace(timed_v, value);
      logger.log(0, "[COI check] input {} is locked as {}", timed_v->to_string(), value->to_string());
    }
  }
} // end of record_coi_info

void Prover::get_var_in_COI(const TermVec & asts, UnorderedTermSet & vars) {
  PartialModelGen partial_model_getter(solver_);
  partial_model_getter.GetVarListForAsts(asts, vars);
  // std::cout << "BACKTRACK on :";
  // for (const auto & ast: asts) {
  //   std::cout << " ---> " << ast->to_string() << std::endl;
  // }
  // std::cout << "GET COI: ";
  // for (const auto & v: vars)
  //   std::cout<< v->to_string() << ", ";
  // std::cout << std::endl;
}


void Prover::compute_dynamic_COI_from_term(const smt::Term & t, int k, smt::UnorderedTermSet & init_state_variables) {
  // bad_ ,  0...reached_k_+1
  // auto last_bad = unroller_.at_time(bad_, reached_k_+1);

  auto last_bad = unroller_.at_time(t, k);
  UnorderedTermSet varset;
  get_var_in_COI({last_bad}, varset); // varset contains variables like : a@n

  for(int i = k-1; i>=0; --i) {
    UnorderedTermSet newvarset;
    TermVec update_functions_to_check;
    for (const auto & var : varset) {
      auto untimed_var = unroller_.untime(var);  // a@n --> a

      if (ts_.is_input_var(untimed_var))
        continue;
      if (!ts_.is_curr_var(untimed_var)) // is_curr_var check if it is input var
        continue;
        
      auto pos = ts_.state_updates().find(untimed_var);

      if (pos == ts_.state_updates().end()) // this is likely
        continue; // because ts_ may promote input variables
      // therefore, there could be state vars without next function

      // assert(pos != ts_.state_updates().end());
      const auto & update_function = pos->second;  // a, b, c ...
      // at_time is used to change the variable set in update_function
      auto timed_update_function = unroller_.at_time(update_function, i); // i ?
      update_functions_to_check.push_back(timed_update_function);
    }
    get_var_in_COI(update_functions_to_check, newvarset);
  
    varset.swap(newvarset); // the same as "varset = newvarset;" , but this is faster
  }

  // varset at this point: a@0 ,  b@0 , ...
  for (const auto & timed_var : varset) { 
    init_state_variables.emplace(unroller_.untime(timed_var));
  }
} // end of compute_dynamic_COI_from_term


std::string static remove_vertical_bar(const std::string & in) {
  if (in.length() > 2 && in.front() == '|' && in.back() == '|')
    return in.substr(1,in.length()-2);
  return in;
}

void Prover::recursive_dynamic_COI_using_ILA_info(smt::UnorderedTermSet & init_state_variables) {

  AssumptionRelationReader IlaAsmptLoader("asmpt-ila.smt2", ts_);
  logger.log(3,"{} loaded from asmpt-ila.smt2.", IlaAsmptLoader.ReportStatus());

  UnorderedTermSet init_sv;
  
  // initially, we extract bad
  set<std::pair<smt::Term, int>> next_round_to_track = { {bad_, reached_k_+1} };

  while(!next_round_to_track.empty()) {
    for (const auto & term_k_pair : next_round_to_track) {
      compute_dynamic_COI_from_term(term_k_pair.first, term_k_pair.second, init_sv);
    } // compute all sub var in 
    next_round_to_track.clear();

    // then let's go through all variables
    for (const auto & v : init_sv) {
      if (init_state_variables.find(v) != init_state_variables.end())
        continue; // to avoid repitition like v : v == another variable
      init_state_variables.emplace(v);
      auto vname = remove_vertical_bar(v->to_string());
      if (IlaAsmptLoader.IsConstrainedInAssumption(vname)) {
        logger.log(0, "SV {} is in constraints", vname);
        auto cond = IlaAsmptLoader.GetConditionInAssumption(vname);
        auto val = IlaAsmptLoader.GetValueTermInAssumption(vname);

        bool triggered = false;
        for(int k = 0; k <= reached_k_+1; k++) {
          auto cond_at_k = unroller_.at_time(cond, k);
          auto is_cond_true_at_k = solver_->get_value(cond_at_k)->to_int();
          if(is_cond_true_at_k) {
            
            logger.log(0, "SV {} is triggered at Cycle #{}", vname, k);
            next_round_to_track.emplace(std::make_pair(val, k));
            logger.log(0,"added {} in next round.", val->to_string());
            triggered = true;
            break;
          }
        }
        if(!triggered)
          logger.log(0, "WARNING: [COI] condition for {} was NOT triggered!", vname);
      } else {
        logger.log(0, "SV {} is NOT in constraints", vname);
      }
    } // end for each init_sv
    
    logger.log(0, "----------------END of a round ----------------");
  } // end of while next_round_to_track is not empty

} // end of recursive_dynamic_COI_using_ILA_info


bool Prover::coi_failure_witness(std::vector<UnorderedTermMap> & out)
{
  if (!coi_failure_witness_.size()) {
    throw PonoException(
        "Recovering witness failed. Make sure that there was "
        "a counterexample and that the engine supports witness generation.");
  }

  function<Term(const Term &, SortKind)> transfer_to_prover_as;
  function<Term(const Term &, SortKind)> transfer_to_orig_ts_as;
  TermTranslator to_orig_ts_solver(orig_ts_.solver());
  if (solver_ == orig_ts_.solver()) {
    // don't need to transfer terms if the solvers are the same
    transfer_to_prover_as = [](const Term & t, SortKind sk) { return t; };
    transfer_to_orig_ts_as = [](const Term & t, SortKind sk) { return t; };
  } else {
    // need to add symbols to cache
    UnorderedTermMap & cache = to_orig_ts_solver.get_cache();
    for (const auto &v : orig_ts_.statevars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }
    for (const auto &v : orig_ts_.inputvars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }

    transfer_to_prover_as = [this](const Term & t, SortKind sk) {
      return to_prover_solver_.transfer_term(t, sk);
    };
    transfer_to_orig_ts_as = [&to_orig_ts_solver](const Term & t, SortKind sk) {
      return to_orig_ts_solver.transfer_term(t, sk);
    };
  }

  bool success = true;

  // Some backends don't support full witnesses
  // it will still populate state variables, but will return false instead of
  // true
  for (const auto & wit_map : coi_failure_witness_) {
    out.push_back(UnorderedTermMap());
    UnorderedTermMap & map = out.back();

    for (const auto &v : orig_ts_.statevars()) {
      const SortKind &sk = v->get_sort()->get_sort_kind();
      const Term &pv = transfer_to_prover_as(v, sk);
      map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
    }

    for (const auto &v : orig_ts_.inputvars()) {
      const SortKind &sk = v->get_sort()->get_sort_kind();
      const Term &pv = transfer_to_prover_as(v, sk);
      try {
        map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
      }
      catch (std::exception & e) {
        success = false;
        break;
      }
    }

    if (success) {
      for (const auto &elem : orig_ts_.named_terms()) {
        const SortKind &sk = elem.second->get_sort()->get_sort_kind();
        const Term &pt = transfer_to_prover_as(elem.second, sk);
        try {
          map[elem.second] = transfer_to_orig_ts_as(wit_map.at(pt), sk);
        }
        catch (std::exception & e) {
          success = false;
          break;
        }
      }
    }
  }

  return success;
}



}  // namespace pono
