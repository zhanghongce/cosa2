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
#include <iomanip>
#include "core/rts.h"
#include "modifiers/static_coi.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/partial_model.h"
#include "assert.h"
using namespace smt;
using namespace std;

namespace pono {
static std::vector<std::pair<int, int>> merge_intervals(
    const std::vector<std::pair<int, int>> & intervals)
{
  if (intervals.empty()) return {};

  std::vector<std::pair<int, int>> sorted_intervals = intervals;
  // Sort by the second value (the smaller one) in descending order
  std::sort(sorted_intervals.begin(),
            sorted_intervals.end(),
            [](const auto & a, const auto & b) { return a.second > b.second; });

  std::vector<std::pair<int, int>> merged_intervals;
  merged_intervals.push_back(sorted_intervals[0]);

  for (size_t i = 1; i < sorted_intervals.size(); ++i) {
    auto & last_merged_interval = merged_intervals.back();
    if (sorted_intervals[i].first >= last_merged_interval.second - 1) {
      last_merged_interval.second =
          std::min(sorted_intervals[i].second, last_merged_interval.second);
      last_merged_interval.first =
          std::max(sorted_intervals[i].first, last_merged_interval.first);
    } else
      merged_intervals.push_back(sorted_intervals[i]);
  }
  return merged_intervals;
}


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
  for (auto wit_map : witness_) {
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
    var_in_coi_t varset;

    int backtrack_to_step_n = 0;
    
    var_in_coi_t input_var_tmp;
    int num_coi = 0;
    compute_dynamic_COI_from_term(bad_,
                                    { { 0, 0 } },
                                    reached_k_ + 1,
                                    varset,
                                    input_var_tmp,
                                    backtrack_to_step_n,
                                    num_coi);
    
    std::ofstream fout("COI.txt");
    for (const auto & v : varset) {  // varname size h0 l0 h1 l1 ...
      if(ts_.state_updates().find(v.first) == ts_.state_updates().end())
        continue;
      fout << v.first->to_string();
      fout << " " << v.second.size();
      for (const auto & h_l : v.second)
        fout << " " << h_l.first << " " << h_l.second;
      auto var_time =  unroller_.at_time(v.first, backtrack_to_step_n);
      fout <<" "<<solver_->get_value(var_time)->to_string();
      fout << std::endl;
    }
    
    float num_state_float = static_cast<float>(ts_.statevars().size());
    float bound_float = static_cast<float>(reached_k_ + 2);
    float coi_float = static_cast<float>(num_coi);
    std::ofstream summary_of_COI(options_.logging_coi_, std::ios::app);
    assert(!ts_.inputvars().size());
    summary_of_COI<< options_.filename_ << " | " << "state: " << ts_.statevars().size()<< " | " << "trace length: "
                  << reached_k_ + 2 << " | " << "total: " << ts_.statevars().size()*(reached_k_ + 2) << " | " << "after COI: "
                  << num_coi << " | " << "reduction: " << std::setprecision(2)
                  <<1 - coi_float / (num_state_float * bound_float) <<std::endl;
    summary_of_COI.close(); 
    
    if (options_.dynamic_coi_check_) {
      UnorderedTermSet all_inputs = ts_.inputvars();
      for (const auto & inpv : ts_.statevars()) {
        if (ts_.state_updates().find(inpv) == ts_.state_updates().end())
          all_inputs.insert(inpv);
      }
      record_coi_info(varset, all_inputs, reached_k_ + 1, backtrack_to_step_n);
    }
  }
  for (int i = 0; i <= reached_k_ + 1; ++i) {
    witness_.push_back(UnorderedTermMap());
    UnorderedTermMap & map = witness_.back();

    for (const auto &v : ts_.statevars()) {
      const Term &vi = unroller_.at_time(v, i);
      const Term &r = solver_->get_value(vi);
      map[v] = r;
    }

    for (const auto &v : ts_.inputvars()) {
      const Term &vi = unroller_.at_time(v, i);
      const Term &r = solver_->get_value(vi);
      map[v] = r;
    }

    for (const auto &elem : ts_.named_terms()) {
      const Term &ti = unroller_.at_time(elem.second, i);
      map[elem.second] = solver_->get_value(ti);
    }
  }

  return true;
}


static const bool restrict_RTL_vars_only_in_ILA_RTL_rfcheck = false;

bool Prover::check_coi(const smt::Term & original_trans)
{
  if (!options_.compute_dynamic_coi_upon_cex_) {
    std::cout << "NO COI computed." << std::endl;
    return true;
  }
  if (!options_.dynamic_coi_check_) {
    std::cout << "check is not enabled." << std::endl;
    return true;
  }

  // {
  //   std::ofstream fout("coi-check.txt");
  //   for (const auto & item : coi_trace_k) {
  //     fout << std::get<1>(item) << " " << std::get<0>(item) << " "
  //          << std::get<2>(item) << "\n";
  //   }
  // }

  auto another_solver_ = create_solver(BTOR, true, false, true);
  TermTranslator tt_(another_solver_);
  TermTranslator tt_back_(solver_);
  auto add_formula = [&another_solver_, &tt_](const Term & t) -> void {
    another_solver_->assert_formula(tt_.transfer_term(t));
  };
  auto get_model = [&another_solver_, &tt_, &tt_back_](const Term & t) -> Term {
    return tt_back_.transfer_term(
        another_solver_->get_value(tt_.transfer_term(t)));
  };

  // add_formula(unroller_.at_time(ts_.init(), 0));
  for (int k = 0; k <= reached_k_; ++k) {
    // add_formula(unroller_.at_time(ts_.trans(), k));
    add_formula(unroller_.at_time(original_trans, k));
  }

  // this includes initial svs and input variables along the way
  for (const auto & var_val_pair : all_coi_values) {
    add_formula(
        solver_->make_term(Equal, var_val_pair.first, var_val_pair.second));
  }

  add_formula(unroller_.at_time(solver_->make_term(Not, bad_), reached_k_ + 1));
  auto result = another_solver_->check_sat();
  if (result.is_sat()) {
    for (int i = 0; i <= reached_k_ + 1; ++i) {
      coi_failure_witness_.push_back(UnorderedTermMap());
      UnorderedTermMap & map = coi_failure_witness_.back();

      for (const auto & v : ts_.statevars()) {
        Term vi = unroller_.at_time(v, i);
        Term r = get_model(vi);
        map[v] = r;
      }

      for (const auto & v : ts_.inputvars()) {
        Term vi = unroller_.at_time(v, i);
        Term r = get_model(vi);
        map[v] = r;
      }

      for (const auto & elem : ts_.named_terms()) {
        Term ti = unroller_.at_time(elem.second, i);
        map[elem.second] = get_model(ti);
      }
    }
    if (!restrict_RTL_vars_only_in_ILA_RTL_rfcheck)
      throw PonoException("COI check failed!");
    return false;
  }
  return true;
}

bool static keep_this_name(const std::string & n)
{
  const static std::unordered_set<std::string> keep = {
    "__START__",    "__STARTED__", "__ENDED__",
    "__2ndENDED__", "__RESETED__", "__CYCLE_CNT__"
  };
  const static std::unordered_set<std::string> partial_keep = {
    "__delay_d", "__recorder_sn_condmet"
  };
  const static std::string aux_var_ends = "__recorder";

  if (keep.find(n) != keep.end()) return true;
  if (n.find("ILA.") == 0) return false;
  if (n.find("RTL.") == 0) return true;
  for (const auto & sub : partial_keep)
    if (n.find(sub) != n.npos) return true;

  if (n.find("__auxvar") == 0 && n.length() >= aux_var_ends.length()
      && n.compare(n.length() - aux_var_ends.length(),
                   aux_var_ends.length(),
                   aux_var_ends)
             == 0)
    return false;
  if (n.find("__VLG_I_") == 0 || n.find("__ILA_I_") == 0 || n == "dummy_reset"
      || n == "reset" || n == "rst")
    return false;
  if (n.find("ppl_stage_") == 0) return true;
  throw PonoException("Unknown how to handle: " + n);
  return false;
  //
}

void Prover::record_coi_info(const var_in_coi_t & sv,
                             const smt::UnorderedTermSet & inp,
                             int bnd,
                             int start_bnd)
{
  // store all values on sv @ 0 , and all inp vars @ 0...k
  for (const auto & v : sv) {
    auto sv_name = v.first->to_string();
    if (restrict_RTL_vars_only_in_ILA_RTL_rfcheck) {
      if (!keep_this_name(sv_name)) {
        logger.log(0, "[COI check] removing sv {}", sv_name);
        continue;
      }
    }
    auto timed_v = unroller_.at_time(v.first, start_bnd);
    auto value = solver_->get_value(timed_v);
    for (const auto & range : v.second) {
      auto extracted_v = solver_->make_term(
          smt::Op(smt::PrimOp::Extract, range.first, range.second), timed_v);
      auto extracted_val = solver_->make_term(
          smt::Op(smt::PrimOp::Extract, range.first, range.second), value);
      all_coi_values.emplace(extracted_v, extracted_val);
      logger.log(0,
                 "[COI check] sv {} is locked as {}",
                 extracted_v->to_string(),
                 extracted_val->to_string());
    }
  }
  for (int k = start_bnd; k <= bnd; ++k) {
    for (const auto & inpv : inp) {
      auto timed_v = unroller_.at_time(inpv, k);
      auto value = solver_->get_value(timed_v);
      all_coi_values.emplace(timed_v, value);
      logger.log(0,
                 "[COI check] input {} is locked as {}",
                 timed_v->to_string(),
                 value->to_string());
    }
  }
}  // end of record_coi_info

void Prover::get_var_in_COI(const var_in_coi_t & input_asts,
                            var_in_coi_t & varset_slice)
{
  PartialModelGen partial_model_getter(solver_);
  partial_model_getter.GetVarListForAsts_in_bitlevel(input_asts, varset_slice);
  // std::cout << "[get var in COI] in:\n";
  // std::cout << " (Omitted). \n";
  // Print(input_asts);
  // std::cout << "[get var in COI] out:\n";
  // Print(varset_slice);
}

void Prover::compute_dynamic_COI_from_term(const smt::Term & t,
                                           const slice_t & ranges,
                                           int k,
                                           var_in_coi_t & init_state_variables,
                                           var_in_coi_t & input_state_variables,
                                           int backtrack_frame,
                                           int & num_coi)
{
  // bad_ ,  0...reached_k_+1
  // auto last_bad = unroller_.at_time(bad_, reached_k_+1);

  auto t_at_time_k = unroller_.at_time(t, k);
  var_in_coi_t varset;
  get_var_in_COI({ { t_at_time_k, ranges } },
                 varset);  // varset contains variables like : a@n
  std::ofstream fout("coi-check-rev.txt");
  for(const auto out:varset){
    for(const auto slice: out.second){
      auto val = solver_->get_value(out.first);
      fout<< k << " "<<out.first->to_string() << " "<<slice.first << " " <<slice.second << " " <<val->to_string()<<"\n";
    }
  }
  num_coi = varset.size();

  for (int i = k - 1; i >= backtrack_frame; --i) {
    std::unordered_map<smt::Term, std::vector<std::pair<int, int>>>
        update_functions_to_check;
    std::unordered_map<smt::Term, std::vector<std::pair<int, int>>>
        newvarset_slice;
    for (const auto & var_ranges_pair : varset) {
      auto untimed_var = unroller_.untime(var_ranges_pair.first);  // a@n --> a
      register_coi_trace_k(
          untimed_var->to_string(),
          i + 1,
          solver_->get_value(var_ranges_pair.first)->to_string());

      if (ts_.is_input_var(untimed_var)) continue;
      if (!ts_.is_curr_var(
              untimed_var))  // is_curr_var check if it is input var
        continue;

      auto pos = ts_.state_updates().find(untimed_var);

      if (pos == ts_.state_updates().end())  // this is likely
        continue;  // because ts_ may promote input variables
      // therefore, there could be state vars without next function

      // assert(pos != ts_.state_updates().end());
      const auto & update_function = pos->second;  // a, b, c ...
      // at_time is used to change the variable set in update_function
      auto timed_update_function =
          unroller_.at_time(update_function, i);  // i ?
      update_functions_to_check.emplace(timed_update_function,
                                        var_ranges_pair.second);
    }  // for each variable in varset
    
    auto constraints = ts_.constraints();
    if(constraints.empty()==false){
      Term constraint_all;
      for(const auto constraint: constraints){
        assert(constraint.second);
        if(constraint_all==nullptr)
          constraint_all = constraint.first;
        else
          constraint_all = ts_.make_term(And,constraint_all, constraint.first);
      }
      auto constraint_update_function =
            unroller_.at_time(constraint_all, i);  // i ?
      slice_t range;
      range.push_back(std::make_pair(0, 0));
      update_functions_to_check.emplace(constraint_update_function,range);  
    }
  
    
    get_var_in_COI(update_functions_to_check, newvarset_slice);

    for(const auto out:newvarset_slice){
      for(const auto slice: out.second){
        auto val = solver_->get_value(out.first);
        fout<< i << " "<<out.first->to_string() << " " << slice.first << " " <<slice.second << " " <<val->to_string()<<"\n";
      }
    }
    varset.swap(newvarset_slice);  // the same as "varset = newvarset;" , but
                                   // this is faster
    num_coi = num_coi + varset.size();
  }
  
  fout.close();
  // varset at this point: a@0 ,  b@0 , ...
  for (const auto & timed_var : varset) {
    auto untimed_var = unroller_.untime(timed_var.first);
    register_coi_trace_k(untimed_var->to_string(),
                         backtrack_frame,
                         solver_->get_value(timed_var.first)->to_string());

    auto pos = ts_.state_updates().find(untimed_var);

    if (ts_.is_input_var(untimed_var) || !ts_.is_curr_var(untimed_var)
        || pos == ts_.state_updates().end()) {
      // this is an input variable
      auto res = input_state_variables.emplace(untimed_var, timed_var.second);
      if (!res.second) {
        const auto & old_ranges = input_state_variables.at(untimed_var);
        auto new_range = timed_var.second;
        new_range.insert(
            new_range.begin(), old_ranges.begin(), old_ranges.end());
        new_range = merge_intervals(new_range);
        input_state_variables.at(untimed_var) = new_range;
      }
      continue;
    }

    auto result = init_state_variables.emplace(untimed_var, timed_var.second);
    if (!result.second) {
      // was not able to insert, then we need to merge list
      const auto & old_ranges = init_state_variables.at(untimed_var);
      auto new_range = timed_var.second;
      new_range.insert(new_range.begin(), old_ranges.begin(), old_ranges.end());
      new_range = merge_intervals(new_range);
      init_state_variables.at(untimed_var) = new_range;
    }
  }
}  // end of compute_dynamic_COI_from_term

std::string static remove_vertical_bar(const std::string & in)
{
  if (in.length() > 2 && in.front() == '|' && in.back() == '|')
    return in.substr(1, in.length() - 2);
  return in;
}
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
    for (const auto & v : orig_ts_.statevars()) {
      cache[to_prover_solver_.transfer_term(v)] = v;
    }
    for (const auto & v : orig_ts_.inputvars()) {
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

    for (const auto & v : orig_ts_.statevars()) {
      const SortKind & sk = v->get_sort()->get_sort_kind();
      const Term & pv = transfer_to_prover_as(v, sk);
      map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
    }

    for (const auto & v : orig_ts_.inputvars()) {
      const SortKind & sk = v->get_sort()->get_sort_kind();
      const Term & pv = transfer_to_prover_as(v, sk);
      try {
        map[v] = transfer_to_orig_ts_as(wit_map.at(pv), sk);
      }
      catch (std::exception & e) {
        success = false;
        break;
      }
    }

    if (success) {
      for (const auto & elem : orig_ts_.named_terms()) {
        const SortKind & sk = elem.second->get_sort()->get_sort_kind();
        const Term & pt = transfer_to_prover_as(elem.second, sk);
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
