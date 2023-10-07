/*********************                                                        */
/*! \file cex_generalizer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   
 ** This file is part of the CEDA-HK EDAthon.
 ** \endverbatim
 **
 ** \brief
 **
 **
 **/

#include "utils/logger.h"
#include "core/unroller.h"
#include "smt/available_solvers.h"
#include "smt-switch/utils.h"
#include <iomanip>
#include "cex_generalizer.h"

#include "gmpxx.h"
#include "assert.h"
#include <fstream>
namespace pono {

using namespace std;
using namespace smt;

struct k_var_val {
  size_t k;
  Term var;
  Term val;
  k_var_val(size_t k_, const Term & variable, const Term & value) :
    k(k_), var(variable), val(value) {}
};


// this will insert (var, val) pair to clock cycle k
void CexGeneralizer::cex_trace_insert(size_t k, const Term & var, const Term & val) {
  if(generalized_cex.size() <= k) {
    generalized_cex.resize(k+1);
  }
  auto & vmap = generalized_cex.at(k);
  assert(vmap.find(var) == vmap.end());
  vmap.emplace(var, val);
} // end of cex_trace_insert

CexGeneralizer::CexGeneralizer(
    const TransitionSystem & ts,
    const BTOR2Encoder & btor_enc,
    const CexTraceType & cex,
    const PonoOptions opt) {

  if (cex.empty())
    throw PonoException("No CEX trace to generalize.");

  // TODO: add your code here
  // Assemble the formula: init(@0) /\ T@0 /\ T@1 /\ ... /\ T@k-1 /\ P@k-1
  //                         v0 @ 0 == ?? 
  //                      /\ v1 @ 0 == ??
  //                      /\ ...
  //                      /\ i0 @ 0 == ??
  //                      /\ ...
  //                      /\ i0 @ 1 == ??
  //                         ...
  //   the above should be unsat, and then ReduceUNSATCore

  // make a new (local) trans
  SmtSolver ts_new_slv = create_solver_for(BTOR, BMC, true);
  TermTranslator termtrans(ts_new_slv);

  SmtSolver reducer_slv = create_reducer_for(BTOR, BMC, true);
  UnsatCoreReducer reducer(reducer_slv);

  auto translate_term = [&termtrans](const Term & t) -> Term { 
    return termtrans.transfer_term(t); };

  // only handle the first property
  assert (btor_enc.propvec().size() == 1);
  auto prop = translate_term(btor_enc.propvec().at(0));
  // auto prop_new =  translate_term(prop);
  TransitionSystem ts_(ts, termtrans);
  const auto & sv = ts_.statevars();
  const auto & inpv = ts_.inputvars();

  Unroller unroller_(ts_);

  auto init_conj_trans = unroller_.at_time(ts_.init(), 0);
  unordered_map<Term, k_var_val> expr2cex;
  TermVec all_eq_expr;
  auto cex_length = cex.size();
  for (size_t k = 0; k < cex_length; ++k) {
    // EDAthon code starts here.
    init_conj_trans = ts_.make_term(And, init_conj_trans,
      unroller_.at_time(ts_.trans(), k));

    const auto & state_at_cycle_k = cex.at(k);
    for (const auto & term_val_pair : state_at_cycle_k) {
      auto var = translate_term(term_val_pair.first);
      // check if var is statevar or inputvar or none of the above
      if (sv.find(var) == sv.end() && inpv.find(var) == inpv.end())
        continue; // we don't care about wires
      
      auto pos = ts_.state_updates().find(var);
      if (k > 0 && pos!= ts_.state_updates().end())
        continue; // If we use promote variable, we need to check whether the state is in the state_update

      // if(!promote_invar){
      //   if (k > 0 && inpv.find(var) == inpv.end())
      //     continue; // for all later steps svs are not needed
      // }
      // else{
      //   auto pos = ts_.state_updates().find(var);
      //   if (k > 0 && pos!= ts_.state_updates().end())
      //     continue; // If we use promote variable, we need to check whether the state is in the state_update
      // }
      auto val = translate_term(term_val_pair.second);
      
      auto term_val_eq = ts_.make_term(Equal, var, val);
      // set unroller
      auto term_val_eq_k = unroller_.at_time(term_val_eq, k);
      // store it, and make sure we can later map it back
      expr2cex.emplace(term_val_eq_k,
        k_var_val(k, term_val_pair.first, term_val_pair.second));
      all_eq_expr.push_back(term_val_eq_k);
    }

  } // end for each clock cycle
  // init_conj_trans := init_conj_trans /\ prop
  init_conj_trans = ts_.make_term(And, init_conj_trans, unroller_.at_time(prop, cex_length-1));

  { // a sanity check
    ts_new_slv->push();
      ts_new_slv->assert_formula(init_conj_trans);
      auto res = ts_new_slv->check_sat_assuming(all_eq_expr);
      if (res == SAT) { // This should not happen
        // print debugging info
        
        UnorderedTermSet allvars;
        get_free_symbols(init_conj_trans, allvars);
        for (const auto & v : allvars) {
          auto val = ts_new_slv->get_value(v);
          logger.log(0, "{} : {}",  v->to_string(), val->to_string());
        }
        throw PonoException("CexGeneralizer: sanity check failed!");
      }
    ts_new_slv->pop();
  } // end of sanity check

  // to reduce the unsatcore using two methods
  TermVec reduced_all_eq_expr;
  reducer.reduce_assump_unsatcore(init_conj_trans, all_eq_expr, reduced_all_eq_expr);

  TermVec final_reduction;
  reducer.linear_reduce_assump_unsatcore(init_conj_trans, reduced_all_eq_expr, final_reduction);
  

  // translate it back to CexTraceType
  for (const auto & eq : final_reduction) {
    const auto & var_val_pair = expr2cex.at(eq);
    cex_trace_insert(var_val_pair.k, var_val_pair.var, var_val_pair.val);
  }
  std::ofstream summary_of_pivot_input( opt.logging_pivot_input_, std::ios::app);
  assert(!ts_.inputvars().size());

    float num_state_float = static_cast<float>(ts_.statevars().size());
    float bound_float = static_cast<float>(cex_length);
    float pivot_float = static_cast<float>(final_reduction.size());

  summary_of_pivot_input<< opt.filename_ << " | " << "state: " << ts_.statevars().size()<< " | " << "trace length: "
                  << cex_length << " | " << "total: " << ts_.statevars().size()*cex_length << " | " << "after reduction: "
                  << final_reduction.size() << " | " << "reduction: " <<  std::setprecision(2)
                  << 1 - pivot_float / (num_state_float*bound_float) 
                  << std::endl;
  summary_of_pivot_input.close(); 
} // end of CexGeneralizer::CexGeneralizer


std::string CexGeneralizer::as_bits(std::string val)
{
  // TODO: this makes assumptions on format of value from boolector
  //       to support other solvers, we need to be more general
  std::string res = val;

  if (val.length() < 2) {
    throw PonoException("Don't know how to interpret value: " + val);
  }

  if (res.substr(0, 2) == "#b") {
    // remove the #b prefix
    res = res.substr(2, val.length() - 2);
  } else if (res.substr(0, 2) == "#x") {
    throw PonoException("Not supporting hexadecimal format yet.");
  } else {
    res = res.substr(5, res.length() - 5);
    std::istringstream iss(res);
    std::vector<std::string> tokens(std::istream_iterator<std::string>{ iss },
                                    std::istream_iterator<std::string>());

    if (tokens.size() != 2) {
      throw PonoException("Failed to interpret " + val);
    }

    res = tokens[0];
    // get rid of ")"
    std::string width_str = tokens[1].substr(0, tokens[1].length() - 1);
    size_t width = std::stoull(width_str);
    mpz_class cval(res);
    res = cval.get_str(2);
    size_t strlen = res.length();

    if (strlen < width) {
      // pad with zeros
      res = std::string(width - strlen, '0') + res;
    } else if (strlen > width) {
      // remove prepended zeros
      res = res.erase(0, strlen - width);
    }
    return res;
  }
  return res;
} // end of as_bits

void CexGeneralizer::print_btor_vals_at_time(
  const smt::TermVec & vec,
  const smt::UnorderedTermMap & valmap,
  unsigned int time,
  std::ofstream & fout)
{
  smt::SortKind sk;
  smt::TermVec store_children(3);
  for (size_t i = 0, size = vec.size(); i < size; ++i) {
    // if valmap does not contain this vector, then let's skip it
    if (valmap.find(vec.at(i)) == valmap.end())
      continue;
    sk = vec[i]->get_sort()->get_sort_kind();
    fout<< "@"<<time<<std::endl;
    if (sk == smt::BV) {
      // this makes assumptions on format of value from boolector
      logger.log(0,
                 "{} {} {}@{}",
                 i,
                 as_bits(valmap.at(vec[i])->to_string()),
                 vec[i],
                 time);
      fout<< i << " "<<as_bits(valmap.at(vec[i])->to_string())<< " " << vec[i] << "@"<<time<<std::endl;
    } else if (sk == smt::ARRAY) {
      smt::Term tmp = valmap.at(vec[i]);
      while (tmp->get_op() == smt::Store) {
        int num = 0;
        for (auto c : tmp) {
          store_children[num] = c;
          num++;
        }

        logger.log(0,
                   "{} [{}] {} {}@{}",
                   i,
                   as_bits(store_children[1]->to_string()),
                   as_bits(store_children[2]->to_string()),
                   vec[i],
                   time);
        tmp = store_children[0];
        fout<< i << " "<<"["<<as_bits(store_children[1]->to_string())<<"]"<<" "<< as_bits(store_children[2]->to_string()) 
        << " " << vec[i] << "@"<<time<<std::endl;
      }

      if (tmp->get_op().is_null()
          && tmp->get_sort()->get_sort_kind() == smt::ARRAY) {
        smt::Term const_val = *(tmp->begin());
        logger.log(
            0, "{} {} {}@{}", i, as_bits(const_val->to_string()), vec[i], time);
      }

    } else {
      throw PonoException("Unhandled sort kind: " + ::smt::to_string(sk));
    }
  }
} // end of print_btor_vals_at_time


void CexGeneralizer::print_witness_btor(
  const BTOR2Encoder & btor_enc,
  const std::vector<smt::UnorderedTermMap> & cex)
{
  if (cex.empty()) {
    logger.log(0, "#0\nEmpty trace.");
    return;
  }
  
  const smt::TermVec inputs = btor_enc.inputsvec();
  const smt::TermVec states = btor_enc.statesvec();
  

  smt::TermVec no_next_states;
  for (const auto & n_s_pair : btor_enc.no_next_statevars()) {
    no_next_states.push_back(n_s_pair.second);
  }
  bool has_states_without_next = no_next_states.size();

  logger.log(0, "#0");
  std::ofstream fout("pivot_input.txt");
  print_btor_vals_at_time(states, cex.at(0), 0,fout);

  for (size_t k = 0, cex_size = cex.size(); k < cex_size; ++k) {
    // states without next
    if (k && has_states_without_next) {
      logger.log(0, "#{}", k);

      print_btor_vals_at_time(no_next_states, cex.at(k), k, fout);
    }

    // inputs
    if (k < cex_size) {
      logger.log(0, "@{}", k);
      print_btor_vals_at_time(inputs, cex.at(k), k, fout);
    }
  }
  fout.close();

  logger.log(0, ".");
} // end of print_witness_btor


} // end of namespace pono
