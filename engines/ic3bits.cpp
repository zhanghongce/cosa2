/*********************                                                  */
/*! \file ic3bits.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bit-level IC3 implementation that splits bitvector variables
**        into the individual bits for bit-level cubes/clauses
**        However, the transition system itself still uses bitvectors
**/

#include "utils/logger.h"
#include "engines/ic3bits.h"
#include "utils/container_shortcut.h"

using namespace smt;
using namespace std;


// #define DEBUG
#ifdef DEBUG
  #define D(...) logger.log( __VA_ARGS__ )
  #define INFO(...) D(0, __VA_ARGS__)
#else
  #define D(...) do {} while (0)
  #define INFO(...) logger.log(3, __VA_ARGS__)
#endif


namespace pono {

IC3Bits::IC3Bits(const Property & p,
                 const TransitionSystem & ts,
                 const SmtSolver & s,
                 PonoOptions opt)
    : super(p, ts, s, opt), partial_model_getter(solver_)
{
}

void IC3Bits::initialize()
{
  if (super::initialized_) {
    return;
  }

  if(!options_.ic3_pregen_) {
    options_.ic3_pregen_ = true;
    logger.log(0,"Turning on IC3 predecessor generalization for better performance");
  }
  if (approx_pregen_) {
    logger.log(0,"IC3bits is not an over-generalizaton.");
    approx_pregen_ = false;
  }

  super::initialize();


  build_ts_related_info();

  has_assumptions = false;
  assert(!nxt_state_updates_.empty());
  for (const auto & c_initnext : ts_.constraints()) {
    // if (!c_initnext.second)
    //  continue; // should not matter
    has_assumptions = true;
    assert(ts_.no_next(c_initnext.first));
    // if (no_next) {
    constraints_curr_var_.emplace(c_initnext.first, std::vector<std::pair<int,int>>({{0,0}}));
    // translate input_var to next input_var
    // but the state var ...
    // we will get to next anyway
    constraints_curr_var_.emplace(
      next_curr_replace(ts_.next(c_initnext.first)), std::vector<std::pair<int,int>>({{0,0}}));
    // } // else skip
  }

  // build bits
  Term bv1 = solver_->make_term(1, solver_->make_sort(BV, 1));

  assert(!state_bits_.size());
  for (const auto & sv : ts_.statevars()) {
    const Sort & sort = sv->get_sort();
    if (sort == boolsort_) {
      state_bits_.push_back(sv);
    } else {
      assert(sort->get_sort_kind() == BV);
      for (size_t i = 0; i < sort->get_width(); ++i) {
        state_bits_.push_back(solver_->make_term(
            Equal, solver_->make_term(Op(Extract, i, i), sv), bv1));
      }
    }
  }
} // end of initialize



// call this before op abstraction
// op abstraction will change ts_.inputvar?
// and promote again is needed, but we want to
// keep these states in the model
void IC3Bits::build_ts_related_info() {
  // the input vars and the prime to next function
  const auto & all_state_vars = ts_.statevars();//The input and state in the btor
  for (const auto & sv : all_state_vars) {
    const auto & s_updates = ts_.state_updates();////The state in the btor
    // for(const auto &s:  s_updates){
    //   std::cout<< s.first->to_string() << std::endl;
    // }
    if (!IN(sv, s_updates))
      no_next_vars_.insert(sv);
    else
      nxt_state_updates_.emplace(ts_.next(sv), s_updates.at(sv)); // ts_.next(sv): registers[0] ->  registers[0].next. Why we need to use ts_.statevars()? 
                                                                  // We cam use ts_.state_updates() directly.
  }
}

bool IC3Bits::keep_var_in_partial_model(const Term & v) const {
  if (has_assumptions) { // must keep input vars
    return (ts_.is_curr_var(v));
  }

  return ts_.is_curr_var(v) && !IN(v, no_next_vars_);
} // keep_var_in_partial_model


IC3Formula IC3Bits::get_model_ic3formula() const
{
  // expecting all solving in IC3 to be done at context level > 0
  // so if we're getting a model we should not be at context 0
  assert(solver_context_);

  TermVec children;
  children.reserve(state_bits_.size());
  for (const auto & b : state_bits_) {
    if (solver_->get_value(b) == solver_true_) {
      children.push_back(b);
    } else {
      children.push_back(solver_->make_term(Not, b));
    }
  }

  return ic3formula_conjunction(children);
}

bool IC3Bits::ic3formula_check_valid(const IC3Formula & u) const
{
  // check that children are booleans
  // with only a single variable
  UnorderedTermSet free_vars;
  Op op;
  for (const auto & c : u.children) {
    free_vars.clear();
    get_free_symbolic_consts(c, free_vars);
    if (c->get_sort() != boolsort_ || free_vars.size() > 1) {
      return false;
    }
  }

  // got through all checks without failing
  return true;
}

void IC3Bits::check_ts() const
{
  for (const auto & sv : ts_.statevars()) {
    const Sort & sort = sv->get_sort();
    if (sort != boolsort_ && sort->get_sort_kind() != BV) {
      throw PonoException("Unsupported variable sort in IC3Bits: "
                          + sv->to_string() + ":" + sort->to_string());
    }
  }

  for (const auto & iv : ts_.inputvars()) {
    const Sort & sort = iv->get_sort();
    if (sort != boolsort_ && sort->get_sort_kind() != BV) {
      throw PonoException("Unsupported variable sort in IC3Bits: "
                          + iv->to_string() + ":" + sort->to_string());
    }
  }
}


IC3Formula IC3Bits::ExtractPartialModel(const Term & p) {
  // extract using keep_var_in_partial_model  
  assert(ts_.no_next(p));

  std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> varlist;
  Term bad_state_no_nxt = next_curr_replace(ts_.next(p));

  // we need to make sure input vars are mapped to next input vars

  D(4, "[PartialModel] prime state : {}", bad_state_no_nxt->to_string());
  if (has_assumptions) {
    D(4, "[PartialModel] assumptions (mapped): {}", constraints_curr_var_.size());
    unsigned idx = 0;
    for (const auto & c : constraints_curr_var_)
      D(4, "[PartialModel] assumption #{} : {}", idx ++, c->to_string());
    constraints_curr_var_.emplace(bad_state_no_nxt,std::vector<std::pair<int,int>>({{0,0}}));
    partial_model_getter.GetVarListForAsts_in_bitlevel(constraints_curr_var_, varlist);
    constraints_curr_var_.erase(bad_state_no_nxt);
  } else {
    std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> in_ast;
    in_ast.emplace(bad_state_no_nxt, std::vector<std::pair<int,int>>({{0,0}}) );
    partial_model_getter.GetVarListForAsts_in_bitlevel(
      in_ast,
      varlist);
  }

  {
    D(4, "[PartialModel] before cutting vars: ");
    for (const auto & v : varlist)
      D(4, "[PartialModel] {} := {} ", v->to_string(), solver_->get_value(v)->to_string());
    D(4, "[PartialModel] ------------------- ");
  }

  TermVec conjvec_partial;
  for (const auto & v_slice_pair : varlist) {
    const auto & v = v_slice_pair.first;
    Term val = solver_->get_value(v);
    for (const auto & h_l_pair:v_slice_pair.second) {

      if (!keep_var_in_partial_model(v))
          continue;
      for (int idx = h_l_pair.first; idx >= h_l_pair.second; --idx) {
        auto eq = solver_->make_term(Op(PrimOp::Equal), 
          solver_->make_term(Op(PrimOp::Extract, idx, idx), v),
          solver_->make_term(Op(PrimOp::Extract, idx, idx), val)
        );
        conjvec_partial.push_back( eq );
      }
    }
  }
  return ic3formula_conjunction(conjvec_partial);
} // SygusPdr::ExtractPartialAndFullModel

void IC3Bits::predecessor_generalization(size_t i, const Term & cterm, IC3Formula & pred) {
  // used in rel_ind_check
  // extract the model based on var list
  // NOTE: i may be incorrect, it is given as F/\T->(here is i)

  // no need to pop (pop in rel_ind_check)
  // return the model and build IC3FormulaModel
  if (options_.ic3bits_coi_pregen) {
    pred = ExtractPartialModel(cterm);
  }
} // generalize_predecessor

}  // namespace pono
