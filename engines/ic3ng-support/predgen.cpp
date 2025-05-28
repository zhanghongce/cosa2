/*********************                                                  */
/*! \file predgen.cpp
** \verbatim
** Top contributors (to current version of this file):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2025 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Predecessor generalization using UNSAT core-based method
**/



#include "engines/ic3ng.h"
#include "engines/ic3ng-support/debug.h"
#include "utils/container_shortcut.h"


namespace pono
{
  
static size_t TermScore(const smt::Term & t) {
  auto e = (t->get_op().prim_op == smt::PrimOp::Not ||
            t->get_op().prim_op == smt::PrimOp::BVNot) ? *(t->begin()): t;
  unsigned slice = 0;
  if (e->get_op().prim_op == smt::PrimOp::Extract) {
    slice = e->get_op().idx0;
    auto c = *(e->begin());
    slice += c->get_sort()->get_width();
  }
  return slice;
}

void IC3ng::SortCube(std::vector<std::pair<smt::Term, smt::Term>> & inout, bool descending) {
  // we don't want to sort the term themselves
  // we don't want to invoke TermScore function more than once for a term
  std::vector<std::pair<size_t,size_t>> complexity_index_pair;
  size_t idx = 0;
  for (const auto & t : inout) { /* score: slice + width */
    complexity_index_pair.push_back({ TermScore(t.first) ,idx++});
  }

  // HZ: it seems that ascending sorting will put lower bits first

  //  0: ((_ extract 0 0) x)
  //  1: ((_ extract 2 2) x)
  // ....

#ifdef DEBUG_IC3_PREDGEN
  std::cout << "Before sorting cube:\n";
  unsigned i = 0;
  for (const auto & e : inout)
    std::cout << " " << i++ << ": " << e.first->to_string() << " = " << e.second->to_string() << "\n";
  std::cout << "------------------\n";
#endif

  // sort in descending order (the `first` is compared first), so term-index with 
  // the highest score will rank first
  if(descending) // from greater to smaller
    std::sort(complexity_index_pair.begin(), complexity_index_pair.end(), std::greater<>());
  else // from smaller to greater
    std::sort(complexity_index_pair.begin(), complexity_index_pair.end(), std::less<>());
    

  // now map back to termvec
  std::vector<std::pair<smt::Term, smt::Term>> sorted_term;
  for (const auto & cpl_idx_pair : complexity_index_pair)
    sorted_term.push_back(inout.at(cpl_idx_pair.second));
  
  inout.swap(sorted_term); // this is the same as inout = sorted_term, but faster
} // end of SortCube


// reduce predecessor by unsat core reduction
void IC3ng::get_min_pred(
  const smt::Term &bad_next, /* bad (over current version of variables) */
  unsigned prevFidx, // fidx
  smt::UnorderedTermSet & slicedvars,
  smt::UnorderedTermSet & noslicevars,
  smt::TermVec & eqs)
{ // starting from vars in constraints
  smt::UnorderedTermSet varset = vars_in_constraints_;
  smt::get_free_symbols(bad_next, varset);

  std::vector<std::pair<smt::Term, smt::Term>> sliced_pairs;
  std::vector<std::pair<smt::Term, smt::Term>> sliced_pairs_input;
  for (const auto & v : varset) {
    // if it is inputvar, put in sliced_pairs, ow. sliced_pairs_input
    auto & vec = actual_statevars_.find(v) == actual_statevars_.end() ? sliced_pairs_input : sliced_pairs;
    auto val = solver_->get_value(v);
    auto sk = v->get_sort()->get_sort_kind();
    assert(sk == smt::BV || sk == smt::BOOL);
    if ( sk == smt::BV ) {
      auto width = v->get_sort()->get_width();
      if (width > 1) {
        for (unsigned idx = 0; idx < width; ++idx) {
          auto sliced_var = solver_->make_term(smt::Op(smt::Extract, idx, idx), v);
          auto sliced_val = solver_->make_term(smt::Op(smt::Extract, idx, idx), val);
          vec.push_back(std::make_pair(sliced_var, sliced_val ));
        }
        continue; // next variable
      } // else
    } // else
    vec.push_back(std::make_pair(v, val));
  } // end for each var
  solver_->pop(); // old values are no longer needed
  SortCube(sliced_pairs, false);
  smt::TermList slice_pair_to_reduce;
  for (const auto & v_val : sliced_pairs)
    slice_pair_to_reduce.push_back(solver_->make_term(smt::Equal, v_val.first, v_val.second));
  for (const auto & v_val : sliced_pairs_input)
   slice_pair_to_reduce.push_back(solver_->make_term(smt::Equal, v_val.first, v_val.second));
  
  // build F/\ not(bad)
  solver_->push();
  // assert_frame(prevFidx);
  disable_all_labels();
  // let's try if s /\ i /\ i' /\ not(bad /\ cons /\ cons' ) work
  auto not_bad = smart_not(smart_and(smt::TermVec({bad_next, all_constraints_})));
  auto res = syntax_analysis::reduce_unsat_core_to_fixedpoint(not_bad, slice_pair_to_reduce, solver_);
  assert(res); // must be unsat
  // we don't even need to push pop twice...
  assert(!slice_pair_to_reduce.empty());
  syntax_analysis::reduce_unsat_core_linear_rev(not_bad, slice_pair_to_reduce, solver_);
  assert(!slice_pair_to_reduce.empty());
  solver_->pop();

  // finally, if no assumptions, remove all inputs
  for (const auto & eq : slice_pair_to_reduce) {
    smt::Term slice_symb;
    smt::Term symb;
    if(eq->get_op().prim_op == smt::PrimOp::Equal) {
      auto lhs = *(eq->begin());
      auto rhs = *(++(eq->begin()));
      auto noslice_lhs = (lhs->get_op().prim_op == smt::PrimOp::Extract) ? *(lhs->begin()) : lhs;
      auto noslice_rhs = (rhs->get_op().prim_op == smt::PrimOp::Extract) ? *(rhs->begin()) : rhs;
      assert(noslice_lhs->is_symbol() || noslice_rhs->is_symbol());
      symb = noslice_lhs->is_symbol() ? noslice_lhs : noslice_rhs;
      slice_symb = noslice_lhs->is_symbol() ? lhs : rhs;
    } else if (eq->get_op().prim_op == smt::PrimOp::Not || eq->get_op().prim_op == smt::PrimOp::BVNot) {
      slice_symb = symb = *(eq->begin());
      symb = (symb->get_op().prim_op == smt::PrimOp::Extract) ? *(symb->begin()) : symb;
      assert(symb->is_symbol());
    } else {
      slice_symb = eq;
      symb = (slice_symb->get_op().prim_op == smt::PrimOp::Extract) ? *(slice_symb->begin()) : slice_symb;
      assert(symb->is_symbol());
    }
    if(!ts_.is_curr_var(symb))
      continue; // definitely remove 

    // I doubt if we need this, rIC3 is not using input
    // But I don't understand why it is OKAY to do so 
    // if you find INV CHECK/ CEX CHECK failure
    // you might use !has_assumptions in the following if-condition
  
    if (  /* !has_assumptions && */ actual_statevars_.find(symb) == actual_statevars_.end() )
      continue; // if no assumptions and symb is actually an input, then remove it
    slicedvars.insert(slice_symb);
    noslicevars.insert(symb);
    eqs.push_back(eq);
  }
  assert(!slicedvars.empty());
  assert(!noslicevars.empty());
  assert(!eqs.empty());


#ifdef DEBUG_IC3_PREDGEN
  std::cout << "After sorting cube:\n";
  unsigned i = 0;
  for (const auto & eq : eqs) {
    std::cout << " " << i++ << ": " << eq->to_string() << "\n";
  }
  std::cout << "------------------\n";
#endif
} // end of get_min_pred

} // end of namespace predgen
