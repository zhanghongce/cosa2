/*********************                                                  */
/*! \file indgen.cpp
** \verbatim
** Top contributors (to current version of this file):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2025 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Inductive generalization
**/


#include "utils/logger.h"
#include "engines/ic3ng.h"
#include "engines/ic3ng-support/debug.h"
#include "utils/container_shortcut.h"


namespace pono
{


static size_t TermScoreVar(const smt::Term & t) {
  // remove NOT
  auto e = (t->get_op().prim_op == smt::PrimOp::Not ||
            t->get_op().prim_op == smt::PrimOp::BVNot) ? *(t->begin()): t;
  // if it is just a variable: 0
  // otherwise, slice+width
  unsigned slice = 0;
  if (e->get_op().prim_op == smt::PrimOp::Extract) {
    slice = e->get_op().idx0;
    auto c = *(e->begin());
    slice += c->get_sort()->get_width();
  }
  return slice;
}

static void SortLemma(smt::TermVec & inout, bool descending) {
  // we don't want to sort the term themselves
  // we don't want to invoke TermScore function more than once for a term
  std::vector<std::pair<size_t,size_t>> complexity_index_pair;
  size_t idx = 0;
  for (const auto & t : inout) {
    complexity_index_pair.push_back({ TermScoreVar(t) ,idx});
    ++ idx;
  }
  // sort in descending order (the `first` is compared first), so term-index with 
  // the highest score will rank first
  if(descending) // from greater to smaller
    std::sort(complexity_index_pair.begin(), complexity_index_pair.end(), std::greater<>());
  else // from smaller to greater
    std::sort(complexity_index_pair.begin(), complexity_index_pair.end(), std::less<>());
  // now map back to termvec
  smt::TermVec sorted_term;
  for (const auto & cpl_idx_pair : complexity_index_pair) {
    sorted_term.push_back(inout.at(cpl_idx_pair.second));
  }
  inout.swap(sorted_term); // this is the same as inout = sorted_term, but faster
} // end of SortLemma


#if 0
// ( ( not(S) /\ F /\ T ) \/ init_prime ) /\ ( cube' )
//   cube (v[0]=1 /\ v[1]=0 /\ ...)
void IC3ng::inductive_generalization(unsigned fidx, Model *cex, LCexOrigin origin) {

  auto F = get_frame_formula(fidx);
  auto T = get_trans_for_vars(cex->get_varset_unslice()); // find the update F for vars in set...
  auto F_and_T = smart_and<smt::TermVec>({F,T});


  smt::TermVec all_conjs = cex->to_expr_conj();
  // HZ: TODO a better way is to check, if the vars are appearing too often
  // if so, we extend the predicates
  // otherwise, we will not use word-level preds


  // TODO: sort conjs
  SortLemma(all_conjs, options_.ic3base_sort_lemma_descending);


  auto npred = extend_predicates(cex, all_conjs); // IC3INN
  //  conjs.erase(conjs.begin()+1);
  //  TODO: you may need more than 1 round (if not word-level pred used)
  smt::UnorderedTermSet pred_vars, pred_vars_nxt;
  for (size_t idx = 0; idx < npred; ++ idx) {
    smt::get_free_symbols( all_conjs.at(idx), pred_vars );
  }
  for (const auto & v : pred_vars)
    pred_vars_nxt.emplace(ts_.next(v));


#ifdef DEBUG_IC3_INDGEN
  std::cout << "After sorting:\n";
  unsigned i = 0;
  for (const auto & e : all_conjs)
    std::cout << " " << i++ << ": " << e->to_string() << "\n";
  std::cout << "------------------\n";
#endif

  assert(!all_conjs.empty());
  if (all_conjs.size() == 1) { // a short-cut
    auto cex_expr = smart_not(smart_and(all_conjs));
    D(3,"[ig] F{} get lemma:{}", fidx+1, cex_expr->to_string());
    auto lemma = new_lemma(cex_expr, cex, origin, std::move(all_conjs)); // it does not matter whether we have the NOT 
    add_lemma_to_frame(lemma,fidx+1);
    return;
  }

  // Next, if we have more than 1 clause...
  smt::TermVec allconjs_nxt;
  std::unordered_map<smt::Term, size_t> conjnxt_to_idx_map; // use this map to identify more easily its index
  for (size_t idx = 0; idx < all_conjs.size(); ++idx) {
    allconjs_nxt.push_back(ts_.next(all_conjs.at(idx)));
    conjnxt_to_idx_map.emplace(allconjs_nxt.back(), idx);
  }
  std::vector<bool> conjs_used(all_conjs.size(), false); // initialized: all un-used

  unsigned max_round = options_.ic3ng_indgen_max_round; // default 3
  if (options_.ic3ng_indgen_multilemma_on_predicates_only && npred == 0)
    max_round = 1; // if we have no predicates, then just one round

  for (unsigned rnd = 0 ; rnd < max_round; ++ rnd) {
    // we start from all_conjs, and generate the conjs and conj_nxt for this round
    smt::TermList conjs_list;
    smt::TermList conjs_nxt;
    for (size_t idx = 0; idx < all_conjs.size(); ++idx) {
      if (!conjs_used[idx]) {
        conjs_list.push_back(all_conjs.at(idx));
        conjs_nxt.push_back(allconjs_nxt.at(idx));
      }
    }
    // we need to test here, if the remaining ones are still good enough to block the CTI
    auto cex_expr = smart_not(smart_and(conjs_list));
    smt::Term base = 
      smart_or<smt::TermVec>(
        {smart_and<smt::TermVec>(  {cex_expr, F_and_T} ) , init_prime_ } );
    solver_->push();
    disable_all_labels();
    bool succ = syntax_analysis::reduce_unsat_core_to_fixedpoint(base, conjs_nxt, solver_);
    solver_->pop();
    if (!succ) { // the remaining ones are not enough, we should stop
      D(3,"[ig] not enough pred remained, skipped @ rnd{}.", rnd);
      assert(rnd != 0); // you should never fail at the first attempt!
      break;
    }

    conjs_list.clear(); // update conjs_list
    for (const auto & c : conjs_nxt)
      conjs_list.push_back(all_conjs.at(conjnxt_to_idx_map.at(c)));

    if (conjs_nxt.size() > 1) {
      solver_->push();
      disable_all_labels();
      // syntax_analysis::reduce_unsat_core_linear_rev(base, conjs_nxt, solver_);
      reduce_unsat_core_linear_backwards(F_and_T, conjs_list, conjs_nxt);
      solver_->pop();
    }

    // strategy #2: find those variables in provided lemmas, and try to through them away
    bool disabled_any = false;
    for (const auto & cj_nxt : conjs_nxt) {
      auto to_disable_idx = conjnxt_to_idx_map.at(cj_nxt);
      if (to_disable_idx < npred) continue; // no need to disable those external preds
      smt::UnorderedTermSet cj_vars;
      smt::get_free_symbols(cj_nxt,cj_vars);
      for (const auto & v : cj_vars)
        if (pred_vars_nxt.find(v) != pred_vars_nxt.end()) {
          conjs_used[to_disable_idx] = true;
          disabled_any = true;
          break;
        }
    }

    // Design Choice here: should we disable all or just one, and which one?
    // strategy #1: using the last one, but is there a better way?
    if (!disabled_any) {
      auto to_disable_idx = conjnxt_to_idx_map.at(conjs_nxt.back());
      conjs_used[to_disable_idx] = true;
    }


#ifdef DEBUG_IC3_INDGEN
    std::cout << rnd << " Kept:\n";
    for (const auto & e : conjs_nxt) {
      std::cout << conjnxt_to_idx_map.at(e) << " : " << e->to_string() << std::endl;
      if (conjnxt_to_idx_map.at(e) < npred)
        std::cout << "Used!\n";
    }
    std::cout << "------------------\n";
#endif

    cex_expr = smart_not(smart_and(conjs_list));
    D(1,"[ig] F{} get lemma size:{}", fidx+1, conjs_list.size());
    D(3,"[ig] F{} get lemma:{}", fidx+1, cex_expr->to_string());
    auto lemma = new_lemma(cex_expr, cex, origin, smt::TermVec(conjs_list.begin(),conjs_list.end()) );
    add_lemma_to_frame(lemma,fidx+1);
  } // end for each round
} // end of inductive_generalization
#endif

// a helper function : the rev version
// it goes from the end to the beginning
void remove_and_move_to_next_backward(smt::TermList & pred_set_prev, smt::TermList::iterator & pred_pos_rev,
  smt::TermList & pred_set, smt::TermList::iterator & pred_pos,
  const smt::UnorderedTermSet & unsatcore) {

  assert(pred_set.size() == pred_set_prev.size());
  assert(pred_pos != pred_set.end());
  assert(pred_pos_rev != pred_set_prev.end());

  auto pred_iter = pred_set.end(); // pred_pos;
  auto pred_pos_new = pred_set.end();

  auto pred_iter_prev = pred_set_prev.end();
  auto pred_pos_new_prev = pred_set_prev.end();

  pred_pos_new--;
  pred_pos_new_prev--;

  bool reached = false;
  bool next_pos_found = false;

  while( pred_iter != pred_set.begin() ) {
    pred_iter--;
    pred_iter_prev--;
    
    if (!reached && pred_iter == pred_pos) {
      reached = true;
    }
    
    if (unsatcore.find(*pred_iter) == unsatcore.end()) {
      // assert (reached); OK, this can happen.
      // it is possible that a previously unremoveable one now is removable
      // because the pre-set is also changed (it becomes more restrictive
      // after you remove another one)
      pred_iter = pred_set.erase(pred_iter);
      pred_iter_prev = pred_set_prev.erase(pred_iter_prev);
    } else {
      if (reached && ! next_pos_found) {
        pred_pos_new = pred_iter;
        pred_pos_new ++;

        pred_pos_new_prev = pred_iter_prev;
        pred_pos_new_prev++;

        next_pos_found = true;
      }
    }
  } // end of while

  assert(reached);
  if (! next_pos_found) {
    assert (pred_iter == pred_set.begin());
    assert (pred_iter_prev == pred_set_prev.begin());

    pred_pos_new = pred_iter;
    pred_pos_new_prev = pred_iter_prev;
  }
  pred_pos = pred_pos_new;
  pred_pos_rev = pred_pos_new_prev;
} // remove_and_move_to_next

// 1. check if init /\ (conjs-removed)  is unsat
// 2. if so, check ( ( not(conjs-removed) /\ F /\ T ) /\ ( conjs-removed )' is unsat?
void IC3ng::reduce_unsat_core_linear_backwards(const smt::Term & F_and_T,
  smt::TermList &conjs, smt::TermList & conjs_nxt) {
  
  auto to_remove_pos_prev = conjs.end(); // prev means on the predicates with current version of variables
  auto to_remove_pos_next = conjs_nxt.end(); // next means over the predicates with the next version of variables

  assert(conjs.size() == conjs_nxt.size());

  while(to_remove_pos_prev != conjs.begin()) {
    to_remove_pos_prev--; // firstly, point to the last one
    to_remove_pos_next--; // synchronously point to the corresponding one in the next set

    if (conjs.size() == 1) // no need to reduce anymore, if we only have 1 left
      continue;

    smt::Term term_to_remove = *to_remove_pos_prev;
    smt::Term term_to_remove_next = *to_remove_pos_next;

    auto pos_after_conj = conjs.erase(to_remove_pos_prev); // let's try to remove it
    auto pos_after_conj_nxt = conjs_nxt.erase(to_remove_pos_next);
    // the return value is the pointer to the element after the removed one

    auto cex_expr = smart_not(smart_and(conjs));
    auto base = smart_or<smt::TermVec>(
        { smart_and<smt::TermVec>(  {cex_expr, F_and_T} ) , init_prime_ } );

    solver_->push();
    disable_all_labels();
    solver_->assert_formula(base);
    smt::Result r = solver_->check_sat_assuming_list(conjs_nxt);

    to_remove_pos_prev = conjs.insert(pos_after_conj, term_to_remove); // will insert before pos_after_conj
    to_remove_pos_next = conjs_nxt.insert(pos_after_conj_nxt, term_to_remove_next);
    if (r.is_sat()) {
      solver_->pop();
      continue;
    } // else { // if unsat, we can remove
    smt::UnorderedTermSet core_set;
    solver_->get_unsat_assumptions(core_set);
    // below function will update assumption_list and to_remove_pos
    remove_and_move_to_next_backward(conjs, to_remove_pos_prev, conjs_nxt, to_remove_pos_next, core_set);
    solver_->pop();
  } // end of while
}

// ---------------------- BELOW is another method --------------------------- //

// remove from conjs_list those elements that are not in (core1 union core2)
// and also remove its next state version from conjs_next
static void update_list_based_on_core(smt::TermList & conjs_list, smt::TermList & conjs_next, 
  // core1 and core1 are all on current variables
  const smt::TermList & core1, const smt::TermList & core2)
{
  smt::UnorderedTermSet core(core1.begin(), core1.end());
  for (const auto & t : core2)
    core.emplace(t);

  for (auto pos = conjs_list.begin(), pos_nxt = conjs_next.begin(); pos != conjs_list.end(); ) {
    if (core.find(*pos) == core.end()) {
      // can remove it
      pos = conjs_list.erase(pos);
      pos_nxt = conjs_next.erase(pos_nxt);
    } else {
      ++ pos; ++pos_nxt;
    }
  }
}

bool IC3ng::ic3_down(smt::TermList & conjs_list, smt::TermList & conjs_next, 
    const smt::Term & Trans, unsigned fidx,
    std::unordered_map<smt::Term, size_t> & conjnxt_to_idx_map, smt::TermVec all_conjs_curr) 
{  // now let's check (1) init /\ conj_list 
  while(true) {
    solver_->push();
    assert_init();
    auto res = solver_->check_sat_assuming_list(conjs_list);
    solver_->pop();
    if (res.is_sat()) { // if sat
      return false;
    }
    // now let's check (2)  F(i) /\ not(conjs_list) /\ Trans /\ conjs_nxt
    solver_->push();
    assert_frame(fidx);
    solver_->assert_formula(smart_not(smart_and(conjs_list)));
    solver_->assert_formula(Trans);
    res = solver_->check_sat_assuming_list(conjs_next);
    if (res.is_unsat()) {
      // yes, we can remove, 
      smt::UnorderedTermSet unsatcore_next;
      solver_->get_unsat_assumptions(unsatcore_next); // unsatcore_next would be a subset of conjs_nxt
      solver_->pop();
      // map cores to curr state version
      smt::TermList unsatcore_curr;
      for (const auto & t : unsatcore_next) // map to curr
        unsatcore_curr.push_back(all_conjs_curr.at(conjnxt_to_idx_map.at(t)));
      // now we need to make sure, this has no intersection with init 
      // (init /\ the remaining conjs)  should be unsat
      solver_->push();
      assert_init();
      auto init_check = solver_->check_sat_assuming_list(unsatcore_curr);
      solver_->pop();
      if (init_check.is_sat()) {
        // we are removing too many elements
        // let's fix this problem
        //      init /\ the remaining conjs /\ all conjs       is still unsat
        // reduce those in (all conjs)
        smt::TermList reduced_cube = conjs_list; // make a copy
        solver_->push();
        assert_init();
        for (const auto & t : unsatcore_curr)
          solver_->assert_formula(t);
        // reduce the elements in reduced_cube
        bool is_unsat = syntax_analysis::reduce_unsat_core_to_fixedpoint(solver_true_, reduced_cube, solver_);
        assert(is_unsat);
        syntax_analysis::reduce_unsat_core_linear_rev(solver_true_, reduced_cube, solver_);
        assert(!reduced_cube.empty());
        solver_->pop();
        // update conjs_list and conjs_nxt
        // only keep those in `unsatcore_curr union reduced_cube`
        update_list_based_on_core(conjs_list, conjs_next, unsatcore_curr, reduced_cube);
        return true;
      } // end of 'amending core'
      // if we don't need amendment, then, we just update
      // only keep those in `unsatcore_curr`
      update_list_based_on_core(conjs_list, conjs_next, unsatcore_curr, {});
      return true;
    } else {
      // (2)  F(i) /\ not(conjs_list) /\ Trans /\ conjs_nxt is SAT
      // then we extract the SAT assignment and update conjs_list and conjs_next
      for (auto pos = conjs_list.begin(), pos_next = conjs_next.begin();
          pos != conjs_list.end(); ) {
        const auto & t = *pos;
        auto val = solver_->get_value(t);
        if (extract_bit_from_val(val) != true ) { 
          // remove this
          pos = conjs_list.erase(pos);
          pos_next = conjs_next.erase(pos_next);
        } else {
          ++ pos; ++ pos_next;
        }
      } // this is q = q |_| s
      solver_->pop();
    } // and then try again
  } // end of while (true)
} // end of ic3_down


// ( ( not(S) /\ F /\ T ) \/ init_prime ) /\ ( cube' )
//   cube (v[0]=1 /\ v[1]=0 /\ ...)
void IC3ng::inductive_generalization_mic(unsigned fidx, Model *cex, LCexOrigin origin) {

  // auto F = get_frame_formula(fidx);
  auto Trans = get_trans_for_vars(cex->get_varset_unslice()); // find the update F for vars in set...
  // auto F_and_T = smart_and<smt::TermVec>({F,T});


  smt::TermVec all_conjs = cex->to_expr_conj();
  // HZ: TODO a better way is to check, if the vars are appearing too often
  // if so, we extend the predicates
  // otherwise, we will not use word-level preds


  // TODO: sort conjs
  SortLemma(all_conjs, options_.ic3base_sort_lemma_descending);


  auto npred = extend_predicates(cex, all_conjs); // IC3INN

#ifdef DEBUG_IC3_INDGEN
  std::cout << "# pred: " << npred << std::endl;
  std::cout << "After sorting:\n";
  unsigned i = 0;
  for (const auto & e : all_conjs)
    std::cout << " " << i++ << ": " << e->to_string() << "\n";
  std::cout << "------------------\n";
#endif
  

  assert(!all_conjs.empty());
  if (all_conjs.size() == 1) { // a short-cut
    auto cex_expr = smart_not(smart_and(all_conjs));
    D(3,"[ig] F{} get lemma:{}", fidx+1, cex_expr->to_string());
    auto lemma = new_lemma(cex_expr, cex, origin, std::move(all_conjs)); // it does not matter whether we have the NOT 
    add_lemma_to_frame(lemma,fidx+1);
    return;
  }

  // Next, if we have more than 1 clause...
  smt::TermVec allconjs_nxt;
  std::unordered_map<smt::Term, size_t> conjnxt_to_idx_map; // use this map to identify more easily its index
  for (size_t idx = 0; idx < all_conjs.size(); ++idx) {
    allconjs_nxt.push_back(ts_.next(all_conjs.at(idx)));
    conjnxt_to_idx_map.emplace(allconjs_nxt.back(), idx);
  }
  // we start from all_conjs, and generate the conjs and conj_nxt for this round
  smt::TermList conjs_list;
  smt::TermList conjs_nxt;
  for (size_t idx = 0; idx < all_conjs.size(); ++idx) {
    //if (!conjs_used[idx]) {
      conjs_list.push_back(all_conjs.at(idx));
      conjs_nxt.push_back(allconjs_nxt.at(idx));
    //}
  }
  // from the last element, try to remove from conjs_list and conjs_nxt and check
  // (1) init /\ conj_list             (is unsat)   (disable all)
  // (2) F(i) /\ not(conjs_list) /\ Trans /\ conjs_nxt   (is unsat)
  //          if unsat, use UNSAT core to further reduce and return
  //          if not, extract sat-value of elements in conjs_list, if the literal is not true, then remove it
  //             and try again
  //     Use a `keep` to record those you cannot remove anyway

  auto to_remove_pos_curr_term = conjs_list.end(); // prev means on the predicates with current version of variables
  auto to_remove_pos_next_term = conjs_nxt.end(); // next means over the predicates with the next version of variables

  while (to_remove_pos_curr_term != conjs_list.begin()) {
    to_remove_pos_curr_term --; to_remove_pos_next_term --;

    if (conjs_list.size() == 1)
      continue; // no need to reduce anymore, if we only have 1 left

    smt::Term term_to_remove_curr = *to_remove_pos_curr_term;
    smt::Term term_to_remove_next = *to_remove_pos_next_term;

    auto pos_after_conj_curr = conjs_list.erase(to_remove_pos_curr_term); // let's try to remove it
    auto pos_after_conj_next = conjs_nxt.erase(to_remove_pos_next_term);
    
    auto conjs_list_copy = conjs_list;
    auto conjs_nxt_copy  = conjs_nxt;

    bool res = ic3_down(conjs_list_copy, conjs_nxt_copy, Trans, fidx, conjnxt_to_idx_map, all_conjs);

    to_remove_pos_curr_term = conjs_list.insert(pos_after_conj_curr, term_to_remove_curr); // will insert before pos_after_conj
    to_remove_pos_next_term = conjs_nxt.insert(pos_after_conj_next, term_to_remove_next);
    if (!res) {
      continue;
    } else {
      // update conjs_list, conjs_nxt_copy, and to_remove_pos_curr_term, term_to_remove_next
      assert(conjs_list_copy.size() == conjs_nxt_copy.size());
      smt::UnorderedTermSet remaining(conjs_nxt_copy.begin(), conjs_nxt_copy.end());
      remove_and_move_to_next_backward(conjs_list, to_remove_pos_curr_term, conjs_nxt, to_remove_pos_next_term, remaining);
      }
  } // end of while (going backwards through the constraints)

#ifdef DEBUG_IC3_INDGEN
  std::cout << " Kept:\n";
  for (const auto & e : conjs_nxt) {
    std::cout << conjnxt_to_idx_map.at(e) << " : " << e->to_string() << std::endl;
    if (conjnxt_to_idx_map.at(e) < npred)
      std::cout << "Used!\n";
  }
  std::cout << "------------------\n";

  for (const auto & e : conjs_nxt) {
    if (conjnxt_to_idx_map.at(e) < npred) {
      std::cout << "[IG] Pred is used!\n";
      break;
    }
  }
#endif

  auto cex_expr = smart_not(smart_and(conjs_list));
  D(1,"[ig] F{} get lemma size:{}", fidx+1, conjs_list.size());
  D(3,"[ig] F{} get lemma:{}", fidx+1, cex_expr->to_string());
  auto lemma = new_lemma(cex_expr, cex, origin, smt::TermVec(conjs_list.begin(),conjs_list.end()) );
  add_lemma_to_frame(lemma,fidx+1);
    
} // end of inductive_generalization_mic


} // end of namespace pono
