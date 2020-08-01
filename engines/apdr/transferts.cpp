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
 ** \brief A dummy transition system to hold msat ts
 **
 **
 **/
 
#include "transferts.h"
#include "sort_convert_util.h"

#include <cassert>

namespace cosa {

TransferredTransitionSystem::TransferredTransitionSystem(
    const TransitionSystem & ts, 
     //smt::SmtSolver from_solver,
     smt::SmtSolver & to_solver,
     smt::TermTranslator & translator
  ) : TransitionSystem(to_solver),
      //from_solver_(from_solver),
      translater_(translator)
{
  // okay now we do the translation
  // 1. translate states/inputs
  for (const auto & s : ts.states()) {
    auto local_s = translater_.transfer_term(s, true);
    assert (local_s->get_sort()->get_sort_kind() == smt::SortKind::BV);
    states_.insert( local_s );
    symbol_map_ex2in.emplace( s, local_s );
    symbol_map_in2ex.emplace( local_s, s );
  }

  for (const auto & v : ts.inputs()) {
    auto local_v = translater_.transfer_term(v, true);
    assert (local_v->get_sort()->get_sort_kind() == smt::SortKind::BV);
    inputs_.insert( local_v );
    symbol_map_ex2in.emplace( v, local_v );
    symbol_map_in2ex.emplace( local_v, v );
  }

  for (const auto & v : ts.next_states()) {
    auto local_v = translater_.transfer_term(v, true);
    assert (local_v->get_sort()->get_sort_kind() == smt::SortKind::BV);
    next_states_.insert( local_v );
    symbol_map_ex2in.emplace( v, local_v );
    symbol_map_in2ex.emplace( local_v, v );
  }

  for (const auto & v : ts.symbols()) {
    symbols_.emplace( v.first, translater_.transfer_term(v.second, false) );
  }


  for (const auto & v_vp_pair : ts.next_map() ) {
    next_map_.emplace(
      translater_.transfer_term(v_vp_pair.first, false),
      translater_.transfer_term(v_vp_pair.second, false)
    );
  }

  for (const auto & vp_v_pair : ts.curr_map() ) {
    curr_map_.emplace(
      translater_.transfer_term(vp_v_pair.first, false),
      translater_.transfer_term(vp_v_pair.second, false)
    );
  }

  for (const auto & n_t_pair : ts.named_terms() ) {
    named_terms_.emplace(
      n_t_pair.first,
      translater_.transfer_term(n_t_pair.second, false)
    );
  }


  for (const auto & v_nxt_pair : ts.state_updates() ) {
    state_updates_.emplace(
      translater_.transfer_term(v_nxt_pair.first, false),
      bool_to_bv_msat(translater_.transfer_term(v_nxt_pair.second, false), to_solver)
    );
  }

  for (const auto & vp_nxt_pair : ts.nxt_state_updates() ) {
    nxt_state_updates_.emplace(
      translater_.transfer_term(vp_nxt_pair.first, false),
      bool_to_bv_msat(translater_.transfer_term(vp_nxt_pair.second, false), to_solver)
    );
  }

  init_ = bv_to_bool_msat(translater_.transfer_term(ts.init(), false), to_solver);
  trans_ = bv_to_bool_msat(translater_.transfer_term(ts.trans(), false), to_solver);
  constraint_ =  bv_to_bool_msat(translater_.transfer_term(ts.constraint(), false), to_solver);

} // end of constructor

void TransferredTransitionSystem::setup_reverse_translator(smt::TermTranslator & rtrans) const {
  auto & cache = rtrans.get_cache();
  // in2ex map is needed
  for (const auto & in2ex : symbol_map_in2ex) {
    auto res = cache.insert(in2ex);
    assert (res.second); // assert the insertion is sucessful
  }
} // setup_reverse_translator


} // namespace cosa
 
