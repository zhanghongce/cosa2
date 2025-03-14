/*********************                                                  */
/*! \file ic3bits.cpp
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2025 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief clause dumping to aiger
**/

#include "engines/ic3ng.h"


namespace pono
{

void IC3ng::build_initial_aiger() {
  initial_lit2term_map.push_back(solver_->make_term(false));

  unsigned aig_encoding_counter = 2;
  for (const auto & sv : ts_.statevars()) {
    if( sv->get_sort()->get_sort_kind() == smt::BOOL ) {
      initial_aiger.addInput(aig_encoding_counter, sv->to_string().c_str());
      statevar_to_aiglit_map.emplace(sv, aig_encoding_counter);
      initial_lit2term_map.push_back(sv);
      aig_encoding_counter += 2;
      assert(initial_lit2term_map.size() << 1 == aig_encoding_counter);
    } else if ( sv->get_sort()->get_sort_kind() == smt::BV ) {
      auto width = sv->get_sort()->get_width();
      for (unsigned i = 0; i<width; ++i) {
        auto name = sv->to_string()+"["+std::to_string(i)+"]";
        auto term = solver_->make_term(smt::Op(smt::Extract,i,i),sv);
        initial_aiger.addInput(aig_encoding_counter, name.c_str());
        statevar_to_aiglit_map.emplace(term, aig_encoding_counter);
        aig_encoding_counter += 2;
        initial_lit2term_map.push_back(term);
        assert(initial_lit2term_map.size() << 1 == aig_encoding_counter);
      }
    } else // else not handled
      throw PonoException("Not handling state variable of none BOOL/BV type");
  } // end of all latches

  // the first time we dump, we don't have the loaded_aiger yet
  // so initialize them to be the same
  loaded_aiger = initial_aiger;
  internal_nodes_to_aiglit_map = statevar_to_aiglit_map;
}

// static unsigned term_depth(const smt::Term & t) {
//   unsigned max_depth = 0;
//   for (auto c: *t) {
//     auto depth = term_depth(c);
//     if(depth > max_depth)
//       max_depth = depth;
//   }
//   return max_depth+1;
// }
// static bool term_sort_comparator(const std::pair<smt::Term, smt::Term> & l, const std::pair<smt::Term, smt::Term> & r) {
//   return (term_depth(l.first) < term_depth(r.first));
// }


// a simple helper function
bool IC3ng::extract_bit_from_val(const smt::Term & val) {
  if (val == solver_true_)
    return true;
  if (val == solver_false_)
    return false;
  if (val == solver_0_1)
    return false;
  if (val == solver_1_1)
    return true;
  if (val->get_op().prim_op == smt::Extract) {
    auto slice = val->get_op().idx0;
    assert(slice == val->get_op().idx1);
    auto internal_val = *(val->begin());
    assert(internal_val->is_value());
    auto strval = internal_val->to_string();
    auto ch = strval.at(strval.length()-1-slice);
    assert(ch == '0' || ch == '1');
    return (ch == '0');
  }
  assert(false); // not handled
}

// // a simple helper function
// bool IC3ng::extract_neg_from_val(const smt::Term & val) {
//   if (val == solver_true_)
//     return false;
//   if (val == solver_false_)
//     return true;
//   if (val->get_op().prim_op == smt::Extract) {
//     auto slice = val->get_op().idx0;
//     assert(slice == val->get_op().idx1);
//     auto internal_val = *(val->begin());
//     assert(internal_val->is_value());
//     auto strval = internal_val->to_string();
//     auto ch = strval.at(strval.length()-1-slice);
//     assert(ch == '0' || ch == '1');
//     return (ch == '0');
//   }
//   assert(false); // not handled
// }

// warning: this will change `loaded_aiger` because I don't want
// to make another copy
void IC3ng::dump_clause_to_aiger(const std::string & fname) {
  // start from loaded_aiger, it already have the internal nodes etc.
  // the old output represents the clauses in the previous time
  // some of them are not used since they are not pushed to the next frame
  // let's just clear all and re-insert the clauses of this round
  loaded_aiger.clearOutputs();
  // let's not worry about clean-up logic not in COI, since ABC/Yosys can do this for us

  // work on the last frame
  const auto & last_frame = frames.back();
  for (Lemma * l : last_frame) {
    // just to filter out those from init/constraint
    // TODO: maybe allow sideloaded here?
    if (!l->origin().is_must_block() && !l->origin().is_may_block())
      continue; // actually may block is not in use
    const auto & cube = l->cube();
    // unordered_map to vector
    std::vector<std::pair<smt::Term, smt::Term>> var_val_pairs;
    for (const auto & eq : cube) {
      smt::Term slice_symb;
      smt::Term val;
      if(eq->get_op().prim_op == smt::PrimOp::Equal) {
        auto lhs = *(eq->begin());
        auto rhs = *(++(eq->begin()));
        auto noslice_lhs = (lhs->get_op().prim_op == smt::PrimOp::Extract) ? *(lhs->begin()) : lhs;
        auto noslice_rhs = (rhs->get_op().prim_op == smt::PrimOp::Extract) ? *(rhs->begin()) : rhs;
        assert(noslice_lhs->is_symbol() || noslice_rhs->is_symbol());
        slice_symb = noslice_lhs->is_symbol() ? lhs : rhs;
        val = noslice_lhs->is_symbol() ? rhs : lhs;
      } else if (eq->get_op().prim_op == smt::PrimOp::Not || eq->get_op().prim_op == smt::PrimOp::BVNot) {
        slice_symb = *(eq->begin());
        val = solver_false_;
      } else {
        slice_symb = eq;
        val = solver_true_;
      }
      var_val_pairs.push_back(std::make_pair(slice_symb,val));
    }
    { // let's sort var_val_pairs
      // by creating a index vector, this ensures that we will only call
      // the evaluation function internal_nodes_to_aiglit_map n times
      // otherwise, whenever you compare two elements, you will be calling
      // the comparison twice, which is O(nlogn) times of indexing
      std::vector<std::pair<unsigned, unsigned>> depth2idx_map;
      depth2idx_map.reserve(var_val_pairs.size());
      for (size_t idx = 0; idx < var_val_pairs.size(); ++ idx) {
        depth2idx_map.push_back(std::make_pair(
          internal_nodes_to_aiglit_map.at(var_val_pairs.at(idx).first),
          idx));
      }
      // elements with smaller depth come first
      std::sort(depth2idx_map.begin(), depth2idx_map.end());
      { // and then reconstruct
        decltype(var_val_pairs) var_val_pairs_sorted;
        var_val_pairs_sorted.reserve(var_val_pairs.size());
        for (const auto & p : depth2idx_map)
          var_val_pairs_sorted.push_back(var_val_pairs.at(p.second));
        var_val_pairs.swap(var_val_pairs_sorted);
      }
    } // finish sorting var_val_pairs

    assert(!var_val_pairs.empty());
    unsigned prev_lit;
    { // computing prev_lit
      const auto & [var,val] = *(var_val_pairs.begin());
      unsigned lit = internal_nodes_to_aiglit_map.at(var);
      bool neg = extract_neg_from_val(val);
      // bool neg = (val->to_int() == 0 );
      prev_lit = neg ? aiger_cxx::aiger_not(lit) : lit;
    }
    // in case of a single-literal cube, then this loop will be skipped
    // it should work fine as well
    for (unsigned idx = 1; idx < var_val_pairs.size(); ++ idx) {
      const auto & [var,val] = var_val_pairs.at(idx);
      unsigned lit = internal_nodes_to_aiglit_map.at(var);
      bool neg = extract_neg_from_val(val);
      unsigned this_lit = neg ? aiger_cxx::aiger_not(lit) : lit;
      unsigned lhs_lit = loaded_aiger.nextUnusedLiteral();
      loaded_aiger.addAnd(lhs_lit, prev_lit, this_lit);
      prev_lit = lhs_lit;
    }
    loaded_aiger.addOutput( prev_lit, "" );
  }
  loaded_aiger.writeToFile(aiger_cxx::Mode::Binary, fname );
} // end of dump_clause_to_aiger

void IC3ng::load_aiger_internal_nodes(const std::string & fname) {
  aiger_cxx::Aiger new_aiger;
  auto error = new_aiger.readFromFile(fname);
  if (!error.empty())
    throw PonoException("unable to load aiger " + fname);
  // rebuild internal_nodes_to_aiglit_map
  internal_nodes_to_aiglit_map = statevar_to_aiglit_map;
  // build a literal -> term map
  smt::TermVec lit2term_map = initial_lit2term_map; // lit 0 is for false

  const auto & andgates = new_aiger.getAnds();
  for (const auto & andgate : andgates) {
    auto lhs = andgate.lhs;
    assert(!aiger_cxx::aiger_sign(lhs));
    auto varidx = aiger_cxx::aiger_lit2var(lhs);
    assert(lhs == lit2term_map.size());
    auto rhs0_var  = aiger_cxx::aiger_lit2var(andgate.rhs0);
    bool rhs0_sign = aiger_cxx::aiger_sign(andgate.rhs0);

    auto rhs1_var  = aiger_cxx::aiger_lit2var(andgate.rhs1);
    bool rhs1_sign = aiger_cxx::aiger_sign(andgate.rhs1);

    assert(rhs0_var < lit2term_map.size());
    assert(rhs1_var < lit2term_map.size());

    // need the conversion, o.w. some smtsolvers would complain
    auto rhs0_term = bv_to_bool(lit2term_map.at(rhs0_var));
    if (rhs0_sign)
      rhs0_term = smart_not(rhs0_term);

    auto rhs1_term = bv_to_bool(lit2term_map.at(rhs1_var));
    if (rhs1_sign)
      rhs1_term = smart_not(rhs1_term);
    lit2term_map.push_back(smart_and(smt::TermVec({rhs0_term, rhs1_term})));
  }
  // HZ: we don't really care about the clauses
  // no need to rewrite existing ones, because they are equivalent anyway
  // the point is, can we get some useful internal nodes from LS?
} // end of load_aiger_internal_nodes

} // end of namespace pono

