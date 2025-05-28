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
    if( sv->get_sort()->get_sort_kind() == smt::BOOL) {
      initial_aiger.addInput(aig_encoding_counter, sv->to_string().c_str());
      statevar_to_aiglit_map.emplace(sv, aig_encoding_counter);
      initial_lit2term_map.push_back(sv);
      aig_encoding_counter += 2;
      assert(initial_lit2term_map.size() << 1 == aig_encoding_counter);
    } else if ( sv->get_sort()->get_sort_kind() == smt::BV ) {
      auto width = sv->get_sort()->get_width();
      for (unsigned i = 0; i<width; ++i) {
        auto name = sv->to_string()+"["+std::to_string(i)+"]";
        auto term = width == 1 ? sv : solver_->make_term(smt::Op(smt::Extract,i,i),sv);
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
bool IC3ng::extract_bit_from_val(const smt::Term & val) const {
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


bool IC3ng::is_neg(const smt::Term & t, smt::Term & e, bool & neg) const {
  bool is_neg_op = false;
  neg = false;
  if (t->get_op().prim_op == smt::PrimOp::Not || t->get_op().prim_op == smt::PrimOp::BVNot) {
    is_neg_op = true;
    neg = true;
    e = *(t->begin());
  } else if (t->get_op().prim_op == smt::PrimOp::Equal) {
    auto lhs = *(t->begin());
    auto rhs = *(++(t->begin()));
    auto noslice_lhs = (lhs->get_op().prim_op == smt::PrimOp::Extract) ? *(lhs->begin()) : lhs;
    auto noslice_rhs = (rhs->get_op().prim_op == smt::PrimOp::Extract) ? *(rhs->begin()) : rhs;
    assert(noslice_lhs->is_value() || noslice_rhs->is_value());
    auto val = noslice_lhs->is_value() ? lhs : rhs;
    e = noslice_lhs->is_value() ? rhs : lhs;
    neg = extract_neg_from_val(val);
    is_neg_op = true;
  } else
    e = t;
  return is_neg_op;
}

// bool IC3ng::extract_lit(const smt::Term & t, unsigned & lit, smt::Term & e) const {
//   bool neg = false;
//   if (t->get_op().prim_op == smt::PrimOp::Not || t->get_op().prim_op == smt::PrimOp::BVNot) {
//     neg = true;
//     e = *(t->begin());
//   } else if (t->get_op().prim_op == smt::PrimOp::Equal) {
//     auto lhs = *(t->begin());
//     auto rhs = *(++(t->begin()));
//     auto noslice_lhs = (lhs->get_op().prim_op == smt::PrimOp::Extract) ? *(lhs->begin()) : lhs;
//     auto noslice_rhs = (rhs->get_op().prim_op == smt::PrimOp::Extract) ? *(rhs->begin()) : rhs;
//     assert(noslice_lhs->is_value() || noslice_rhs->is_value());
//     auto val = noslice_lhs->is_value() ? lhs : rhs;
//     e = noslice_lhs->is_value() ? rhs : lhs;
//     neg = extract_neg_from_val(val);
//   } else
//     e = t;
//   auto pos = internal_nodes_to_aiglit_map.find(e);
//   if (pos == internal_nodes_to_aiglit_map.end())
//     return false;
//   lit = pos->second;
//   assert(!aiger_cxx::aiger_sign(lit));
//   if (neg)
//     lit = aiger_cxx::aiger_not(lit);
//   return true;
// }

unsigned IC3ng::traverse_eq_build_aiger(
    aiger_cxx::Aiger & aiger,
    const smt::Term & eq
  ) {
  // ==0, ==1
  // term, visited
  std::vector<std::pair<smt::Term, bool>> stack;
  stack.push_back(std::make_pair(eq, false));
  while(!stack.empty()) {
    auto & top = stack.back();
    if (top.second) { // we arrive at the node from bottom up
    
      auto pos = internal_nodes_to_aiglit_map.find(top.first);
      if (pos != internal_nodes_to_aiglit_map.end()) {
        stack.pop_back();
        continue;
      } // else
      smt::Term no_neg;
      bool negated; // is_neg also handle ==1
      if (is_neg(top.first, no_neg, negated)) {
        pos = internal_nodes_to_aiglit_map.find(no_neg);
        assert(pos != internal_nodes_to_aiglit_map.end());
        auto lit = pos->second;
        if (negated)
          lit = aiger_cxx::aiger_not(lit);
        internal_nodes_to_aiglit_map.emplace(top.first, lit);
      } else {
        assert(top.first->get_op().prim_op == smt::PrimOp::And || top.first->get_op().prim_op == smt::PrimOp::BVAnd);
        std::vector<unsigned> and_lit;
        for(auto cpos = top.first->begin(); cpos != top.first->end(); ++cpos) {
          auto res_child_lit = internal_nodes_to_aiglit_map.at(*cpos);
          and_lit.push_back(res_child_lit);
        }
        assert(and_lit.size() == 2);
        unsigned lhs_lit = aiger.nextUnusedLiteral();
        aiger.addAnd(lhs_lit, and_lit[0], and_lit[1]);
        internal_nodes_to_aiglit_map.emplace(no_neg, lhs_lit);
      }
      stack.pop_back();      
    } else { // not visited
      auto pos = internal_nodes_to_aiglit_map.find(top.first);
      if (pos != internal_nodes_to_aiglit_map.end()) {
        stack.pop_back();
        continue;
      } // else
      top.second = true;
      smt::Term no_neg;
      bool negated; // is_neg also handle ==1
      if (is_neg(top.first, no_neg, negated)) {
        stack.push_back(std::make_pair(no_neg, false));
      } else {
        assert(no_neg->get_op().prim_op == smt::PrimOp::And || no_neg->get_op().prim_op == smt::PrimOp::BVAnd);
        for(auto pos = no_neg->begin(); pos != no_neg->end(); ++pos)
          stack.push_back(std::make_pair(*pos, false));
      }
    } // end of if not visited
  } // end of while stack not empty

  unsigned lit = internal_nodes_to_aiglit_map.at(eq);
  return lit;
} // end of traverse_eq_build_aiger

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
  // for (const auto & curr_frame : frames)  {
  const auto & curr_frame = frames.back();
  for (Lemma * l : curr_frame) {
    // just to filter out those from init/constraint
    // TODO: maybe allow sideloaded here?
    if (!l->origin().is_must_block() && !l->origin().is_may_block())
      continue; // actually may block is not in use
    const auto & cube = l->cube();
    std::vector<unsigned> cube_lits;
    for (const auto & eq : cube) {
      cube_lits.push_back(
        traverse_eq_build_aiger(loaded_aiger, eq ));
    }
    assert(!cube_lits.empty());
    // sort cube
    std::sort(cube_lits.begin(), cube_lits.end()); // ascending

    unsigned output_lit = cube_lits[0];
    for (unsigned idx = 1; idx < cube_lits.size(); ++ idx) {
      unsigned rhs1 = cube_lits[idx];
      unsigned lhs_lit = loaded_aiger.nextUnusedLiteral();
      loaded_aiger.addAnd(lhs_lit, output_lit, rhs1);
      output_lit = lhs_lit;
    }
    loaded_aiger.addOutput( output_lit, "" );
  } // foreach lemma in the frame
  // } // foreach frame
  loaded_aiger.writeToFile(aiger_cxx::Mode::Binary, fname );
} // end of dump_clause_to_aiger


void IC3ng::aiger_simulate() {
  #error TODO
  // assert cex->expr,
  // for the input of this aiger
    // if it is a sliced variable, extract its value,
    // otherwise use X value
    // perform ternary simulation
    // for each non-X node, if it is needed, we add its term

  // simulate the aiger based on cex
}

// the output is stored in internal_nodes_to_aiglit_map
void IC3ng::load_aiger_internal_nodes(const std::string & fname) {
  loaded_aiger = aiger_cxx::Aiger(); // clear the old aiger
  auto error = loaded_aiger.readFromFile(fname);
  if (!error.empty())
    throw PonoException("unable to load aiger " + fname);
  // rebuild internal_nodes_to_aiglit_map
  internal_nodes_to_aiglit_map = statevar_to_aiglit_map;
  // build a literal -> term map
  lit2term_map = initial_lit2term_map; // reset to the original 
  loaded_preds_from_aiger_.clear();

  const auto & andgates = loaded_aiger.getAnds();
  for (const auto & andgate : andgates) {
    auto lhs = andgate.lhs;
    assert(!aiger_cxx::aiger_sign(lhs));
    auto varidx = aiger_cxx::aiger_lit2var(lhs);
    assert(varidx == lit2term_map.size());
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
    auto term4aignode = smart_and(smt::TermVec({rhs0_term, rhs1_term}));
    lit2term_map.push_back(term4aignode);
    internal_nodes_to_aiglit_map.emplace(term4aignode, lhs);
    loaded_preds_from_aiger_.push_back(term4aignode);
  }
  #error please check if `internal_nodes_to_aiglit_map` and `lit2term_map` matches the loaded aiger!!!
  // HZ: we don't really care about the clauses
  // no need to rewrite existing ones, because they are equivalent anyway
  // the point is, can we get some useful internal nodes from LS?
} // end of load_aiger_internal_nodes

} // end of namespace pono

