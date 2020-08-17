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
 ** \brief The Policy module
 **
 ** 
 **/
 

#include "policy_sat_enum.h"


namespace cosa {

namespace policy_sat_enum {

bool Enumerator::MoreTermPredicateGetPolicy(width_term_policy_table_t &wpt) {
 
  for (auto & width_term_pair : width_term_table_) {
    auto width = width_term_pair.first;
    auto & terms = width_term_pair.second;

    auto nV = terms.n_vars;
    auto nC = terms.n_consts_vars - terms.n_vars;
    auto syntax_pos = syntax_struct_.find(width);
    size_t nUop = 0;
    size_t nBop = 0;
    if (syntax_pos != syntax_struct_.end()) {
      nUop = syntax_pos->second.op_unary.size();
      nBop = syntax_pos->second.op_binary.size();
    }
    
    bool more_terms_succ = false;

    if (terms.term_policy_action == term_policy_action_t::V_C_EQ) {
      // these are delta values (0,1) does not need 0,1
      auto to_lt = width < 2 ? 0 : term_estimator::estimate_predicate_num_delta_V_C_TO_CMP_LT(nV, nC);
      auto to_le = width < 2 ? 0 : term_estimator::estimate_predicate_num_delta_V_C_TO_CMP_LE(nV, nC);
      auto to_op = term_estimator::estimate_predicate_num_delta_V_C_TO_OP(nV, nC, nUop, nBop);

      if (nC > 5) {
        // will first try lt/le
        if ()
      } else {
        // will first try op
      }
      

    } else if (terms.term_policy_action == term_policy_action_t::ITP_V_C_EQ) {
      // see width and estimate <, <= to see if comp, which is fast we go first
      // compute v,c -> op num    /   v,c comp ??
    }
    // after reaching bvcomp see if we .... go that way
    // and see if we go further op
    // if no way to go, term3 and see if we want <, <=, 

    // per width and also specify how much to go

  }
}

} // namespace policy_sat_enum

} // namespace cosa


