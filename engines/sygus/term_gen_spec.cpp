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
 ** \brief Special Term Generator (from itp's var and from trans 's term))
 **
 ** 
 **/

#include "policy_sat_enum.h"

namespace cosa {

namespace policy_sat_enum {

// only call initially 
void Enumerator::ReplaceTermWithItpVC(uint64_t width, term_table_t & terms) {
  // itp_vars
  terms.reset(term_policy_action_t::ITP_V_C_EQ);
  // first insert vars
  for(const auto & v : itp_info_.itp_vars)
    terms.push_back(std::make_pair(v, btor_var_to_msat_(v)));
  terms.n_vars = terms.terms.size();
  // then consts from syntax
  auto syntax_pos = syntax_struct_.find(width);
  if (syntax_pos != syntax_struct_.end()) {
    
    std::unordered_set<std::string> bool_consts = {"true", "false"};
    std::unordered_set<std::string> bv1_consts = {"#b0", "#b1"};
  
    const std::unordered_set<std::string> & cnsts_set
      = (width == 0) ? bool_consts : (
        (width == 1) ? bv1_consts  : (
        syntax.constants));
    
    for (const auto & c: cnsts_set) {
      terms.terms.push_back(std::make_pair(
        sygus::smt_string_to_const_term(c, solver_),
        sygus::smt_string_to_const_term(c, msat_solver_)
        ));
      terms.term_strings.insert(
        terms.terms.back().first->to_raw_string());
    }
  }
  terms.n_consts_vars = terms.terms.size();  
} // ReplaceTermWithItpVC


// 


void Enumerator::ReplaceTermWithTrans3(uint64_t width, term_table_t & terms, width_new_terms_t & new_terms) {
  // extract that from trans_, also try each's next
  // cache its vars (-- no, you should use cex->var) (per width cex)
  terms.reset(term_policy_action_t::TERM_3_EQ);
  // repopulate its vars
  // if has high level, use high, level, also insert to other term table   (will check other's term_strings, 
  //     and create a width->term map to insert
 
}


} // namespace policy_policy_sat_enum

} // namespace cosa
