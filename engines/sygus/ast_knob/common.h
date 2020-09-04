/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Some type defs, shared by apdr/enum/learner
 **
 ** 
 **/
 
#pragma once

#include "engines/sygus/partial_model.h"

namespace cosa {

namespace unsat_enum {

typedef std::function<smt::Term(const smt::Term &)> to_next_t; // ast to next


struct PerWidthInfo {
 std::vector<smt::Term> terms;
 std::vector<smt::Term> constants;
};

class VarTermManager;

struct PerVarsetInfo {
  // --- type definition --- //
  typedef std::map<unsigned, smt::TermVec> width_term_map_t;
  struct state_t  {
    enum stage_t {EMPTY, WPARTIAL, WALL, FROMCEX} stage;
    unsigned partial_width_done;
    // you don't need to cache those constants, already in width_to_constants_
    state_t() : stage(EMPTY), partial_width_done(0) {}
    explicit state_t(stage_t s) : stage(s), partial_width_done(0)  {}
  }; // class state_t

  std::map<unsigned, PerWidthInfo> terms;
  std::unordered_set<std::string> terms_strings;
  // --- more info --- //

  PerVarsetInfo() {}
  PerVarsetInfo(state_t::stage_t s, const width_term_map_t &init_terms):
    state(s), terms_buffer(init_terms) {}

protected: // let's restrict the accesses to these fields
  friend class VarTermManager; 
  state_t state;
  width_term_map_t terms_buffer; // will be copied from term_walker
}; // class PerVarsetInfo


struct PerCexInfo {
  struct term_const_num{
    unsigned term_num;
    unsigned const_num;
    term_const_num(): term_num(0), const_num(0) {}
  };

  std::unordered_map<smt::Term,eval_val> terms_val_under_cex;
  std::vector<smt::Term> predicates_nxt;
  std::unordered_map<smt::Term, smt::Term> pred_next_to_pred_curr;
  const PerVarsetInfo & varset_info; // reference from VarTermManager

  std::map<unsigned, term_const_num> prev_per_width_term_num;
  PerCexInfo(const PerVarsetInfo & info) : varset_info(info) {}
};

typedef std::unordered_map<Model *, PerCexInfo>   cex_term_map_t; // the enumeration position of a cex
  

} // namespace sat_enum

} // namespace cosa




