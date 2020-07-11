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
 ** \brief The Enumerator
 **
 ** 
 **/

#pragma once

#include "syntax.h"
#include "partial_model.h"

#include "smt-switch/smt.h"

#include <vector>
#include <functional>

namespace cosa {

namespace sygus_enum {

struct enum_status {
  std::vector<smt::Term> predicate_list_btor; // already predicates
  std::vector<smt::Term> predicate_list_msat; // how many in conjunctions and each pos
  
  uint64_t prev_predicate_num;
  uint64_t prev_conjunction_depth;

  uint64_t curr_predicate_num;
  uint64_t curr_conjunction_depth;
  
  std::vector<uint64_t>  looping_indices; // its width tells us how many level it is now
  // will need to rewind once list has expanded

  enum_status() : 
    prev_predicate_num(0), prev_conjunction_depth(0), 
    curr_predicate_num(0), curr_conjunction_depth(0),
    looping_indices({0}) { }

  smt::Term GetCandidateBtor(smt::SmtSolver & btor) const; // based on looping_indices
  smt::Term GetCandidateMsat(smt::SmtSolver & msat) const;
  
  bool is_curr_round_finished() const; // compare looping_indices and curr_predicate_num and curr_conjunction_depth
  void looping_sanity_check() const;
  bool skip_current_idx() const;

  bool is_uninit() const;
  void init(uint64_t init_conj_depth);
  void step();
  void increase_conjunction_depth();
  void increase_predicate_num();
  void increase_both_conjunction_depth_and_predicate_num();

  void dump() const;
};

// Methods:
// 1a. expand pedicate list (must be done if looping_indices reaches current_looping_capacity)
//   : add new predicates and prev_looping_capacity <- current_looping_capacity
//     by adding more terms and add more `term comp term` to predicate
// 1b. one more level of conjunctions

// 2. loop to next indices: use prev_looping_capacity to skip

// get candidate_btor , get_candidate_msat

struct term_table_t {
  std::vector<std::pair<smt::Term, smt::Term>> terms;
  std::unordered_set<std::string> consts_string; // to help eliminate redundant constants
  uint64_t n_vars;    // 0 --> n_vars - 1
  uint64_t n_consts_vars;  // n_vars --> n_vars + n_consts -1 
  uint64_t prev_unary_pointer;
  uint64_t prev_binary_pointer;
  uint64_t prev_ternary_pointer_same_width;
  uint64_t prev_ternary_pointer_bool;
  uint64_t prev_comp_pointer;
  term_table_t() : n_vars(0), n_consts_vars(0), 
    prev_unary_pointer(0), prev_binary_pointer(0),
    prev_ternary_pointer_same_width(0), prev_ternary_pointer_bool(0),
    prev_comp_pointer(0) {}
};


class Enumerator {

public:
  typedef std::unordered_map<smt::Term, enum_status> prop_pos_buf_t; // of a property
  typedef std::unordered_map<Model *, enum_status>   cex_pos_buf_t; // the enumeration position of a cex
  typedef std::unordered_map<uint64_t,  // width -> //(btor_term ,  msat_term)
    term_table_t> 
    width_term_table_t;
  typedef std::unordered_map<smt::Term, width_term_table_t> prop_term_map_t; // of a property
  typedef std::unordered_map<Model *, width_term_table_t>   cex_term_map_t; // the enumeration position of a cex
  // typedef std::unordered_map<smt::Term, smt::Term>  btor_var_to_msat_var_map_t;
  typedef std::function<smt::Term(const smt::Term &)> to_next_t; // ast to next
  typedef std::function<smt::Term(const smt::Term &)> btor_var_to_msat_t;

protected:
  btor_var_to_msat_t btor_var_to_msat_;
  // const btor_var_to_msat_var_map_t & btor_var_to_msat_var_map_;
  to_next_t to_next_;
  smt::SmtSolver & solver_;
  smt::SmtSolver & msat_solver_;
  smt::Term trans_;
  smt::Term init_;
  smt::Term prev_;
  std::vector<Model *> cexs_;
  std::vector<Model *> facts_;  
  smt::Term prop_;
  const sygus::SyntaxStructure & syntax_;  
  const sygus::SyntaxStructure::SyntaxT & syntax_struct_;
  // do you need the keep vars? no I don't think so.
  
  static prop_pos_buf_t prop_enum_buf_;
  static cex_pos_buf_t  cex_enum_buf_;

  static prop_term_map_t prop_term_map_;
  static cex_term_map_t  cex_term_map_;
  
  // Terms to predicates: initial and later
  void PopulatePredicateListsWithTermsIncr(); // Level 1

  
  
  bool is_valid(const smt::Term & e);
  bool a_implies_b(const smt::Term & a, const smt::Term & b);
  
  const bool use_cex_;
  width_term_table_t & width_term_table_; // will update it
  width_term_table_t & SetupInitTermList();

  enum_status & enum_status_;
  std::vector<smt::Term> & predicate_list_btor_; // how many in conjunctions and each pos
  std::vector<smt::Term> & predicate_list_msat_; // how many in conjunctions and each pos
  enum_status & SetUpEnumStatus();

  void PopulateTermTableWithConstants(width_term_table_t & table); //  initial population of tables 
  void PopulateTermTableWithUnaryOp(width_term_table_t & table);
  
  void PopulateTermTableWithBinaryOp(width_term_table_t & table);

  void PopulateTermTableWithExtractOpAllWidthVars(width_term_table_t & table); // only one shot?
  void PopulateTermTableWithExtractOpSyntaxDependentVars(width_term_table_t & table); // only one shot?


  // smt::Term btor_var_to_msat(const smt::Term & btor_var) const;

  bool is_predicate_const(const smt::Term & t);
  bool is_predicate_implicable(const smt::Term & t);
  bool init_imply(const smt::Term & c);
  bool F_T_and_P_imply_Pprime(const smt::Term & c);
  bool compatible_w_facts(const smt::Term & c);

  const std::unordered_set<smt::PrimOp> &  GetCompForWidth(uint64_t w);

public:
  Enumerator(
    btor_var_to_msat_t btor_var_to_msat_func,
    to_next_t to_next_func,
    smt::SmtSolver & btor_solver,
    smt::SmtSolver & msat_solver,
    const smt::Term & T_btor, const smt::Term & Init_btor, const smt::Term & Fprev_btor,
    const std::vector<Model *> & cexs, const std::vector<Model *> & facts,
    const smt::Term & prop_btor,
    const sygus::SyntaxStructure & syntax );

  // get predicate**depth 
  uint64_t GetCurrentLevelMaxEffort() const;
  // 
  std::pair<smt::Term, smt::Term> EnumCurrentLevel(uint64_t bnd = 0);

  void MoveToNextLevel(); // more predicates more in conjunction

  // help to get an idea of what the status of enumeration is
  const enum_status & GetEnumStatus() const { return enum_status_; }

  static void PrintWidthTermTable(const width_term_table_t &);
  static void PrintEnumStatus(const enum_status &);

  static void ClearCache();  // must be called before solver destructors!!!

  uint64_t GetCexRefId() const { return (use_cex_? (uint64_t)(cexs_.at(0)) : (uint64_t)(prop_.get())); }
}; // class Enumerator

} // namespace sygus_enum

} // namespace cosa


