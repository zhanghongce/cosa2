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
 ** \brief The Unsat core based Enumerator
 **
 ** 
 **/
 
#pragma once

#include "engines/sygus/ast_knob/var_term_manager.h"

#include <vector>
#include <functional>


namespace cosa {

namespace unsat_enum {


// value for enumeration
struct eval_val { // will always convert to uint64_t, if width < 64
  enum type_t {NUM, STR} type;
  uint64_t nv;
  std::string sv;
  
  eval_val(const std::string & val); // will remove #b0...0 and then decide to convert or not
  // default copy and assignment, and then

  bool operator==(const eval_val &r) const {
    return (type == r.type) && 
      (type != type_t::NUM || nv == r.nv) && 
      (type != type_t::STR || sv == r.sv);
  }

  bool operator<(const eval_val &) const;

  // the first one is always 1....
  // so, if one is shorter, it must be smaller

};

struct eval_val_hash {
  std::size_t operator() (const eval_val & k) const {
    return (k.type == k.NUM ? std::hash<uint64_t>()(k.nv) : std::hash<std::string>()(k.sv));
  }
};


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

class Enumerator {

public:
  typedef std::unordered_map<Model *, PerCexInfo>   cex_term_map_t; // the enumeration position of a cex
  typedef std::function<smt::Term(const smt::Term &)> to_next_t; // ast to next
  //typedef std::function<smt::Term(const smt::Term &)> btor_var_to_msat_t;
  typedef std::function<void(const smt::UnorderedTermSet &, bool)> extract_model_t;
  
protected:
  // btor_var_to_msat_t btor_var_to_msat_;
  // const btor_var_to_msat_var_map_t & btor_var_to_msat_var_map_;
  to_next_t to_next_;
  extract_model_t extract_model_;

  smt::SmtSolver & solver_;
  smt::Term trans_;
  smt::Term init_;
  smt::Term prev_;
  Model * cex_; // the cexs to block
  
  static cex_term_map_t  cex_term_map_;
  
  
  PerCexInfo & per_cex_info_; // per var set info here
  PerCexInfo & setup_cex_info(VarTermManager & var_term_extractor);
  void terms_to_predicates();
  
  smt::Term AssembleCandFromUnsatCore(const smt::Term & base_term, const smt::UnorderedTermSet & unsatcore);
  void DebugPredicates(const smt::UnorderedTermSet & inpreds, const smt::Term & base, const smt::Term & init) ;
  bool check_failed_at_init(const smt::Term & F_and_T) ;

public:
  Enumerator(
    to_next_t to_next_func,
    extract_model_t extract_model_func,
    smt::SmtSolver & btor_solver,
    //smt::SmtSolver & msat_solver,
    const smt::Term & T_btor, const smt::Term & Init_btor, const smt::Term & Fprev_btor,
    Model * cex,
    VarTermManager & var_term_extractor
    );
  
  void TermsDumping() const;

  static void ClearCache();

  void GetNCandidates(smt::TermVec & cands, size_t n) ;
  void GetOneCandidate(const smt::UnorderedTermSet & in, 
    smt::UnorderedTermSet & unsatcore, const smt::Term & base_term, const smt::Term & F_and_T) ;

}; // class Enumerator

} // namespace sat_enum

} // namespace cosa



