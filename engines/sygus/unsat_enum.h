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
#include "ast_knob/common.h"

#include <vector>
#include <functional>
#include <list>


namespace cosa {

namespace unsat_enum {

class Enumerator {

public:
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
  
  // I'm a bit lazy to write template
  smt::Term AssembleCandFromUnsatCore(const smt::Term & base_term, const smt::UnorderedTermSet & unsatcore);
  smt::Term AssembleCandFromUnsatCore(const smt::Term & base_term, const std::list<smt::Term> & unsatcore);
  void DebugPredicates(const smt::TermVec & inpreds, const smt::Term & base, const smt::Term & init, bool rm_pre) ;
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

  static void ClearCache() {  cex_term_map_.clear(); }
  static cex_term_map_t & GetCexToPreCexInfoMap() { return cex_term_map_; }

  void GetOneCandidate(smt::TermVec & cands, bool iterative_reduction, bool mus_traverse_reduction);

  //void GetNCandidates(smt::TermVec & cands, size_t n) ;

  //void GetNCandidatesRemoveInPrev(smt::TermVec & cands, size_t n) ;

  bool CheckPrepointNowHasPred(Model * m);

protected:
  // true means still unsat
  bool GetInitialUnsatCore(const smt::Term & base_term, const smt::Term & F_and_T, 
    smt::UnorderedTermSet & initial_core);

  std::list<smt::Term>::iterator GetUnsatCoreWithout(const smt::Term & base_term, 
    std::list<smt::Term> & pred_sets, std::list<smt::Term>::iterator pred_pos, 
    /*output*/ smt::UnorderedTermSet & unsatcore );

  void CheckAndRemove(
    std::list<smt::Term> & pred_sets, std::list<smt::Term>::iterator & pred_pos,
    std::list<unsigned> & pred_scores, std::list<unsigned>::iterator & score_pos, 
    const smt::UnorderedTermSet & unsatcore);

  //void GetOneCandidate(const smt::UnorderedTermSet & in, 
  //  smt::UnorderedTermSet & unsatcore, const smt::Term & base_term, const smt::Term & F_and_T, bool first_check) ;
  //smt::Term GetOneCandidateRemoveInPrev(const smt::UnorderedTermSet & in, 
  //  smt::UnorderedTermSet & unsatcore, const smt::Term & F_and_T, bool first_check) ;

  bool CheckPredDisjFailInit();

  //template <class T> smt::Term ANDN_pre(const T & prime_p);

  // for iterative core reduction
  void MinimizeUnsatCore(const smt::Term & base_term,
    const smt::UnorderedTermSet & core_in, smt::UnorderedTermSet & core_out);
  

private:
  // debug purpose
  std::unordered_map<smt::Term, unsigned> pred_to_numbers;
  void DebugRegAllpred(const std::list<smt::Term> & inpreds, const std::list<unsigned> & scores);
  void DebugRegSelRemove(const smt::Term & sel, const std::string & action);
  void DebugRegResult(const std::list<smt::Term> & inpreds);

}; // class Enumerator

} // namespace sat_enum

} // namespace cosa



