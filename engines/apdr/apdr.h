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
 ** \brief APDR header
 **
 ** 
 **/
 
#pragma once

#include "../sygus/partial_model.h"
#include "../prover.h"

#include "lemma.h"

namespace cosa {


// a buffer of frame of lemmas
// use to commit change all at 
// once
class FrameCache {
protected:
  std::unordered_map<unsigned, std::vector<Lemma *>> frames;
  smt::SmtSolver & btor_;
  smt::SmtSolver & msat_;
public:
  FrameCache (smt::SmtSolver & btor, smt::SmtSolver & msat);

  void _add_lemma(Lemma * lemma, unsigned fidx);
  void _add_pushed_lemma(Lemma * lemma, unsigned start, unsigned end);

  bool has_lemma_at_frame(unsigned fidx) const;
  smt::Term conjoin_frame_for_props_btor(unsigned fidx);
  smt::Term conjoin_frame_for_props_msat(unsigned fidx);
}; // framecache


/*
  Although inherited from Prover, I don't want to use the unroller,
  because we are not unrolling. So it is just for interface.
  And I hope "witness" & "prove" are virtual. 

  Prover(const Property & p, smt::SmtSolver & s);
  virtual ~Prover();

  virtual void initialize();

  virtual ProverResult check_until(int k) = 0;

  bool witness(std::vector<smt::UnorderedTermMap> & out, bool include_internal_wires = false);

  ProverResult prove();
*/

class APDR : public Prover, public ModelLemmaManager {
public:
  // type definition
  typedef std::unordered_set<smt::Term> varset_t;
  typedef std::vector<Lemma *> frame_t;
  typedef std::vector<Model *> facts_t;
  struct solve_trans_result {
    Model * pre_ex;
    Model * post_ex;
    smt::Term itp;
    solve_trans_result (Model * pre, Model * post, const smt::Term & itp_):
      pre_ex(pre), post_ex (post), itp(itp_) {}
  };
  // comparator for fidx, cex
  typedef std::pair<unsigned, Model *> fcex_t;
  struct fcex_queue_comparator {
    bool operator() (const fcex_t & l, const fcex_t & r) {
      return l.first > r.first;
    } };
  
public:
  // inherited interfaces
  APDR(const Property & p, smt::SmtSolver & s, smt::SmtSolver & itp_solver,
    const std::unordered_set<smt::Term> & keep_vars,
    const std::unordered_set<smt::Term> & remove_vars);
  virtual void initialize() override;
  virtual ProverResult check_until(int k) override;
  
  virtual ~APDR(); // for lower cost, we will manage the memory ourselves
  // and disallow copy constructor and etc.
  APDR & operator=(const APDR &) = delete;
  APDR(const APDR &) = delete;

  smt::SmtSolver & solver() override { return solver_; }
  smt::SmtSolver & itp_solver() override { return itp_solver_; }
  smt::TermTranslator & to_itp_solver() override { return to_itp_solver_; }
  smt::TermTranslator & to_btor() override { return to_btor_; }

protected:
  const std::unordered_set<smt::Term> keep_vars_;
  const std::unordered_set<smt::Term> remove_vars_;
  std::unordered_set<smt::Term> keep_vars_nxt_;
  std::unordered_set<smt::Term> remove_vars_nxt_;
  smt::Term init_msat_nxt;
  smt::Term T_msat;
  void cut_vars_cur(std::unordered_set<smt::Term> & v);
  void put_vars_nxt(const std::unordered_set<smt::Term> & in, std::unordered_set<smt::Term> & out);
  // void cut_vars_nxt(std::unordered_set<smt::Term> & v);
  // we don't know the pre/post

  PartialModelGen partial_model_getter;

  std::vector<frame_t> frames;
  std::unordered_map<unsigned, facts_t>  unblockable_fact;
  std::unordered_map<unsigned, unsigned> frames_pushed_idxs_map;
  std::unordered_map<unsigned, unsigned> facts_pushed_idxs_map;

  // the itp solver
  smt::SmtSolver & itp_solver_;
  smt::TermTranslator to_itp_solver_;
  smt::TermTranslator to_btor_;
  // no need to cache trans result -- already cached


protected: // frame handling
  smt::Term frame_prop_btor(unsigned fidx) const;
  smt::Term frame_prop_msat(unsigned fidx) const;
  smt::Term get_inv() const;
  bool frame_implies(unsigned fidx, const smt::Term &prop);
  bool frame_and_fc_implies(unsigned fidx, FrameCache &fc, const smt::Term &prop);
  Model * frame_not_implies_model(unsigned fidx, const smt::Term &prop);
  bool frame_compatible_w(unsigned fidx, const smt::Term &prop); 

  void _add_lemma(Lemma * lemma, unsigned fidx);
  void _add_pushed_lemma(Lemma * lemma, unsigned start, unsigned end);
  void _add_fact(Model * fact, unsigned fidx);
  

protected:
  // member class
  bool is_valid(const smt::Term & e);
  bool is_sat(const smt::Term & e);
  Model * get_not_valid_model(const smt::Term & e);
  Model * solve(const smt::Term & formula);

public:
  bool is_last_two_frames_inductive() ;
  bool is_safe_inductive_inv(const smt::Term & inv);
  void sanity_check_imply();
  void sanity_check_frame_monotone();
  void dump_frames(std::ostream & os) const;

  solve_trans_result solveTrans(
    unsigned prevFidx, const smt::Term & prop_btor, bool remove_prop_in_prev_frame,
    bool use_init, bool findItp, bool get_post_state, FrameCache * fc );
  
  Model * get_bad_state_from_property_invalid_after_trans (
    const smt::Term & prop, unsigned idx, bool use_init);

  bool do_recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin);
  
  bool try_recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin,
    FrameCache & frame_cache);

  bool check_init_failed();
  
  void push_lemma_from_the_lowest_frame();


}; // class APDR


}  // namespace cosa
