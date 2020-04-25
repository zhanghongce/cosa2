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
public:
  typedef std::vector<Lemma *> frame_t;
protected:
  std::unordered_map<unsigned, std::vector<Lemma *>> frames;
  smt::SmtSolver & btor_;
  smt::SmtSolver & msat_;
  ModelLemmaManager & mlm_;
public:
  FrameCache (smt::SmtSolver & btor, smt::SmtSolver & msat,
    ModelLemmaManager & mlm) :
    btor_(btor), msat_(msat), mlm_(mlm) {}

  void _add_lemma(Lemma * lemma, unsigned fidx);
  void _add_pushed_lemma(Lemma * lemma, unsigned start, unsigned end);

  bool has_lemma_at_frame(unsigned fidx) const;
  smt::Term conjoin_frame_for_props_btor(unsigned fidx);
  smt::Term conjoin_frame_for_props_msat(unsigned fidx);

  std::unordered_map<unsigned, std::vector<Lemma *>> & get_frames() { return frames; }
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

class APDR : public Prover, public ModelLemmaManager, public LemmaPDRInterface {
public:
  // type definition
  using frame_t = FrameCache::frame_t;
  typedef std::unordered_set<smt::Term> varset_t;
  typedef std::vector<Model *> facts_t;

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
  virtual smt::SmtSolver & btor() override { return solver_; }
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
  virtual smt::Term frame_prop_btor(unsigned fidx) const override;
  virtual smt::Term frame_prop_btor(unsigned fidx, unsigned not_include_lemmaIdx) const override;
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
  virtual bool is_valid(const smt::Term & e) override;
  bool is_sat(const smt::Term & e);
  Model * get_not_valid_model(const smt::Term & e);
  Model * solve(const smt::Term & formula);

public:
  bool is_last_two_frames_inductive() ;
  bool is_safe_inductive_inv(const smt::Term & inv);
  void sanity_check_imply();
  void sanity_check_frame_monotone();
  virtual void dump_frames(std::ostream & os) const override;

  virtual solve_trans_result solveTrans(
    unsigned prevFidx, const smt::Term & prop_btor, bool remove_prop_in_prev_frame,
    bool use_init, bool findItp, bool get_post_state, FrameCache * fc ) override;
  
  Model * get_bad_state_from_property_invalid_after_trans (
    const smt::Term & prop, unsigned idx, bool use_init);

  bool do_recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin);
  
  virtual bool try_recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin,
    FrameCache & frame_cache) override;

  bool check_init_failed();

  void push_lemma_from_the_lowest_frame();

  void push_lemma_from_frame(unsigned fidx);

  void merge_frame_cache(FrameCache & fc);

  // --------------- accessor --------------- //
  // --------- delegate to TransitionSystem -------- //
  virtual smt::Term next(const smt::Term &e) const override { return ts_.next(e);}
  virtual smt::Term curr(const smt::Term &e) const override { return ts_.curr(e);}
  virtual smt::Term init() const override { return ts_.init(); }
  virtual smt::Term trans() const override { return ts_.trans(); }
  virtual const smt::UnorderedTermSet & states() const override { return ts_.states(); }
  virtual const smt::UnorderedTermSet & next_states() const override { return ts_.next_states(); }

}; // class APDR


}  // namespace cosa
