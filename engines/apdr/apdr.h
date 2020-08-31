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
 ** \brief Apdr header
 **
 ** 
 **/
 
#pragma once

#include "engines/sygus/partial_model.h"
#include "engines/sygus/ast_knob/opextract.h"
#include "engines/sygus/gen_sygus_query.h"
#include "engines/sygus/unsat_enum.h"
#include "engines/prover.h"
#include "frontends/smtlib2parser.h"

#include "config.h"
#include "lemma.h"
#include "transferts.h"
#include "sygus_pdr.h"

namespace cosa {

/*
  Although inherited from Prover, I don't want to use the unroller,
  because we are not unrolling. So it is just for interface.
  And I hope "witness" and "prove" are virtual. 

  Prover(const Property & p, smt::SmtSolver & s);
  virtual ~Prover();

  virtual void initialize();

  virtual ProverResult check_until(int k) = 0;

  bool witness(std::vector<smt::UnorderedTermMap> & out, bool include_internal_wires = false);

  ProverResult prove();
*/

class Apdr : public Prover, public ModelLemmaManager, public LemmaPDRInterface {
public:
  // type definition
  typedef std::vector<Lemma *> frame_t;
  typedef std::unordered_set<smt::Term> varset_t;
  typedef std::vector<Model *> facts_t;

  // comparator for fidx, cex
  struct fcex_t{
    unsigned fidx;
    Model * cex;
    bool can_transit_to_next;
    Lemma::LemmaOrigin cex_origin;
    fcex_t(unsigned fidx_, Model * cex_,  bool can_transit_to_next_, Lemma::LemmaOrigin origin) : 
    fidx(fidx_), cex(cex_), can_transit_to_next(can_transit_to_next_), cex_origin(origin) {}
  };
  //typedef std::pair<unsigned, Model *> fcex_t;
  // we don't need the comparator, just use vector

  using to_next_t = unsat_enum::Enumerator::to_next_t;
  using extract_model_t = unsat_enum::Enumerator::extract_model_t;
  
public:
  // inherited interfaces
  Apdr(const Property & p, smt::SmtSolver & s, 
    smt::SmtSolver & itp_solver,
    const std::unordered_set<smt::Term> & keep_vars,
    const std::unordered_set<smt::Term> & remove_vars);
  virtual void initialize() override;
  virtual ProverResult check_until(int k) override;
  
  virtual ~Apdr(); // for lower cost, we will manage the memory ourselves
  // and disallow copy constructor and etc.
  Apdr & operator=(const Apdr &) = delete;
  Apdr(const Apdr &) = delete;

  smt::SmtSolver & solver() override { return solver_; }
  virtual smt::SmtSolver & btor() override { return solver_; }
  virtual smt::SmtSolver & msat() override { return itp_solver_; }
  smt::SmtSolver & itp_solver() override { return itp_solver_; }
  // smt::TermTranslator & to_itp_solver() override { return to_itp_solver_; }
  smt::TermTranslator & to_btor() override { return to_btor_; }

  void print_frame_stat(const std::string & extra_info) const;
  void print_time_stat() const;

protected:
  const std::unordered_set<smt::Term> keep_vars_;
  const std::unordered_set<smt::Term> remove_vars_;
  std::unordered_set<smt::Term> keep_vars_nxt_;
  std::unordered_set<smt::Term> remove_vars_nxt_;
  smt::Term init_msat_nxt;
  smt::Term T_msat;
  bool has_assumptions;
  void cut_vars_cur(std::unordered_set<smt::Term> & v);

  PartialModelGen partial_model_getter;

  std::vector<frame_t> frames;

  // the itp solver
  smt::SmtSolver & itp_solver_;
  smt::TermTranslator to_itp_solver_; 
  // should not need this -- 
  // as itp to msat could result in problem
  smt::TermTranslator to_btor_;

  //const TransitionSystem & ts_msat_;
  //const Property & property_msat_;
  TransferredTransitionSystem ts_msat_;
  smt::Term property_msat_;

  // cache the two lambda function
  to_next_t to_next_func_;
  extract_model_t extract_model_func_;
  Model * extract_model_output_;


  // no need to cache trans result -- already cached
  smt::UnorderedTermSet sygus_symbol_;
  std::unordered_set<std::string> sygus_symbol_names_;
  sygus::SyGuSTransBuffer sygus_tf_buf_;
  std::unique_ptr<OpExtractor> op_extract_;
  unsat_enum::VarTermManager sygus_term_manager_;
  std::unique_ptr<sygus::SyGusQueryGen> sygus_query_gen_;

  // use by internal sygus
  ApdrSygusHelper sygus_info_helper_;

protected:
  bool is_valid(const smt::Term & e);
  bool is_valid_imply(const smt::Term & pre, const smt::Term & post);
  bool is_sat(const smt::Term & e);
  Model * get_not_valid_model(const smt::Term & e);
  Model * solve(const smt::Term & formula);

public: // sanity and dumping
  smt::Term get_inv() const;
  void validate_inv(); // the same as following
  bool is_safe_inductive_inv(const smt::Term & inv);

  virtual void dump_frames(std::ostream & os) const override;
  
protected: // sanity and dumping
  Model * frame_not_implies_model(unsigned fidx, const smt::Term &prop); // check fail dump
  void sanity_check_imply(); // Fi /\ T => F'i+1
  void sanity_check_frame_monotone(); // Fi => Fi+1
  void sanity_check_last_frame_nopushed(); // lemmas at last frame are not pushed
  smt::Result sanity_check_property_at_length_k(const smt::Term & btor_p, unsigned k); // in sat case, validate with BMC
  void sanity_check_prop_fail(const std::vector<fcex_t> & path);


protected: // essentials
  bool is_last_two_frames_inductive() ;
  virtual bool frame_implies(unsigned fidx, const smt::Term &prop) override;
  virtual smt::Term frame_prop_btor(unsigned fidx) const override;
  smt::Term frame_prop_msat(unsigned fidx) const;

  void _add_lemma(Lemma * lemma, unsigned fidx);
  void _add_pushed_lemma(Lemma * lemma, unsigned start, unsigned end);

protected: // sygus related
  void reset_sygus_syntax();  
  // returns msat's term
  smt::Term do_sygus(const smt::Term & prevF_msat, 
    const smt::Term & prevF_btor,
    const smt::Term & prop_msat,
    const smt::Term & prop_btor,
    const std::vector<Model *> & cexs, const std::vector<Model *> & facts,
    bool assert_inv_in_prevF,
    ApdrSygusHelper & sygus_info /* if possible use itp var num */ );

public:
  void propose_new_lemma_to_block(fcex_t * pre, fcex_t * post);
  // within pre/post, you have fidx

  std::pair<smt::Term, smt::Term> gen_lemma(
    unsigned fidx,
    const smt::Term & Fprev_msat, 
    const smt::Term & Fprev_btor, 
    const smt::Term & prop_msat,
    const smt::Term & prop_btor,
    const std::vector<Model *> & cexs );
  
  virtual solve_trans_result solveTrans( unsigned prevFidx, 
    const smt::Term & prop_btor,
    bool remove_prop_in_prev_frame,
    bool use_init, bool get_pre_state) override;

  solve_trans_lemma_result Apdr::solveTransLemma(
    unsigned prevFidx, 
    const std::vector<Model *> & models_to_block,
    bool remove_prop_in_prev_frame,
    // bool use_init = true, bool findItp = true,
    bool get_pre_state);

  bool recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin);

  bool check_init_failed();

  void push_lemma_from_the_lowest_frame();

  void push_lemma_from_frame(unsigned fidx, bool second_round_push);


  // --------------- accessor --------------- //
  // --------- delegate to TransitionSystem -------- //
  virtual smt::Term next(const smt::Term &e) const override { return ts_.next(e);}
  virtual smt::Term curr(const smt::Term &e) const override { return ts_.curr(e);}
  virtual bool is_curr_var(const smt::Term &e) const { return ts_.is_curr_var(e); }
  virtual smt::Term init() const override { return ts_.init(); }
  virtual smt::Term trans() const override { return ts_.trans(); }
  virtual const smt::UnorderedTermSet & states() const override { return ts_.states(); }
  virtual const smt::UnorderedTermSet & next_states() const override { return ts_.next_states(); }

  virtual smt::Term next_msat(const smt::Term &e) const override { return ts_msat_.next(e);}
  virtual smt::Term curr_msat(const smt::Term &e) const override { return ts_msat_.curr(e);}
  virtual smt::Term init_msat() const override { return ts_msat_.init(); }
  virtual smt::Term trans_msat() const override { return ts_msat_.trans(); }
  virtual const smt::UnorderedTermSet & states_msat() const override { return ts_msat_.states(); }
  virtual const smt::UnorderedTermSet & next_states_msat() const override { return ts_msat_.next_states(); }

}; // class Apdr


}  // namespace cosa
