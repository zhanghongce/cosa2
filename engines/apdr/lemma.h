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
 ** \brief APDR Lemma class
 **
 ** 
 **/
 
 
#pragma once

#include "../sygus/partial_model.h"
#include "../prover.h"
#include "sig_apdr_if.h"

namespace cosa {

class Lemma;
class ModelLemmaManager;
class FrameCache;


class LemmaPDRInterface : public SignalPDRInterface {
public:
  enum LemmaOrigin {MUST_BLOCK, MAY_BLOCK, ORIGIN_FROM_INIT};
  
  struct solve_trans_result{
    bool not_hold;
    bool not_hold_at_init;
    Model * prev_ex;
    solve_trans_result(bool sat, bool sat_at_init, Model * pre) :
      not_hold(sat), not_hold_at_init(sat_at_init), prev_ex(pre) {}
    // if sat at init, prev_ex = in cube (of course)
  };

  struct solve_trans_lemma_result : solve_trans_result {
    // if not hold == false and itp == empty
    // then we know we don't have good syntax to gen a lemma
    // at that point may_block should != NULL
    smt::TermVec itp;
    smt::TermVec itp_msat;
    Model * may_block;
    bool may_block_at_init;
    solve_trans_lemma_result( const solve_trans_result & no_lemma) : 
      solve_trans_result(no_lemma), may_block(NULL), may_block_at_init(false) {}
    solve_trans_lemma_result (
      bool sat_, bool sat_at_init, Model * pre, Model * mayblock, bool may_block_at_init_):
      solve_trans_result(sat_, sat_at_init, pre) ,
      may_block(mayblock), may_block_at_init(may_block_at_init_) {}

    bool unblockable() const { return not_hold; }
    bool no_good_syntax() const { return !not_hold && may_block; } // assert itp.empty
    bool has_lemma() const { return !itp.empty(); } // assert !not_hold and may_block == empty
  };

public:
  // some function units
  virtual bool is_valid(const smt::Term &) = 0;
  virtual smt::Term frame_prop_btor(unsigned fidx) const = 0;
  virtual bool frame_implies(unsigned fidx, const smt::Term &prop) = 0;

  virtual solve_trans_result solveTrans( unsigned prevFidx, 
    const smt::Term & prop_btor,
    bool remove_prop_in_prev_frame,
    bool use_init, bool get_pre_state) = 0;

  virtual bool recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin) = 0;
  
  // getters
  virtual smt::SmtSolver & btor() = 0;
  virtual smt::SmtSolver & msat() = 0;
  virtual smt::Term next(const smt::Term &) const = 0;
  virtual smt::Term curr(const smt::Term &) const = 0;
  virtual bool is_curr_var(const smt::Term &) const = 0;
  virtual smt::Term init() const = 0;
  virtual smt::Term trans() const = 0;
  virtual const smt::UnorderedTermSet & states() const = 0;
  virtual const smt::UnorderedTermSet & next_states() const = 0;

  virtual smt::Term next_msat(const smt::Term &) const = 0;
  virtual smt::Term curr_msat(const smt::Term &) const = 0;
  virtual smt::Term init_msat() const = 0;
  virtual smt::Term trans_msat() const = 0;
  virtual const smt::UnorderedTermSet & states_msat() const = 0;
  virtual const smt::UnorderedTermSet & next_states_msat() const = 0;

  virtual void dump_frames(std::ostream & os) const = 0;

};  // class LemmaPDRInterface


// the lemma on a frame
class Lemma {
public:
  using LemmaOrigin = LemmaPDRInterface::LemmaOrigin;
  
  Lemma(const smt::Term & expr, const smt::Term & expr_msat, Model * cex, LemmaOrigin origin);
  
  inline smt::Term  expr() const { return expr_; }
  inline smt::Term  expr_msat() const { return expr_msat_; }
  inline Model *  cex() const { return cex_; }
  inline std::string to_string() const { return expr()->to_string(); }
  inline LemmaOrigin origin() const { return origin_; }

  Lemma * copy(ModelLemmaManager & mfm);
  
  bool pushed;

  void stats_push_fail(bool failed);
  void stats_sygus_fail(bool failed);

  Lemma * direct_push(ModelLemmaManager & mfm);
  bool subsume_by_frame(unsigned fidx, LemmaPDRInterface & pdr);
  // cex_failed, and ITP


  static std::string origin_to_string(LemmaOrigin o) ;
  std::string dump_expr() const;
  std::string dump_cex() const;

protected:
  // the expression : for btor
  smt::Term expr_;
  // the expression : for msat
  smt::Term expr_msat_;
  // the cex it blocks
  Model*  cex_;
  // status tracking
  LemmaOrigin origin_;
  
  unsigned n_itp_push_trial;
  unsigned n_itp_push_failure;
  unsigned n_itp_enhance_trial;
  unsigned n_itp_enhance_failure;
}; // class Lemma


// class to manage the memory of memory and frames
// apdr shall inherit from this
class ModelLemmaManager {
  friend class Lemma;
public:
  ModelLemmaManager ();
  virtual ~ModelLemmaManager();
  
  ModelLemmaManager & operator=(const ModelLemmaManager &) = delete;
  ModelLemmaManager(const ModelLemmaManager &) = delete;
  
  virtual smt::SmtSolver & solver() = 0;
  virtual smt::SmtSolver & itp_solver() = 0;
  // virtual smt::TermTranslator & to_itp_solver() = 0;
  virtual smt::TermTranslator & to_btor() = 0;

protected:
  Model * new_model();
  void register_new_model(Model *);
  Model * new_model(const std::unordered_set<smt::Term> & varset);
  Model * new_model_replace_var(
    const std::unordered_set<smt::Term> & varset,
    const std::unordered_map<smt::Term, smt::Term> & varmap );

  Lemma * new_lemma(
    const smt::Term & expr, const smt::Term & expr_msat,
    Model * cex, Lemma::LemmaOrigin origin);
    
  std::vector<Lemma *> lemma_allocation_pool;
  std::vector<Model *> cube_allocation_pool;
  
};

}  // namespace cosa

