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
  enum LemmaOrigin {ORIGIN_FROM_PROPERTY, ORIGIN_FROM_PUSH, ORIGIN_FROM_INIT};
  struct solve_trans_result {
    Model * prev_ex;
    Model * post_ex;
    smt::Term itp;
    smt::Term itp_msat;
    solve_trans_result (Model * pre, Model * post, const smt::Term & itp_, const smt::Term & itp_msat_):
      prev_ex(pre), post_ex (post), itp(itp_), itp_msat(itp_msat_) {}
  };
public:
  virtual bool is_valid(const smt::Term &) = 0;
  virtual smt::Term frame_prop_btor(unsigned fidx) const = 0;
  virtual smt::Term frame_prop_btor(unsigned fidx, unsigned not_include_lemmaIdx) const = 0;

  virtual smt::SmtSolver & btor() = 0;
  virtual smt::SmtSolver & msat() = 0;
  virtual solve_trans_result solveTrans(
    unsigned prevFidx,
    const smt::Term & prop_btor, const smt::Term & prop_msat, // or the following
    const std::vector<Model *> & models_to_block, const std::vector<Model *> & models_fact,
    bool remove_prop_in_prev_frame,
    bool use_init, bool findItp, bool get_post_state, FrameCache * fc ) = 0;
  virtual bool try_recursive_block(
    Model * cube, unsigned idx, LemmaOrigin cex_origin,
    FrameCache & frame_cache) = 0;
  
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
  bool try_itp_push(FrameCache &fc, unsigned src_fidx, 
     LemmaPDRInterface & pdr);
  // prop_succ, all_succ, bmBnd, unblocked_cube
  std::tuple<bool, bool, int, Model *> try_strengthen(FrameCache &fc,
    int bnd, unsigned src_fidx, Model * prev_ex, LemmaPDRInterface & pdr, ModelLemmaManager & mlm);
  Lemma * try_sygus_repair(unsigned fidx, unsigned lemmaIdx, Model * post_ex,
    Lemma * new_itp, LemmaPDRInterface & pdr, ModelLemmaManager & mfm);



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
  Model * new_model(const std::unordered_set<smt::Term> & varset);

  Lemma * new_lemma(
    const smt::Term & expr, const smt::Term & expr_msat,
    Model * cex, Lemma::LemmaOrigin origin);
    
  std::vector<Lemma *> lemma_allocation_pool;
  std::vector<Model *> cube_allocation_pool;
  
};

}  // namespace cosa

