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

namespace cosa {

class Lemma;
class ModelLemmaManager;


// the lemma on a frame
class Lemma {
public:
  enum LemmaOrigin {ORIGIN_FROM_PROPERTY, ORIGIN_FROM_PUSH, ORIGIN_FROM_INIT};
  
  Lemma(const smt::Term & expr, const smt::Term & expr_msat, Model * cex, LemmaOrigin origin);
  
  inline smt::Term  expr() const { return expr_; }
  inline smt::Term  expr_msat() const { return expr_msat_; }
  inline Model *  cex() const { return cex_; }

  Lemma * copy(ModelLemmaManager & mfm);
  
  bool pushed;
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
  virtual smt::TermTranslator & to_itp_solver() = 0;
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

