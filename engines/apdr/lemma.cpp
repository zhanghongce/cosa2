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
 
 #include "lemma.h"
 #include "apdr.h"
 
namespace cosa {

ModelLemmaManager::ModelLemmaManager() { }

ModelLemmaManager::~ModelLemmaManager() {
  for (auto lp : lemma_allocation_pool)
    delete lp;
  for (auto mp : cube_allocation_pool)
    delete mp;    
}

Model * ModelLemmaManager::new_model() {
  cube_allocation_pool.push_back(new Model);
  return cube_allocation_pool.back();
}


Model * ModelLemmaManager::new_model(const std::unordered_set<smt::Term> & varset) {
  cube_allocation_pool.push_back(new Model(solver() , varset));
  return cube_allocation_pool.back();
}

Lemma * ModelLemmaManager::new_lemma(
    const smt::Term & expr, const smt::Term & expr_msat, 
    Model * cex, Lemma::LemmaOrigin origin) {
  lemma_allocation_pool.push_back(new Lemma(expr, expr_msat, cex, origin));
  return lemma_allocation_pool.back();
}


Lemma::Lemma(const smt::Term & expr, const smt::Term & expr_msat, Model * cex, LemmaOrigin origin):
  expr_(expr), expr_msat_(expr_msat),
  cex_(cex),  origin_(origin), pushed(false),
  n_itp_push_trial(0), n_itp_push_failure(0), 
  n_itp_enhance_trial(0), n_itp_enhance_failure(0) { }
  
Lemma * Lemma::copy(ModelLemmaManager & mfm) {
  return mfm.new_lemma(expr_, expr_msat_, cex_, origin_);
}

} // namespace cosa
 
 
