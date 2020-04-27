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

#include <cassert>

// some helper functions
// #define TERM_TRUE    (pdr.btor()->make_term(true))
#define NOT(x)       (pdr.btor()->make_term(smt::Not, (x)))
// #define EQ(x, y)     (pdr.btor()->make_term(smt::Equal, (x), (y)))
// #define AND(x, y)    (pdr.btor()->make_term(smt::And, (x), (y)))
// #define OR(x, y)     (pdr.btor()->make_term(smt::Or, (x), (y)))
#define IMPLY(x, y)  (pdr.btor()->make_term(smt::Implies, (x), (y)))

// some helper functions
// #define TERM_TRUE_msat    (pdr.msat()->make_term(true))
// #define NOT_msat(x)       (pdr.msat()->make_term(smt::Not, (x)))
// #define EQ_msat(x, y)     (pdr.msat()->make_term(smt::Equal, (x), (y)))
// #define AND_msat(x, y)    (pdr.msat()->make_term(smt::And, (x), (y)))
// #define OR_msat(x, y)     (pdr.msat()->make_term(smt::Or, (x), (y)))
// #define IMPLY_msat(x, y)  (pdr.msat()->make_term(smt::Implies, (x), (y)))



namespace cosa {


smt::Term bv_to_bool_msat(const smt::Term & t, const smt::SmtSolver & itp_solver_ )
{
  smt::Sort sort = t->get_sort();
  if (sort->get_sort_kind() == smt::BV) {
    if (sort->get_width() != 1) {
      throw CosaException("Can't convert non-width 1 bitvector to bool.");
    }
    return itp_solver_->make_term(
        smt::Equal, t, itp_solver_->make_term(1, itp_solver_->make_sort(smt::BV, 1)));
  } else {
    return t;
  }
}


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


Lemma * Lemma::direct_push(ModelLemmaManager & mfm) {
  pushed = true;
  Lemma * ret = mfm.new_lemma(expr_, expr_msat_, cex_, origin_);
  stats_push_fail(false);
  ret->n_itp_push_failure = n_itp_push_failure;
  ret->n_itp_push_trial   = n_itp_push_trial;
  ret->n_itp_enhance_failure = n_itp_enhance_failure;
  ret->n_itp_enhance_trial   = n_itp_enhance_trial;
  return ret;
}


bool Lemma::subsume_by_frame(unsigned fidx, LemmaPDRInterface & pdr) {
  if (!pdr.is_valid(IMPLY(pdr.frame_prop_btor(fidx), NOT(cex_->to_expr_btor(pdr.btor())) )  )) 
    return false;
  return true;
}

// cex_failed? and ITP
std::pair<bool, Lemma *> Lemma::try_itp_push(FrameCache &fc, unsigned src_fidx, 
    LemmaPDRInterface & pdr) {
  unsigned nl_at_f =  fc.n_lemma_at_frame(src_fidx+1);
  bool blockable = pdr.try_recursive_block(cex_, src_fidx+1, origin_, fc);
  if (blockable) {
    assert ( fc.n_lemma_at_frame(src_fidx+1) == nl_at_f + 1);
    stats_push_fail(false);
    Lemma * l = fc.get_frames().at(src_fidx+1).back();
    l->n_itp_push_failure = n_itp_push_failure;
    l->n_itp_push_trial = n_itp_push_trial;
    return std::make_pair(false, l);
  }
  return std::make_pair<bool,Lemma *>(true, NULL);
} // try_itp_push

// prop_succ, all_succ, bmBnd, unblocked_cube
std::tuple<bool, bool, int, Model *> Lemma::try_strengthen(FrameCache &fc,
  int bnd, unsigned src_fidx, Model * prev_ex, LemmaPDRInterface & pdr, ModelLemmaManager & mlm) {
  
  assert (prev_ex);
  while (prev_ex) {
    bool blockable = pdr.try_recursive_block(prev_ex, src_fidx, LemmaOrigin::ORIGIN_FROM_PUSH, fc);
    if (!blockable) {
      stats_push_fail(true);
      return std::make_tuple(false, false, bnd, prev_ex);
    }
    auto trans_result = pdr.solveTrans(src_fidx, expr_, expr_msat_,
      false /*rm prop*/, false /*init*/, false /*itp*/, false /*post_state*/, &fc);
    prev_ex = trans_result.prev_ex; // update the cex
    -- bnd;
    if (bnd < 0) {
      stats_push_fail(true);
      return std::make_tuple(false, false, bnd, prev_ex);
    }
  }
  // okay, we know the current lemma holds on src_fidx+1
  // add its direct push to fc next level
  //  - prev_ex is None from this point
  fc._add_lemma(direct_push(mlm), src_fidx+1);
  // but for the newly added lemma at src_fidx, we want them to be pushable as well
  // there could be more lemma in earlier frames, but we don't bother them
  //  - prop_succ = true from this point
  // try block all lemmas on the current frame
  if (fc.has_lemma_at_frame(src_fidx)) {
    for (Lemma * l : fc.get_frames().at(src_fidx)) {
      auto trans_result = pdr.solveTrans(src_fidx, expr_,  expr_msat_,
        false /*rm prop*/, false /*init*/, false /*itp*/, false /*post_state*/, &fc);
      prev_ex =  trans_result.prev_ex; // update the cex

      if (prev_ex == NULL)
        continue;
      
      bool prop_succ, all_succ; int rmBnd; Model * unblockable_cube;
      std::tie(prop_succ, all_succ, rmBnd, unblockable_cube) = 
        l->try_strengthen(fc, bnd, src_fidx, prev_ex, pdr, mlm);
      bnd = rmBnd;
      if (bnd < 0)
        return std::make_tuple<bool, bool, int, Model *>(true, false, (int)bnd, (Model *) NULL);
      if (! (all_succ || prop_succ)) {
        assert (unblockable_cube);
        return std::make_tuple(true, false, (int)bnd, unblockable_cube);
      }
    } // end each lemma @ src_fidx in fc
  } // fc lemma

  return std::make_tuple<bool, bool, int, Model *>(true, true, (int)bnd, (Model *) NULL);
} // try_strengthen

Lemma * Lemma::try_sygus_repair(unsigned fidx, unsigned lemmaIdx, Model * post_ex,
  Lemma * new_itp, LemmaPDRInterface & pdr, ModelLemmaManager & mfm) {
  // TO BE IMPLEMENTED
  return NULL;
} // try_sygus_repair


// --------------------- DUMPs --------------------- //


void Lemma::stats_push_fail(bool failed) {
  if (failed)
    ++ n_itp_push_failure;
  ++ n_itp_push_trial;
}
void Lemma::stats_sygus_fail(bool failed) {
  if (failed)
    ++ n_itp_enhance_failure;
  ++ n_itp_enhance_trial;
}

std::vector<std::string_view> origin2str = {
  "prop", "push", "init"
};

std::string Lemma::origin_to_string(LemmaOrigin o) {
  return static_cast<std::string>(origin2str.at(o));
}

std::string Lemma::dump_expr() const {
  return ( pushed ? "P" : " " ) + 
    ("|" + expr_->to_string() ) + 
    ("|" + origin_to_string(origin_) ) + 
    ("| (" + std::to_string(n_itp_push_failure) + "," + std::to_string(n_itp_push_trial)+ "),("
           + std::to_string(n_itp_enhance_failure) + "," + std::to_string(n_itp_enhance_trial)+ ")" );
}
std::string Lemma::dump_cex() const {
  return ( pushed ? "P" : " " ) + 
    ("|" + cex_->to_string() ) + 
    ("|" + origin_to_string(origin_) ) + 
    ("| (" + std::to_string(n_itp_push_failure) + "," + std::to_string(n_itp_push_trial)+ "),("
           + std::to_string(n_itp_enhance_failure) + "," + std::to_string(n_itp_enhance_trial)+ ")" );
}

} // namespace cosa
 
 
