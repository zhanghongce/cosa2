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
 ** \brief FrameCache for tentative pushing
 **
 ** 
 **/
 
 
#include "apdr.h"

#include "utils/container_shortcut.h"

#include <cassert>

// some helper functions
#define TERM_TRUE    (btor_->make_term(true))
// #define NOT(x)       (btor_->make_term(smt::Not, (x)))
// #define EQ(x, y)     (btor_->make_term(smt::Equal, (x), (y)))
#define AND(x, y)    (btor_->make_term(smt::And, (x), (y)))
// #define OR(x, y)     (btor_->make_term(smt::Or, (x), (y)))
// #define IMPLY(x, y)  (btor_->make_term(smt::Implies, (x), (y)))

// some helper functions
#define TERM_TRUE_msat    (msat_->make_term(true))
// #define NOT_msat(x)       (msat_->make_term(smt::Not, (x)))
// #define EQ_msat(x, y)     (msat_->make_term(smt::Equal, (x), (y)))
#define AND_msat(x, y)    (msat_->make_term(smt::And, bv_to_bool_msat(x, msat_), bv_to_bool_msat(y, msat_)))
// #define OR_msat(x, y)     (msat_->make_term(smt::Or, (x), (y)))
// #define IMPLY_msat(x, y)  (msat_->make_term(smt::Implies, (x), (y)))

 
namespace cosa {
 
// -----------------------------------------------------------------------
// HERE begins FrameCache's function definitions

void FrameCache::_add_lemma(Lemma * lemma, unsigned fidx) {
  if(!IN(fidx, frames))
    frames.insert(std::make_pair(fidx, frame_t()));
  frames.at(fidx).push_back(lemma);
}
void FrameCache::_add_pushed_lemma(Lemma * lemma, unsigned start, unsigned end) {
  Lemma * l_prev = lemma->copy(mlm_);
  l_prev->pushed = true;
  for (size_t fidx = start; fidx <= end; ++ fidx)
    _add_lemma(l_prev, fidx);
}

bool FrameCache::has_lemma_at_frame(unsigned fidx) const {
  return IN(fidx, frames);
}

unsigned FrameCache::n_lemma_at_frame(unsigned fidx) const {
  if (!IN(fidx,frames))
    return 0;
  return frames.at(fidx).size();
}


smt::Term FrameCache::conjoin_frame_for_props_btor(unsigned fidx) {
  if (!IN(fidx,frames))
    return TERM_TRUE;
  smt::Term ret = nullptr;
  for (Lemma * l : frames.at(fidx)) {
    if (ret == nullptr)
      ret = l->expr();
    else
      ret = AND(ret, l->expr());
  }
  return ret;
}

smt::Term FrameCache::conjoin_frame_for_props_msat(unsigned fidx) {
  if (!IN(fidx,frames))
    return TERM_TRUE_msat;
  smt::Term ret = nullptr;
  for (Lemma * l : frames.at(fidx)) {
    if (ret == nullptr)
      ret = l->expr_msat();
    else
      ret = AND_msat(ret, l->expr_msat());
  }
  return ret;
}

} // namespace cosa


