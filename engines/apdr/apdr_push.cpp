
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
 ** \brief Apdr lemma pushing
 **
 ** 
 **/
 
#include "apdr.h"
#include "support.h"
#include "utils/logger.h"

namespace cosa {

void Apdr::push_lemma_from_the_lowest_frame() {
  unsigned start_frame = 1;
  D(1, "[pushes] F{} --- F{}", start_frame, frames.size() -2);
  for (unsigned fidx = start_frame; fidx < frames.size() -1 ; ++ fidx) {
    push_lemma_from_frame(fidx, true);
  }
}

void Apdr::push_lemma_from_frame(unsigned fidx, bool second_round_push) {
  assert (frames.size() > fidx + 1);
  
#ifdef DEBUG
  if (frames.at(fidx).empty())
    dump_frames(std::cerr);
#endif
  assert (frames.at(fidx).size() > 0 );
  PUSH_STACK(APdrConfig::Apdr_working_state_t::PUSH_A_FRAME);


  // 2. push lemmas
  unsigned start_lemma_idx = 0; // will push all anyway
  unsigned end_lemma_idx   = frames.at(fidx).size();

  //                      lemmaIdx, Lemma, prev_ex, post_ex
  std::vector<std::tuple<unsigned, Lemma *>> unpushed_lemmas;
  
  for (unsigned lemmaIdx = start_lemma_idx ; lemmaIdx < end_lemma_idx; ++ lemmaIdx) {
    Lemma * lemma = frames.at(fidx).at(lemmaIdx);
    if (lemma->pushed)
      continue;
    D(2, "  [push_lemma F{}] Try pushing lemma l{} to F{}: {}",
      fidx, lemmaIdx, fidx+1, lemma->to_string());
    auto result = solveTrans(fidx, 
      lemma->expr(),
      false /*rm prop in prev frame*/, false /*use_init*/,
      false /*pre state : false*/ );
    assert(!result.not_hold_at_init);

    if (!result.not_hold) {
      D(2, "  [push_lemma F{}] Succeed in pushing l{}",
        fidx, lemmaIdx);
      _add_lemma(lemma->direct_push(*this), fidx+1);
    } else if (second_round_push) {
      if (lemma->origin() == LemmaOrigin::MUST_BLOCK)
        unpushed_lemmas.push_back(std::make_tuple(
          lemmaIdx, lemma
        ));
      // will only try hard on MUST block lemma
    }
  } // try plain pushing

  INFO("F{}->F{}: {}/{} not pushed by first round.", fidx , fidx+1, 
    unpushed_lemmas.size(), end_lemma_idx - start_lemma_idx);

  // 3. handle unpushed lemmas
  std::string push_status;
  // if there is no second round push, this loop will not execute
  for (auto && unpushed_lemma : unpushed_lemmas) {
    unsigned lemmaIdx;
    Lemma * lemma;
    std::tie(lemmaIdx, lemma) = unpushed_lemma; // unpack
    
    if (lemma->cex() == NULL) {
      D(2, "  [push_lemma F{}] will give up on lemma as it blocks None, l{} : {}",
        fidx, lemmaIdx, lemma->to_string());
      push_status += '.';
      continue; 
    }

    // 3.1 if cex is subsumed, then we don't need to worry about this one
    if (lemma->subsume_by_frame(fidx + 1, *this)) {
      push_status += '.';
      continue;
    } // this is for mulitple lemmas for the same cex
    // some may be not good, so we will try that hard
    // we may revisit it later if it becomes pushable from this frame

    // 3.2 try itp repair to see if the cex is pushable or not
    //     - if it is pushable, we will use the pushed one the last
    //       but the others the first
    //     - if it is not pushable, we don't need to try anymore
    //       just give up

    // rationals of using frame cache: if cex is not pushable
    // but there might be lemmas added in the previous frame
    // that are used to block the cex, some of them could be incorrect
    // we can add configuration of whether to add them also

    // Aug 29 note: not using frame cache
    // those bad ones will be marked as may-block and they
    // will not be handled as hard. Therefore it is okay to keep
    // them in the same frames

    unsigned old_size = frames.at(fidx+1).size();
    bool cex_failed = !recursive_block(lemma->cex(), fidx+1, Lemma::LemmaOrigin::MUST_BLOCK);
    unsigned new_size = frames.at(fidx+1).size();
    
    if (cex_failed) {
      D(2, "  [push_lemma F{}] skip pushing l{} : {} , as its cex cannot be push-blocked.",
        fidx, lemmaIdx, lemma->to_string());
      push_status += 'x';
      continue;
    }

    push_status += "C"+std::to_string(new_size - old_size);
    continue;
  } // for each unpushe lemma
  
  INFO("F{}->F{}: second round push {} ",fidx,fidx+1, push_status);
  POP_STACK;
} // push_lemma_from_frame

} // namespace cosa


