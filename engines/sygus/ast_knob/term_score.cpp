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
 ** \brief The term scores for predicates (will help decide removing order)
 **
 ** 
 **/

#include "term_score.h"
#include "utils/container_shortcut.h"
#include <cassert>

namespace cosa {

namespace unsat_enum {

TermScore::score_map_t TermScore::scores_;

unsigned TermScore::GetScore(const smt::Term & t) {
  auto pos = scores_.find(t);
  if (pos != scores_.end())
    return pos->second.score;
  TermScore walker;
  walker.WalkBFS(t);
  
  pos = scores_.find(t);
  assert (pos != scores_.end());
  return pos->second.score;
}

bool TermScore::Skip(const smt::Term & ast) {
  return IN(ast, scores_);
}

void TermScore::PreChild(const smt::Term & ast) {
  assert(!IN(ast, scores_));
 // walked_nodes_.insert(ast);
}

void TermScore::PostChild(const smt::Term & ast) {
 // for all its child, add parent pointer to the map
  unsigned width = 1;
  if (ast->get_sort()->get_sort_kind() == smt::SortKind::BOOL)
    width = 1;
  else if (ast->get_sort()->get_sort_kind() == smt::SortKind::BV)
    width = ast->get_sort()->get_width();

  if (ast->is_symbolic_const()) {
    scores_.emplace(ast,term_score_t(0)); // width*2
  } else if ( ast->is_value() ) { 
    scores_.emplace(ast,term_score_t(1)); // width
  } else { // we will hope it is op
    auto ret = scores_.emplace(ast,term_score_t(1));   // width  
    for(auto && c : *ast) { // for each of its child node
      ret.first->second.score += scores_.at(c).score;
      //  iterator->the score
    } // sum their scores and add one for itself
  } // end of op
} // PostChild


} // namespace unsat_enum

} // namespace cosa

