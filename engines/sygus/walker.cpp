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
 ** \brief term walker -- extract op/var or setup parital eval tree
 **
 ** 
 **/

#include "walker.h"
#include "container_shortcut.h"

namespace cosa {

// I was worried that this will make stack overflow
void Walker::WalkRecursion(const smt::Term & ast) {
  if (Skip(ast))
    return;
  PreChild(ast);
  for (const auto & c : *ast)
    WalkRecursion(c);
  PostChild(ast);
}

void Walker::Walk(const smt::Term & ast) {
  std::vector<smt::Term> term_stack;
  std::unordered_set<smt::Term> walked;
  // for post-walk function
  
  term_stack.push_back(ast);
  while(!term_stack.empty()) {
    const auto & cur = term_stack.back();
    if (Skip(cur)) {
      term_stack.pop_back();
      continue;
    }

    if (IN(cur, walked)) { // this is after its children
      PostChild(cur);
      term_stack.pop_back();
      continue;
    } // this is after its child

    PreChild(cur);
    walked.insert(cur);
    // for each of its child
    for (const auto & c : *ast)
      term_stack.push_back(c);
  }
} // end of Walker::Walk

} // namespace cosa