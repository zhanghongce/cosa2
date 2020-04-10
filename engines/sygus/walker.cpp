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
void Walker::WalkDFS(const smt::Term & ast) {
  if (Skip(ast))
    return;
  PreChild(ast);
  for (const auto & c : *ast)
    WalkDFS(c);
  PostChild(ast);
}

void Walker::WalkBFS(const smt::Term & ast) {
  std::vector<std::pair<smt::Term,bool>> term_stack;
  
  term_stack.push_back(std::make_pair(ast,false));
  while(!term_stack.empty()) {
    auto & cur = term_stack.back();
    const auto & astnode = cur.first;
    if (Skip(astnode)) {
      term_stack.pop_back();
      continue;
    }

    if (cur.second) { // this is after its children
      PostChild(astnode);
      term_stack.pop_back();
      continue;
    } // this is after its child

    PreChild(astnode);
    cur.second = true;
    // for each of its child
    for (const auto & c : *astnode)
      term_stack.push_back(std::make_pair(c, false));
  }
} // end of Walker::WalkBFS

} // namespace cosa