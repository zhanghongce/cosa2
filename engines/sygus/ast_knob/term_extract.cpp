/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term extractor
 **
 ** 
 **/

#include "term_extract.h"
#include "utils/logger.h"
#include "utils/container_shortcut.h"

#include <cassert>

// #define DEBUG
#ifdef DEBUG
  #define D(...) logger.log( __VA_ARGS__ )
  #define INFO(...) D(0, __VA_ARGS__)
#else
  #define D(...) do {} while (0)
  #define INFO(...) logger.log(1, __VA_ARGS__)
#endif


namespace cosa {

namespace unsat_enum {


bool TermExtractor::Skip(const smt::Term & ast) {
  return IN(ast, walked_nodes_);
}

void TermExtractor::PreChild(const smt::Term & ast) {
  assert(!IN(ast, walked_nodes_));
  //walked_nodes_.emplace(ast, node_info_t() );
}

void TermExtractor::PostChild(const smt::Term & ast) {
  // check if it is leaf

  walked_nodes_.emplace(ast, node_info_t() );

  unsigned width;
  auto sort_kind = ast->get_sort()->get_sort_kind() ;
  if ( sort_kind == smt::SortKind::BOOL)
    width = 1; // also make it bv?
  else if (sort_kind == smt::SortKind::BV)
    width = ast->get_sort()->get_width();
  else
    return ; // it is for example array, we don't handle

  if (ast->is_symbolic_const()) {
    // walked_nodes_[ast].level = 0; // default 0
    if (IN(ast,related_vars_)) {
      walked_nodes_[ast].in = true;
      width_to_terms_[width].push_back(ast);
    }
  } else if ( ast->is_value() ) {

    walked_nodes_[ast].in = true;
    if (collect_constants_ ) {
      width_to_constants_[width].push_back(ast);
    }
  } else { // we will hope it is op
    unsigned max_level = 0;
    bool all_in = true;
    D(0, "Walk : {} ", ast->to_raw_string());

    for(auto && p : *ast) { // for each of its child node

      D(0, "  - Child : {} , lv: {} , in: {}", p->to_raw_string(), walked_nodes_[p].level, walked_nodes_[p].in);
      max_level = std::max( walked_nodes_[p].level, max_level );
      all_in &= walked_nodes_[p].in;
    }

    if (level_ > 0)
      ++ max_level; // if given level_ > 0, then we will count lv, otherwise, we don't care

    walked_nodes_[ast].in = all_in;
    walked_nodes_[ast].level = max_level;

    D(0, "Result lv: {} , in: {} ", max_level, all_in);

    if (max_level <= level_ && all_in) {
      width_to_terms_[width].push_back(ast);
    }
  } // end of op
} // PostChild


} // namespace unsat_enum

} // namespace cosa