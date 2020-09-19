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
#include "utils/term_analysis.h"

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

// ---------------------------------------------- //
//                                                //
//              TermExtractor                     //
//                                                //
// ---------------------------------------------- //

bool TermExtractor::Skip(const smt::Term & ast) {
  return IN(ast, walked_nodes_);
}

void TermExtractor::PreChild(const smt::Term & ast) {
  assert(!IN(ast, walked_nodes_));
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
      walked_nodes_[ast].related = true;
      width_to_terms_[width].push_back(ast);
      all_terms_.insert(ast);
    }
  } else if ( ast->is_value() ) {

    walked_nodes_[ast].in = true;
    if (collect_constants_ ) {
      width_to_constants_[width].push_back(ast);
    }
  } else { // we will hope it is op
    unsigned max_level = 0;
    bool all_in = true;
    // bool some_in = false;
    D(0, "Walk : {} ", ast->to_raw_string());

    for(auto && p : *ast) { // for each of its child node

      D(0, "  - Child : {} , lv: {} , in: {}", p->to_raw_string(), walked_nodes_[p].level, walked_nodes_[p].in);
      max_level = std::max( walked_nodes_[p].level, max_level );
      all_in &= walked_nodes_[p].in;
    //  some_in |= walked_nodes_[p].related;
    }

    if (level_ > 0)
      ++ max_level; // if given level_ > 0, then we will count lv, otherwise, we don't care

    walked_nodes_[ast].in = all_in;
    // walked_nodes_[ast].related = some_in;
    walked_nodes_[ast].level = max_level;

    D(0, "Result lv: {} , in: {} , related: {}", max_level, all_in, some_in);

    if (max_level <= level_ && all_in) {
      width_to_terms_[width].push_back(ast);
      all_terms_.insert(ast);
    }
    //if (max_level <= level_ && some_in) {
    //  related_terms_.insert(ast);
    //}
  } // end of op
} // PostChild

// ---------------------------------------------- //
//                                                //
//              Parent Extract                    //
//                                                //
// ---------------------------------------------- //
ParentExtract::parent_map_t ParentExtract::parent_;

bool ParentExtract::Skip(const smt::Term & ast) {
  return IN(ast, walked_nodes_);
}

void ParentExtract::PreChild(const smt::Term & ast) {
  assert(!IN(ast, walked_nodes_));
 // walked_nodes_.insert(ast);
}

void ParentExtract::PostChild(const smt::Term & ast) {
 // for all its child, add parent pointer to the map
  walked_nodes_.insert(ast);
  if (ast->is_symbolic_const()) { }
  else if ( ast->is_value() ) { } 
  else { // we will hope it is op
    for(auto && p : *ast) { // for each of its child node
      parent_[p].insert(ast);
    } // set up its parent to have ast there
  } // end of op
} // PostChild

// ---------------------------------------------- //
//                                                //
//              Constant Extract                  //
//                                                //
// ---------------------------------------------- //

bool ConstantExtractor::Skip(const smt::Term & ast) {
  return (IN(ast, walked_nodes_));
}

void ConstantExtractor::PreChild(const smt::Term & ast) {
 // walked_nodes_.insert(ast);
}

void ConstantExtractor::PostChild(const smt::Term & ast) {
  walked_nodes_.insert(ast);

  if (! ast->is_value() )
    return;

  unsigned width;
  auto sort_kind = ast->get_sort()->get_sort_kind() ;
  if ( sort_kind == smt::SortKind::BOOL)
    width = 1; // also make it bv?
  else if (sort_kind == smt::SortKind::BV)
    width = ast->get_sort()->get_width();
  else
    return;
  auto ret = constants_strs_.insert(ast->to_raw_string());
  if(ret.second)
    width_constant_map[width].push_back(ast);
} // PostChild

// ---------------------------------------------- //
//                                                //
//              SliceExtractor                    //
//                                                //
// ---------------------------------------------- //

bool SliceExtractor::Skip(const smt::Term & ast) {
  return IN(ast, walked_nodes_);
}

void SliceExtractor::PreChild(const smt::Term & ast) {

}

void SliceExtractor::PostChild(const smt::Term & ast) {
  walked_nodes_.insert(ast);

  if ( ast->is_value() )
    return;
  if ( ast->is_symbolic_const() )
    return;
  
  smt::Op op;
  try {
    op = ast->get_op();
  } catch (NotImplementedException) {
    // op will be initialized correctly
    // so do nothing here
    return;
  }

  if (op.prim_op == smt::PrimOp::Extract) {
    assert (op.num_idx == 2);

    // get its varset
    smt::UnorderedTermSet varset;
    get_free_symbols(ast, varset);
    unsigned l = op.idx0, r = op.idx1;

    bool has_related_vars = false;
    for (const auto & sv : varset) {
      if (IN(sv, related_vars_)) {
        auto w = sv->get_sort()->get_width();
        if(l<w)
          sv2exts_[sv].insert(std::make_pair(l,r));
        has_related_vars = true;
      }
    } // for each var
    if (has_related_vars) {
      auto width = ast->get_sort()->get_width();
      //if (insert_res.second) { // if insertion succeed
      // this is just term buffer, does not matter
      ext_terms_[width].push_back(ast);
      //}
    }

  } // if it is extract (slice)
} // PostChild


} // namespace unsat_enum

} // namespace cosa