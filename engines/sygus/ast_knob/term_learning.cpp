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
 ** \brief Term Learning from Cexs
 **
 ** 
 **/
 
#include "term_learning.h"
#include "term_extract.h"

#include "engines/apdr/config.h"
#include "engines/apdr/support.h"
#include "utils/container_shortcut.h"
#include "utils/multitimer.h"
#include "utils/logger.h"


#include <cassert>

namespace cosa {

namespace unsat_enum {

TermLearner::to_full_model_map_t TermLearner::to_full_model_map;

// return learned new terms
unsigned TermLearner::learn_terms_from_cex(Model * pre, Model * post, /*OUTPUT*/  PerVarsetInfo & varset_info ) {
  // you will need the full model of pre !
  assert(IN(pre, to_full_model_map));
  Model * full_pre = to_full_model_map.at(pre);
  auto pre_prop = full_pre->to_expr_btor(solver_);
  auto post_prop = NOT(to_next_(post->to_expr_btor(solver_)));
  unsigned delta_term_num = 0;
  D(0, "[TermLearner] Pre model : {}", full_pre->to_string() );
  D(0, "[TermLearner] Post model : {}", post->to_string() );
  solver_->push();
    solver_->assert_formula(pre_prop);
    solver_->assert_formula(trans_);
    solver_->assert_formula(post_prop);
    auto res = solver_->check_sat();
    assert(res.is_sat());
    // okay now we need to find the right model on terms
    delta_term_num += concat_to_extract(varset_info);
    delta_term_num += same_val_replace_ast(varset_info);
    delta_term_num += extract_complement(varset_info);

  solver_->pop();
  D(0, "  [TermLearner] Learn new terms #{}", delta_term_num);
  return delta_term_num;  
} // learn_terms_from_cex

// helper function : get op
static smt::Op get_op(const smt::Term & ast) {
  smt::Op op;

  try {
    op = ast->get_op();
  } catch (NotImplementedException) {
    // op will be initialized correctly
    // so do nothing here
  }
  return op;
}

#define ARG1            \
      auto ptr = t->begin();    \
      auto a1  = *(ptr++);      \
      assert (ptr == t->end());

#define ARG2            \
      auto ptr = t->begin();    \
      auto a1  = *(ptr++);      \
      auto a2  = *(ptr++);      \
      assert (ptr == t->end());

unsigned TermLearner::concat_to_extract(/*INOUT*/  PerVarsetInfo & varset_info) {
  unsigned nterm = 0; 
  for(auto & width_info_pair : varset_info.terms){
    if (width_info_pair.first <= 1)
      continue; // you will not expect to have concat here
    const auto & terms = width_info_pair.second.terms;
    std::vector<std::pair<unsigned, unsigned>> extract_positions;
    for (const auto & t : terms) {
      // if it is concat, make extract ?
      if (!t->is_symbolic_const() && !t->is_value() && !t->is_param() &&
          t->begin() != t->end() && 
          (get_op(t).prim_op == smt::PrimOp::Concat)
          ) {
        
          ARG2
          unsigned sep = a2->get_sort()->get_width();
          unsigned msb = a1->get_sort()->get_width() + sep;
          // assert(sep>=1);
          extract_positions.push_back(std::make_pair(sep-1,0));
          extract_positions.push_back(std::make_pair(msb-1,sep));
      }
    } // end of for each term
    // okay, now, we will add the extract there
    for (const auto & t : terms) {
      for (const auto & pos : extract_positions) {
        auto new_term = solver_->make_term(smt::Op(smt::PrimOp::Extract, pos.first, pos.second), t);
        nterm += varset_info.TermLearnerInsertTerm(new_term) ? 1 : 0;
      } // for each postion
    } // for each term
  } // for each width
  return nterm;
} // concat_to_extract concat (v1, v2)  
// concat (extract(v, 6,0), extract(v,7,7) )
// concat (extract(v, 7,1), extract(v,0,0) )

unsigned TermLearner::extract_complement(/*INOUT*/  PerVarsetInfo & varset_info) {
  return 0; // not implemented
}


unsigned TermLearner::same_val_replace_ast( /*INOUT*/  PerVarsetInfo & varset_info ) {
  unsigned new_terms = 0;
  for(auto & width_info_pair : varset_info.terms){
    auto width = width_info_pair.first;
    if (width <= 1)
      continue;
    std::unordered_map<eval_val, std::vector<smt::Term>, eval_val_hash> eq_class; // equivalent classes

    for (const auto & t : width_info_pair.second.terms) {
      auto v = eval_val(solver_->get_value(to_next_(t))->to_raw_string());
      eq_class[v].push_back(t);
    } // finish saparate into eq classes

    // also check for constants of the same width and insert
    for (auto const & c : width_info_pair.second.constants) {
      auto v = eval_val(c->to_raw_string());
      eq_class[v].push_back(c);
    }

    // for each pair, do a replacement and see if new terms can be added
    for( const auto & val_tvec_pair : eq_class) {
      const auto & tvec = val_tvec_pair.second;

#ifdef DEBUG
      std::cout << "EQ class, val: " << val_tvec_pair.first.to_string() << " #:" << tvec.size() << "\n  * ";
      for(const auto & t : tvec)
        std::cout <<t->to_raw_string() << " , ";
      std::cout << std::endl;
#endif

      for( unsigned idx1 = 0; idx1 < tvec.size(); ++ idx1) {
        for (unsigned idx2 = idx1 + 1; idx2 < tvec.size(); ++ idx2) {
          const auto & t1 = tvec.at(idx1);
          const auto & t2 = tvec.at(idx2);
          
          new_terms += replace_hierachically(t1, t2, varset_info);
          new_terms += replace_hierachically(t2, t1, varset_info);
        }
      }
    } // for each eq class
  } // on each width
  return new_terms;
} // same_val_replace_ast

static bool replace_child_in_parent(smt::SmtSolver & solver_, 
  const smt::Term & child_old, const smt::Term & child_new,
  const smt::Term & parent,
  smt::TermVec & out)
{
  smt::TermVec old_children;
  std::vector<unsigned> child_pos;
  unsigned idx = 0;
  for(const auto & c : *parent) {
    old_children.push_back(c);
    if (c == child_old)
      child_pos.push_back(idx);
    ++ idx;
  }
  for (auto idx : child_pos) {
    old_children[idx] = child_new;
    out.push_back(solver_->make_term(parent->get_op(), old_children));
    old_children[idx] = child_old;
  }
  return !child_pos.empty();
} // replace_child_in_parent

// let's just make the stack larger
unsigned TermLearner::replace_hierachically(
  const smt::Term & orig, const smt::Term & repl, PerVarsetInfo & varset_info ) {
  
  assert(!parent_map_.empty());
  auto parent_termvec_pos = parent_map_.find(orig);
  if (parent_termvec_pos == parent_map_.end())
    return 0; // if has no parent term, no replacement
  const auto & parentvec = parent_termvec_pos->second;
  if (parentvec.empty())
    return 0; // if has no parent term, no replacement
  unsigned nterm = 0;
  for(const auto & p : parentvec) {
    if (varset_info.TermLearnerIsOut(p))
      continue;

    smt::TermVec new_terms;
    replace_child_in_parent(solver_, orig, repl, p, new_terms);
    for (const auto & new_term : new_terms) {
      nterm += varset_info.TermLearnerInsertTerm(new_term) ? 1 : 0;
      nterm += replace_hierachically(p, new_term, varset_info);
    }
  }
  return nterm;
} // replace_hierachically


} // namespace unsat_enum

} // namespace cosa

