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
  GlobalTimer.RegisterEventStart("TermLearner.NewTerm", 0);
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
  GlobalTimer.RegisterEventEnd("TermLearner.NewTerm", delta_term_num);
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
        ParentExtract::RegisterNewParentRelation(t, new_term);
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

struct old_new_terms {
  smt::TermVec old;
  smt::TermVec noval;
};

unsigned TermLearner::same_val_replace_ast( /*INOUT*/  PerVarsetInfo & varset_info ) {
  unsigned n_new_terms = 0;
  for(auto & width_info_pair : varset_info.terms){
    auto width = width_info_pair.first;
    if (width <= 1)
      continue;
    std::unordered_map<eval_val, old_new_terms, eval_val_hash> eq_class; // equivalent classes

    for (const auto & t : width_info_pair.second.terms) {
      auto v_old = eval_val(solver_->get_value(t)->to_raw_string());
      auto v_new = eval_val(solver_->get_value(to_next_(t))->to_raw_string());
      eq_class[v_old].old.push_back(t);
      eq_class[v_new].noval.push_back(t);
    } // finish saparate into eq classes

    // also check for constants of the same width and insert
    for (auto const & c : width_info_pair.second.constants) {
      auto v = eval_val(c->to_raw_string());
      eq_class[v].old.push_back(c);
    }

    // for each pair, do a replacement and see if new terms can be added
    for( const auto & val_tvec_pair : eq_class) {
      const auto & tvec_old = val_tvec_pair.second.old;
      const auto & tvec_new = val_tvec_pair.second.noval;

#ifdef DEBUG
      std::cout << "EQ class, val: " << val_tvec_pair.first.to_string() <<" w" << width
        << " #old:" << tvec_old.size() <<" |-> #new:" << tvec_new.size() << "\n  * ";
      for(const auto & t : tvec_old)
        std::cout <<t->to_raw_string() << " , ";
      std::cout << " :|old -> new|: ";
      for(const auto & t : tvec_new)
        std::cout <<t->to_raw_string() << " , ";
      std::cout << std::endl;
#endif
      // old -> new & new -> new
      for (const auto & oldterm : tvec_old) {
        for(const auto & newterm : tvec_new) {
          n_new_terms += replace_hierachically(oldterm, newterm, varset_info);
        }
      } // old -> new replacement

      // new -> new replacement

#if 1
      for( unsigned idx1 = 0; idx1 < tvec_new.size(); ++ idx1) {
        for (unsigned idx2 = idx1 + 1; idx2 < tvec_new.size(); ++ idx2) {
          const auto & t1 = tvec_new.at(idx1);
          const auto & t2 = tvec_new.at(idx2);
          
          n_new_terms += replace_hierachically(t1, t2, varset_info);
          n_new_terms += replace_hierachically(t2, t1, varset_info);
        }
      } // new -> new replacement


      for( unsigned idx1 = 0; idx1 < tvec_old.size(); ++ idx1) {
        for (unsigned idx2 = idx1 + 1; idx2 < tvec_old.size(); ++ idx2) {
          const auto & t1 = tvec_old.at(idx1);
          const auto & t2 = tvec_old.at(idx2);
          
          n_new_terms += replace_hierachically(t1, t2, varset_info);
          n_new_terms += replace_hierachically(t2, t1, varset_info);
        }
      } // new -> new replacement
#endif
    } // for each eq class
  } // on each width
  return n_new_terms;
} // same_val_replace_ast


unsigned TermLearner::replace_hierachically(
  const smt::Term & orig, const smt::Term & repl, PerVarsetInfo & varset_info ) {
  smt::TermVec new_terms;
  unsigned ret = replace_hierachically_w_parent(orig, repl, varset_info, new_terms);
  for (const auto & nt : new_terms)
    std::cout << nt->to_raw_string() << std::endl;
  std::cout << "ret = " << ret << std::endl;
  assert(ret == new_terms.size());
  if (ret != 0) {
    ParentExtract extractor;
    for (const auto & t : new_terms) {
      extractor.WalkBFS(t);
    }
  }
  return ret;
}

// let's just make the stack larger
unsigned TermLearner::replace_hierachically_w_parent(
  const smt::Term & orig, const smt::Term & repl, PerVarsetInfo & varset_info,
  smt::TermVec & output_new_terms ) {
  
  assert(!parent_map_.empty());
  auto parent_termvec_pos = parent_map_.find(orig);
  if (parent_termvec_pos == parent_map_.end())
    return 0; // if has no parent term, no replacement
  const auto & parentvec = parent_termvec_pos->second;
  if (parentvec.empty())
    return 0; // if has no parent term, no replacement
  unsigned nterm = 0;

  ParentExtract::parent_map_t new_parent_relation;
  for(const auto & p : parentvec ) {
    if (varset_info.TermLearnerIsOut(p))
      continue;

    smt::TermVec new_terms;
    {
      smt::TermVec old_children;
      std::vector<unsigned> child_pos;
      unsigned idx = 0;
      for(const auto & c : *p) {
        old_children.push_back(c);
        if (c == orig)
          child_pos.push_back(idx);
        ++ idx;
      } // find child pos
      for (auto idx : child_pos) {
        old_children[idx] = repl;
        auto new_parent = (solver_->make_term(p->get_op(), old_children));

        bool is_new_term = varset_info.TermLearnerInsertTerm(new_parent);
        if (is_new_term) {
          output_new_terms.push_back(new_parent);
          new_terms.push_back(new_parent);
        }
        old_children[idx] = orig;
      }
    } // replace_child_in_parent
    for (const auto & nt : new_terms) {
        D(1,"  [TermLearner Replace] {} ==> {}", p->to_raw_string(), nt->to_raw_string());
        nterm += 1 + replace_hierachically_w_parent(p, nt, varset_info,output_new_terms );
          //ParentExtract::RegisterNewParentRelation(c, out.back());
    }
  }
  return nterm;
} // replace_hierachically


} // namespace unsat_enum

} // namespace cosa

