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
 ** \brief parital eval tree
 **
 ** 
 **/

#include "utils/logger.h"
#include "evalcond.h"
#include "container_shortcut.h"

#include <cassert>
#include <queue>

namespace cosa {


// ------------------------------- // 
//
//    PartialEvalTreeWalker
//
// ------------------------------- // 

PartialEvalTreeWalker::PartialEvalTreeWalker(smt::SmtSolver & solver):
  solver_(solver) {
  // do nothing
}

PartialEvalTreeWalker::~PartialEvalTreeWalker() {
  for (auto ptr : node_allocation_table) {
    assert (ptr);
    delete (ptr);
  }
}

void PartialEvalTreeWalker::PreChild(const smt::Term & ast) {
  // do nothing
} // PartialEvalTreeManager::PreChild

bool PartialEvalTreeWalker::Skip(const smt::Term & ast) {
  return IN(ast, node_tree_buffer);
}

void PartialEvalTreeWalker::merge_node(ParitalEvalTreeNode * node, ParitalEvalTreeNode * subtree) {
  for (const auto & v : subtree->vars)
    node->vars.insert(v);
  for (const auto & p : subtree->condition_map) {
    for (const auto & subtsub : p.second)
      node->condition_map[p.first].insert(subtsub);
  }
} // merge_node


ParitalEvalTreeNode * PartialEvalTreeWalker::get_node(const smt::Term & n) const {
  assert (IN(n,node_tree_buffer));
  return node_tree_buffer.at(n);
}


// some MACROS to help with these
#define NEG(x) (solver_->make_term(smt::Not,(x)))
#define ARG2(a1,a2)            \
      auto ptr = ast->begin();    \
      auto a1  = *(ptr++);      \
      auto a2  = *(ptr++);      \
      assert (ptr == ast->end()); \
      ParitalEvalTreeNode * subtree_##a1 = get_node(a1); \
      ParitalEvalTreeNode * subtree_##a2 = get_node(a2);

#define ARG3(a1,a2,a3)            \
      auto ptr = ast->begin();    \
      auto a1  = *(ptr++);      \
      auto a2  = *(ptr++);      \
      auto a3  = *(ptr++);      \
      assert (ptr == ast->end()); \
      ParitalEvalTreeNode * subtree_##a1 = get_node(a1); \
      ParitalEvalTreeNode * subtree_##a2 = get_node(a2); \
      ParitalEvalTreeNode * subtree_##a3 = get_node(a3);

void PartialEvalTreeWalker::PostChild(const smt::Term & ast) {
  // root case
  //   - if it is symbol 
  //   - ow add an empty node
  assert (!IN(ast,node_tree_buffer));

  ParitalEvalTreeNode * node = new ParitalEvalTreeNode();
  node_allocation_table.push_back(node);

  smt::Op op = ast->get_op();
  if (op.is_null()) { // this is the root node
    if (ast->is_symbolic_const()) {
      node->vars.insert(ast);
    }
  } else {
    // non root case
    //   - if it is Ite, And, Or, BvAnd ( EQ 0, ow), BvOr ( EQ 1...1, ow)
    //      construct the condition accordingly
    //   - ow merge v & merge conditions
    
    if (op.prim_op == smt::PrimOp::Ite) {
      ARG3(cond, texpr, fexpr)

      merge_node(node, subtree_cond);
      // connect the true and false branch
      // cond -> true_branch,
      // ~cond ->  ~false_branch
      node->condition_map[cond].insert(subtree_texpr);
      node->condition_map[NEG(cond)].insert(subtree_fexpr);

    } else if (op.prim_op == smt::PrimOp::Implies) {
      ARG2(arg0,arg1)

      node->condition_map[arg0].insert(subtree_arg1);
      // only when it is true, the second half matters (~true) || ...
      node->condition_map[NEG(arg1)].insert(subtree_arg0);

    } else if (op.prim_op == smt::PrimOp::And) {
      ARG2(arg0,arg1)
      // if arg0 is 0, it has nothing to do with the other side
      node->condition_map[arg0].insert(subtree_arg1);
      node->condition_map[arg1].insert(subtree_arg0);
    } else if (op.prim_op == smt::PrimOp::Or) {
      ARG2(arg0,arg1)
      // only if arg0 is 0 (NEG(arg0) is true), it has something to do with other side
      node->condition_map[NEG(arg0)].insert(subtree_arg1);
      node->condition_map[NEG(arg1)].insert(subtree_arg0);
    } else if (op.prim_op == smt::PrimOp::BVAnd || op.prim_op == smt::PrimOp::BVNand) {
      ARG2(arg0,arg1)
      auto zero = solver_->make_term(0, ast->get_sort() );
      auto arg0_eq_zero = solver_->make_term(smt::BVComp, arg0, zero);
      auto arg1_eq_zero = solver_->make_term(smt::BVComp, arg1, zero);
      node->condition_map[NEG(arg0_eq_zero)].insert(subtree_arg1);
      node->condition_map[NEG(arg1_eq_zero)].insert(subtree_arg0);     
    } else if (op.prim_op == smt::PrimOp::BVOr  || op.prim_op == smt::PrimOp::BVNor) {
      ARG2(arg0,arg1)
      std::string binary_all_one;
      for (uint64_t idx = 0; idx < ast->get_sort()->get_width(); ++ idx)
        binary_all_one += "1";
      
      auto allone = solver_->make_term(binary_all_one, ast->get_sort(), 2 );
      auto arg0_eq_one = solver_->make_term(smt::BVComp, arg0, allone);
      auto arg1_eq_one = solver_->make_term(smt::BVComp, arg1, allone);
      node->condition_map[NEG(arg0_eq_one)].insert(subtree_arg1);
      node->condition_map[NEG(arg1_eq_one)].insert(subtree_arg0);     
    } else { // ow. merging the conditions/variables
      for (const auto & child : *ast) {
        // get its childs tree node
        ParitalEvalTreeNode * subtree = get_node(child);
        merge_node(node, subtree);
      }
    } // merging
  }

  node_tree_buffer.insert(std::make_pair(ast, node));

} // PartialEvalTreeManager::PreChild



// ------------------------------- // 
//
//    PartialEvalTreeManager
//
// ------------------------------- // 


PartialEvalTreeManager::PartialEvalTreeManager(smt::SmtSolver & solver):
  solver_(solver), walker_(solver) {

} // PartialEvalTreeManager::PartialEvalTreeManager

PartialEvalTreeManager::~PartialEvalTreeManager() {
  for (auto ptr : node_allocation_table) {
    assert (ptr);
    delete (ptr);
  }
}

// some MACROS to help with these
#define AND(x,y) (solver_->make_term(smt::And,(x),(y)))

FlattenedParitalEvalTreeNode * 
PartialEvalTreeManager::get_flatten_varlist(const smt::Term & ast) {
  walker_.WalkRecursion(ast);
  ParitalEvalTreeNode * unflattened_tree = walker_.get_node(ast);
  auto pos = node_tree_buffer.find(unflattened_tree);
  if (pos != node_tree_buffer.end())
    return pos->second;
  // o.w. we need to flatten,
  // but do check for internal nodes if they are in the buffer
  FlattenedParitalEvalTreeNode * node = new FlattenedParitalEvalTreeNode;

  // even if we approach a node twice, we may have to do it twice
  // as the parent condition could be different

  // the parent conditions, and the node to walk
  std::queue<std::pair<smt::Term, ParitalEvalTreeNode *> > walk_queue;
  auto top_level_true = solver_->make_term(true);
  walk_queue.push(std::make_pair( top_level_true, unflattened_tree));
  while(!walk_queue.empty()) {
    const auto & cond_node_pair = walk_queue.front();
    const auto & cond = cond_node_pair.first;
    const auto & nodeptr = cond_node_pair.second;

    auto buffer_pos = node_tree_buffer.find(nodeptr);
    if (buffer_pos != node_tree_buffer.end()) {
      // copy that result to the root node,
      if (cond == top_level_true) {
        // let's do a short cut
        node->vars.insert(buffer_pos->second->vars.begin(), buffer_pos->second->vars.end());
        for (auto && cond_vars_pair : buffer_pos->second->condition_map)
          node->condition_map[cond_vars_pair.first].insert(cond_vars_pair.second.begin(),cond_vars_pair.second.end() );
        // for each condition, insert them to the top level condition-var map
      } else {
        node->condition_map[cond].insert(buffer_pos->second->vars.begin(), buffer_pos->second->vars.end());
        for (auto && cond_vars_pair : buffer_pos->second->condition_map)
          node->condition_map[AND(cond,cond_vars_pair.first)].insert(cond_vars_pair.second.begin(),cond_vars_pair.second.end() );
      }
      // and we don't need to dive into it
      walk_queue.pop();
      continue;
    } // else, we will need to (insert the vars w. cond -> condition map)
    // deal with its child
    if (cond == top_level_true)
      node->vars.insert(nodeptr->vars.begin(), nodeptr->vars.end());
    else
      node->condition_map[cond].insert(nodeptr->vars.begin(), nodeptr->vars.end());
    for(auto && cond_nodes_pair : nodeptr->condition_map) {
      const auto & low_level_cond = cond_nodes_pair.first;
      const auto & nodes = cond_nodes_pair.second;
      for (auto && node : nodes) {
        auto new_cond = cond == top_level_true ? low_level_cond : AND(cond, low_level_cond);
        walk_queue.push(std::make_pair(new_cond, node));
      }
    }
    walk_queue.pop();
  } // while queue not empty

  // finally remove vars from conds if they are in non-cond
  auto condition_map_pos = node->condition_map.begin();
  while (condition_map_pos !=  node->condition_map.end()) {
    // if its var is in the parent no condition case
    auto var_pos = condition_map_pos->second.begin();
    while (var_pos != condition_map_pos->second.end()) {
      if (IN(*var_pos, node->vars)) {
        var_pos = condition_map_pos->second.erase(var_pos);
      } else {
        ++ var_pos;
      }
    }
    // to remove the case, where there is only an empty left
    if (condition_map_pos->second.empty()) {
      condition_map_pos = node->condition_map.erase(condition_map_pos);
    } else 
      ++condition_map_pos;
  }
  
  node_tree_buffer.insert(std::make_pair(unflattened_tree, node));
  return node;
}



void PartialEvalTreeManager::DebugDumpTree(const smt::Term & ast) {
  FlattenedParitalEvalTreeNode * tree = get_flatten_varlist(ast);
  logger.log(0, "-------------------------------------------");
  logger.log(0, "Expr : {}", ast->to_string());
  logger.log(0, "Tree : top nodes:");
  for (const auto & v: tree->vars)
    logger.log(0, "\t{}", v->to_string());
  logger.log(0, "     : cond-var pair");
  for (const auto & c_vs_pair: tree->condition_map) {
    logger.log(0, "\t{}", c_vs_pair.first->to_string());
    for (const auto & v: c_vs_pair.second)
      logger.log(0, "\t\t{}", v->to_string());
  }
  logger.log(0, "-------------------------------------------");
}









} // namespace cosa