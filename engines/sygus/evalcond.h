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

#pragma once

#include "engines/sygus/ast_knob/walker.h"
#include "smt-switch/smt.h"

#include <vector>

namespace cosa {

struct ParitalEvalTreeNode {
  typedef std::unordered_set<smt::Term> vars_t;
  typedef std::unordered_map<smt::Term, 
    std::unordered_set<ParitalEvalTreeNode *>> condition_map_t;

  vars_t vars;
  condition_map_t condition_map;
}; // ParitalEvalTreeNode


struct FlattenedParitalEvalTreeNode {
  typedef std::unordered_set<smt::Term> vars_t;
  typedef std::unordered_map<smt::Term, std::unordered_set<smt::Term>> condition_map_t;
  // make sure if a symbol exists in vars_t, it is not in any condition map
  // because there is no need for its appearance
  vars_t vars;
  condition_map_t condition_map;
}; // ParitalEvalTreeNode


// will manage the buffers explicitly
class PartialEvalTreeWalker : public Walker {
public:
  typedef std::unordered_map<smt::Term, ParitalEvalTreeNode *> node_buffer_t;

  static void merge_node(ParitalEvalTreeNode * node, ParitalEvalTreeNode * subtree);
protected:
  // let's keep a reference to the solver since we need to add terms
  smt::SmtSolver & solver_;
  // we keep a pointer to the allocated nodes, so we will free them correctly
  std::vector<ParitalEvalTreeNode *> node_allocation_table;
  // Map of (smt::Term -> ParitalEvalTreeNode)
  node_buffer_t node_tree_buffer;

public:
  // get node and do sanity check also
  // this is a dangerous interface, the lifetime of the referenced
  // object may go away, I only expect PartialEvalTreeManager will use it
  ParitalEvalTreeNode * get_node(const smt::Term & n) const;

public:
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;
  virtual bool Skip(const smt::Term & ast) override;

  PartialEvalTreeWalker(smt::SmtSolver & solver);
  virtual ~PartialEvalTreeWalker();

  // disallow copy construct/assign
  PartialEvalTreeWalker(const PartialEvalTreeWalker &) = delete;
  PartialEvalTreeWalker & operator=(const PartialEvalTreeWalker &) = delete;

};

// flatten a tree and buffers its flatten result
// flatten on-demand
// we expect we don't need to that very often
class PartialEvalTreeManager {
public:
  typedef std::unordered_map<ParitalEvalTreeNode *, FlattenedParitalEvalTreeNode *> node_buffer_t;
protected:
  // let's keep a reference to the solver since we need to add terms
  smt::SmtSolver & solver_;
  PartialEvalTreeWalker walker_;

  std::vector<FlattenedParitalEvalTreeNode *> node_allocation_table;

  node_buffer_t node_tree_buffer;
  // we only store the root of a query, but will look into it
  // in the next tree flatten process, I expect that we will
  // only build ast on top of existing asts

  FlattenedParitalEvalTreeNode * get_flatten_varlist(const smt::Term & ast);

public:
  PartialEvalTreeManager(smt::SmtSolver & solver);
  virtual ~PartialEvalTreeManager();
  // disallow copy construct/assign
  PartialEvalTreeManager(const PartialEvalTreeManager &) = delete;
  PartialEvalTreeManager & operator=(const PartialEvalTreeManager &) = delete;

  void DebugDumpTree(const smt::Term & ast);
}; // PartialEvalTreeManager 

}  // namespace cosa