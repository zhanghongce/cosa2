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
 ** \brief parital model generation
 **
 ** 
 **/

#pragma once

#include "smt-switch/smt.h"

#include <vector>

namespace cosa {

typedef std::unordered_map<smt::Term, smt::Term> cube_t;
struct Model {
  cube_t cube;
  std::string to_string() const;
  std::string vars_to_canonical_string() const;
  void get_varset(std::unordered_set<smt::Term> & varset) const;
  smt::Term to_expr(smt::SmtSolver & solver_);
  static smt::Term to_expr(const cube_t & c, smt::SmtSolver & solver_);
  static smt::Term to_expr_translate(
      const cube_t & c, smt::SmtSolver & solver_,
      smt::TermTranslator & to_msat);

  // the following two use cache
  smt::Term to_expr_btor(smt::SmtSolver & btor_solver_);
  smt::Term to_expr_msat(smt::SmtSolver & msat_solver_, smt::TermTranslator & to_msat);

  // constructors
  Model() : expr_btor_(NULL), expr_msat_(NULL) {}
  Model(const Model &m) : cube(m.cube), expr_btor_(m.expr_btor_), expr_msat_(m.expr_msat_) {}
  // from get value from a solver
  Model(smt::SmtSolver & solver_, const std::unordered_set<smt::Term> & varset);
  Model(smt::SmtSolver & solver_, 
    const std::unordered_set<smt::Term> & varset, // extract using these vars
    const std::unordered_map<smt::Term, smt::Term> & varmap // but use the map in here for the vars
    );
  // return true, if it really exists
  bool erase_var(const smt::Term & v);

  static smt::Term bool_to_bv(const smt::Term & t, smt::SmtSolver & solver_);
  static smt::Term bv_to_bool(const smt::Term & t, smt::SmtSolver & solver_);
  
protected:
  // cache expr result
  smt::Term expr_btor_;
  smt::Term expr_msat_;


};

typedef std::shared_ptr<Model> ModelPtr;

std::ostream & operator<< (std::ostream & os, const Model & m);


struct CondVarBuffer {
  typedef std::unordered_set<smt::Term> vars_t;
  typedef std::unordered_map<smt::Term, std::unordered_set<smt::Term>> condition_map_t;
  // make sure if a symbol exists in vars_t, it is not in any condition map
  // because there is no need for its appearance
  vars_t vars;
  condition_map_t condition_map;
}; // ParitalEvalTreeNode

class PartialModelGen {
public:

protected:
  // let's keep a reference to the solver since we need to add terms
  smt::SmtSolver & solver_;

  // for the DFS, will not use the stack but use one reference here
  std::unordered_set<smt::Term> dfs_walked_;
  std::unordered_set<smt::Term> dfs_vars_;
  bool use_cache_;
  void dfs_walk(const smt::Term & ast);

  // conditon var buffer
  std::unordered_map<smt::Term, CondVarBuffer *> node_buffer_;
  std::vector<CondVarBuffer *> node_allocation_table_;
  std::vector<std::unordered_set<smt::Term>> dfs_variable_stack_;
  CondVarBuffer * cur_node_;
  bool not_in_parent_vars(const smt::Term & var);
  void dfs_bufwalk(const smt::Term & ast, const smt::Term & cond);
  void cur_node_insert_back(const smt::Term & cond);

  void GetVarList(const smt::Term & ast, bool use_cache = true);

public:

  PartialModelGen(smt::SmtSolver & solver);
  virtual ~PartialModelGen();
  // disallow copy construct/assign
  PartialModelGen(const PartialModelGen &) = delete;
  PartialModelGen & operator=(const PartialModelGen &) = delete;

  void GetVarList(const smt::Term & ast, 
    std::unordered_set<smt::Term> & out_vars, bool use_cache = true);

  void GetVarListForAsts(const smt::TermVec & asts, 
    smt::UnorderedTermSet & out_vars, bool use_cache = true);

  // get a partial model and put in the cube
  void GetPartialModel(const smt::Term & ast, cube_t & m, bool use_cache = true);

  /// caching 
  void CacheNode(const smt::Term & ast);
  CondVarBuffer * CheckCache(const smt::Term & ast) const;
  void InterpretCache(CondVarBuffer * n, std::unordered_set<smt::Term> & var);

  // add an API to use buffers 
};


}  // namespace cosa