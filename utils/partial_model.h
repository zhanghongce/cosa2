/*********************                                                  */
/*! \file partial_model.h
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class for performing dynamic cone of influence reduction based
**        on the model from the solver. This is essentially extracting a
**        partial model. (see tests/test_partial_model.cpp for usage)
**
**/

#pragma once

#include "utils/sygus_ic3formula_helper.h"
#include "engines/ic3base.h"

namespace pono {

class PartialModelGen {

private:
  struct hash_pair {
    template <class T1, class T2>
    size_t operator()(const std::pair<T1, T2>& p) const
    {
        auto hash1 = std::hash<T1>{}(p.first);
        auto hash2 = std::hash<T2>{}(p.second);
 
        if (hash1 != hash2) {
            return hash1 ^ hash2;             
        }
         
        // If hash1 == hash2, their XOR is zero.
          return hash1;
    }
  }; // end of hash_pair
  typedef std::unordered_set<std::pair<int, int>, hash_pair> pair_set;

public:
  /** This class computes the cone of influence on construction
   *  The current implementation does not have internal cache,
   *  but in the future maybe we can cache some of the results
   *  @param the solver where the assertions were made
   */
  PartialModelGen(smt::SmtSolver & solver) : solver_(solver) { }
    
  // disallow copy construct/assign
  PartialModelGen(const PartialModelGen &) = delete;
  PartialModelGen & operator=(const PartialModelGen &) = delete;
  
protected:
  // let's keep a reference to the solver since we need to add terms
  smt::SmtSolver & solver_;
  // void GetVarList_coi_extract(const smt::Term & ast, 
  // std::unordered_set<smt::Term> & out_vars,std::vector<std::pair<std::string,std::string>> & varset_slice);
  // void op_Extract(smt::Term ast,smt::TermVec & node_stack_,std::vector<std::pair<std::string,std::string>> & varset_slice);
  // for the DFS, will not use the stack but use one reference here
  std::unordered_set<smt::Term> dfs_walked_;
  std::unordered_set<smt::Term> dfs_vars_;
  std::unordered_map<smt::Term, pair_set> dfs_walked_extract;

  void dfs_walk(const smt::Term & ast);
  void dfs_walk_bitlevel(const smt::Term & input_ast, int high, int low, 
    std::unordered_map<smt::Term, pair_set> & varset_slice);
  // conditon var buffer
  void GetVarList(const smt::Term & ast);
public:

  /** This class computes the variables that need to
   *  appear in the partial model of ast
   *  @param the ast to walk
   *  @param (output) the set of variables
   */
  void GetVarList(const smt::Term & ast, 
    std::unordered_set<smt::Term> & out_vars);

  void GetVarListForAsts_in_bitlevel(
    const std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> & input_asts_slices, 
    std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice);

  /** This class computes the variables that need to
   *  appear in the partial model of asts in the vector
   *  @param the vector of ast to walk
   *  @param (output) the set of variables
   */
  void GetVarListForAsts(const smt::TermVec & asts, 
    smt::UnorderedTermSet & out_vars);

  /** This class computes the variables that need to
   *  appear in the partial model of asts in the vector
   *  @param the ast to walk
   *  @return the partial model in ic3formula
   */
  IC3Formula GetPartialModel(const smt::Term & ast);

  /** This class computes the variables that need to
   *  appear in the partial model of asts in the vector
   *  @param the ast to walk
   *  @return the partial model and the var/val cube
   */
  std::pair<IC3Formula,syntax_analysis::IC3FormulaModel> 
    GetPartialModelInCube(const smt::Term & ast);


  /** This class computes the variables that need to
   *  appear in the partial model of asts in the vector
   *  @param the ast to walk
   *  @return the partial model in ic3formula
   */
  IC3Formula GetPartialModel_bitlevel(const smt::Term & ast);

  /** This class computes the variables that need to
   *  appear in the partial model of asts in the vector
   *  @param the ast to walk
   *  @return the partial model and the var/val cube
   */
  std::pair<IC3Formula,syntax_analysis::IC3FormulaModel> 
    GetPartialModelInCube_bitlevel(const smt::Term & ast);

  // add an API to use buffers 
 
};

}  // namespace pono
