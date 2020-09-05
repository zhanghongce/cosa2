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
 
#pragma once

#include "common.h"

namespace cosa {

namespace unsat_enum {

// you may also want to register the model -> full model map

class TermLearner {
public: // -- static -- model-to-model map
   typedef std::unordered_map<Model *, Model *> to_full_model_map_t;
   static void RegisterPartialToFullModelMap(Model * pre, Model * post) {
     to_full_model_map.emplace(pre, post); }
   static void ClearCache() { to_full_model_map.clear(); }

   using parent_map_t = ParentExtract::parent_map_t;

protected:
   static to_full_model_map_t to_full_model_map;

public:
  TermLearner(const smt::Term & trans_btor, to_next_t to_next_func, 
      //cex_term_map_t & cex_pred_map, 
      smt::SmtSolver & btor, const parent_map_t & parent_map) : 
    trans_(trans_btor), to_next_(to_next_func),
    // cex_pred_map_ref_(cex_pred_map),
    solver_(btor),
    parent_map_(parent_map) {}
    
  unsigned learn_terms_from_cex(Model * pre, Model * post, /*OUTPUT*/  PerVarsetInfo & varset_info );
  
protected:
  smt::Term trans_;
  to_next_t to_next_;
  //cex_term_map_t & cex_pred_map_ref_; // from unsat enum
  smt::SmtSolver & solver_;
  const parent_map_t & parent_map_; // ParentExtract
  
protected:
  unsigned same_val_replace_ast( /*INOUT*/  PerVarsetInfo & varset_info );
  unsigned replace_hierachically(
    const smt::Term & orig, const smt::Term & repl, /*INOUT*/  PerVarsetInfo & varset_info );
  
  unsigned concat_to_extract(/*INOUT*/  PerVarsetInfo & varset_info);
  unsigned extract_complement(/*INOUT*/  PerVarsetInfo & varset_info);

}; // class TermLearner
  
} // namespace unsat_enum

} // namespace cosa
