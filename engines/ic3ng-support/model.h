#pragma once

#include "smt-switch/smt.h"

#include "engines/ic3ng-support/cex_info_map.h"

namespace pono {

struct Model;

struct ic3_rel_ind_check_result{
  bool not_hold;
  Model * prev_ex;
  ic3_rel_ind_check_result(bool sat, Model * pre) :
    not_hold(sat), prev_ex(pre) {}
  // if sat at init, prev_ex = in cube (of course)
};


// NOTE: the vars here could be (_ extract ...)
struct Model {

  static std::string compute_vars_canonical_string(
    const std::unordered_set<smt::Term> & varset);

private: 
  // none cache version, usually
  // should not be used from outside
  // this is to make sure the cache
  // thing is not accidentally broken
  smt::Term _to_expr(smt::SmtSolver & solver_);

public:
  // the following use cache, NOTE: it does not contain NOT!!!
  smt::Term to_expr(smt::SmtSolver & btor_solver_);
  const smt::TermVec & to_expr_conj() const { return conjs; }
  std::string to_string() const;
  
  // these are pre-computed and stored in var_info_
  std::string get_var_canonical_string() const { return var_info_->vars_canonical_string; }
  const std::unordered_set<smt::Term> & get_varset_sliced() const {  return var_info_->slicedvars_in_cex; }
  const std::unordered_set<smt::Term> & get_varset_unslice () const { 
    return var_info_->unsliced_varinfo->vars_in_cex;
  }


  // constructors
  // Model() : expr_cached_(NULL) {}
  // Model(const Model &m) : conjs(m.conjs), expr_cached_(m.expr_cached_) {}
  // by default, move var_val_map to avoid copy
  Model(smt::TermVec && eqs, 
    PerSlicedVarInfo * var_info_ptr) : conjs(eqs) , var_info_(var_info_ptr) { var_info_ptr->unsliced_varinfo->ref_count++; }
  
  PerSlicedVarInfo * get_per_slicedvar_info() const { return var_info_; }
  PerUnslicedVarInfo * get_per_unslicedvar_info() const { return var_info_->unsliced_varinfo; }
  // Model(smt::SmtSolver & solver_, 
  //   const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice, // extract using these vars
  //   const std::unordered_map<smt::Term, smt::Term> & varmap // but use the map in here for the vars
  // );

  // return true, if it really exists
  // bool erase_var(const smt::Term & v);  // depending if v is ((_ extract ) ...), erase that one
  //                                      // if v is a var, erase all containing the var

protected:
  smt::TermVec conjs;
  // cache expr result
  smt::Term expr_cached_;
  PerSlicedVarInfo * var_info_;
};

std::ostream & operator<< (std::ostream & os, const Model & m);

}
