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
typedef std::unordered_map<smt::Term, smt::Term> cube_t;
struct Model {

  static std::string compute_vars_noslice_canonical_string(
    const std::unordered_set<smt::Term> & varset);
  static void compute_varset_noslice(
    const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice,
    std::unordered_set<smt::Term> & varset);  // will remove (_ extract )

private: 
  // none cache version, usually
  // should not be used from outside
  // this is to make sure the cache
  // thing is not accidentally broken
  smt::Term _to_expr(smt::SmtSolver & solver_);

public:
  // the following use cache, NOTE: it does not contain NOT!!!
  smt::Term to_expr(smt::SmtSolver & btor_solver_);
  void to_expr_conj(smt::SmtSolver & btor_solver_, smt::TermVec & out) const;
  std::string to_string() const;
  
  // these are pre-computed and stored in var_info_
  std::string get_var_noslice_canonical_string() const { return var_info_->vars_noslice_canonical_string; }
  const std::unordered_set<smt::Term> & get_varset_noslice() const {  return var_info_->vars_noslice_in_cex; }

  // these are computed
  std::string get_var_canonical_string() const;
  void get_varset(std::unordered_set<smt::Term> & varset) const;

  // constructors
  // Model() : expr_cached_(NULL) {}
  Model(const Model &m) : cube(m.cube), expr_cached_(m.expr_cached_) {}
  // from get value from a solver
  Model(smt::SmtSolver & solver_, 
    const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice,
    PerVarInfo * var_info_ptr);
  // Model(smt::SmtSolver & solver_, 
  //   const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice, // extract using these vars
  //   const std::unordered_map<smt::Term, smt::Term> & varmap // but use the map in here for the vars
  // );

  // return true, if it really exists
  // bool erase_var(const smt::Term & v);  // depending if v is ((_ extract ) ...), erase that one
  //                                      // if v is a var, erase all containing the var

protected:
  cube_t cube;
  // cache expr result
  smt::Term expr_cached_;
  PerVarInfo * var_info_;

};

std::ostream & operator<< (std::ostream & os, const Model & m);

}
