#pragma once

#include "smt-switch/smt.h"

namespace pono {

struct ic3_rel_ind_check_result{
  bool not_hold;
  Model * prev_ex;
  ic3_rel_ind_check_result(bool sat, Model * pre) :
    not_hold(sat), prev_ex(pre) {}
  // if sat at init, prev_ex = in cube (of course)
};

typedef std::unordered_map<smt::Term, smt::Term> cube_t;
struct Model {
  cube_t cube;
  std::string to_string() const;
  std::string vars_to_canonical_string() const;
  void get_varset(std::unordered_set<smt::Term> & varset) const;

private: 
  // none cache version, usually
  // should not be used from outside
  // this is to make sure the cache
  // thing is not accidentally broken
  smt::Term _to_expr(smt::SmtSolver & solver_);
  static smt::Term _to_expr(const cube_t & c, smt::SmtSolver & solver_);

public:
  // the following use cache
  smt::Term to_expr(smt::SmtSolver & btor_solver_);

  // constructors
  Model() : expr_cached_(NULL) {}
  Model(const Model &m) : cube(m.cube), expr_cached_(m.expr_cached_) {}
  // from get value from a solver
  Model(smt::SmtSolver & solver_, const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice);
  Model(smt::SmtSolver & solver_, 
    const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice, // extract using these vars
    const std::unordered_map<smt::Term, smt::Term> & varmap // but use the map in here for the vars
    );
  // return true, if it really exists
  bool erase_var(const smt::Term & v);

protected:
  // cache expr result
  smt::Term expr_cached_;

};

std::ostream & operator<< (std::ostream & os, const Model & m);

}
