#include "model.h"

#include <algorithm>

#define DELIM "*#<?>#*"

namespace pono {

std::string Model::to_string() const {
 #error todo
}

std::string Model::vars_to_canonical_string() const {
  std::vector<std::string> varnames;
  for(const auto & var_val_pair : cube)
    varnames.push_back(var_val_pair.first->to_string());
  // sort
  std::sort(varnames.begin(),varnames.end());
  std::string ret;
  for(const auto & n : varnames)
    ret += n + DELIM;
  return ret;
}

void Model::get_varset(std::unordered_set<smt::Term> & varset) const {
  for (const auto & var_val_pair : cube)
    varset.emplace(var_val_pair.first);
}


smt::Term Model::to_expr(smt::SmtSolver & btor_solver_) {
  if (expr_cached_ != nullptr)
    return expr_cached_;
  expr_cached_ = _to_expr(btor_solver_);
  return expr_cached_;
}

smt::Term Model::_to_expr(smt::SmtSolver & solver_) {
  smt::Term ret;
  for (const auto & var_val_pair : cube) {
    auto eq = solver_->make_term(smt::Equal, var_val_pair.first, var_val_pair.second);
    if (ret)
      ret = eq;
    else
      ret = solver_->make_term(smt::And, eq, ret);
  } 
  return ret;
}

Model::Model(smt::SmtSolver & solver_, const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice) {
  
}

} // end of namespace pono
