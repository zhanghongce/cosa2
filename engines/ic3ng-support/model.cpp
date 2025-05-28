#include "model.h"

#include <algorithm>
#include <cassert>

#define DELIM "*#<?>#*"

namespace pono {

std::string Model::to_string() const {
  std::string ret;
  for (const auto & eq : conjs) {
    ret += eq->to_string() + " /\\ ";
  }
  return ret;
}


std::string Model::compute_vars_canonical_string(const std::unordered_set<smt::Term> & varset) {
  std::vector<std::string> varnames;
  for (const auto &v : varset)
    varnames.push_back(v->to_string());
  std::sort(varnames.begin(),varnames.end());
  std::string ret;
  for(const auto & n : varnames)
    ret += n + DELIM;
  return ret;
}


smt::Term Model::to_expr(smt::SmtSolver & btor_solver_) {
  if (expr_cached_ != nullptr)
    return expr_cached_;
  expr_cached_ = _to_expr(btor_solver_);
  return expr_cached_;
}

smt::Term Model::_to_expr(smt::SmtSolver & solver_) {
  smt::Term ret;
  assert(!conjs.empty());
  for (const auto & eq : conjs) {
    if (ret)
      ret = solver_->make_term(smt::And, eq, ret);
    else
      ret = eq;
  } 
  return ret;
}

std::ostream & operator<< (std::ostream & os, const Model & m) { return (os << m.to_string()); }

} // end of namespace pono
