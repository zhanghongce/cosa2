#include "model.h"

#include <algorithm>
#include <cassert>

#define DELIM "*#<?>#*"

namespace pono {

std::string Model::to_string() const {
  std::string ret;
  for (const auto & var_val_pair : cube) {
    if (var_val_pair.first->is_symbol())
      ret += "|" + var_val_pair.first->to_string() + "=" + var_val_pair.first->to_string();
    else {
      auto op = var_val_pair.first->get_op();
      assert(op.prim_op == smt::Extract);
      auto child = *(var_val_pair.first->begin());
      auto left = op.idx0, right = op.idx1;
      ret += "|" + child->to_string() + "["+ std::to_string(left) + ":"+  std::to_string(right) +"]=" + var_val_pair.first->to_string();
    }
  }
  return ret;
}

std::string Model::vars_to_canonical_string() const {
  std::vector<std::string> varnames;
  for (const auto & var_val_pair : cube) {
    if (var_val_pair.first->is_symbol())
      varnames.push_back(var_val_pair.first->to_string());
    else {
      auto op = var_val_pair.first->get_op();
      assert(op.prim_op == smt::Extract);
      auto child = *(var_val_pair.first->begin());
      auto left = op.idx0, right = op.idx1;
      assert(child->is_symbol());
      varnames.push_back(child->to_string()+"["+ std::to_string(left) + ":"+  std::to_string(right) +"]");
    }
  }
  // sort
  std::sort(varnames.begin(),varnames.end());
  std::string ret;
  for(const auto & n : varnames)
    ret += n + DELIM;
  return ret;
}

std::string Model::vars_noslice_to_canonical_string() const {
  std::unordered_set<smt::Term> varset;
  get_varset_noslice(varset);
  std::vector<std::string> varnames;
  for (const auto &v : varset)
    varnames.push_back(v->to_string());
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

void Model::get_varset_noslice(std::unordered_set<smt::Term> & varset) const {
  for (const auto & var_val_pair : cube) {
    if (var_val_pair.first->is_symbol())
      varset.emplace(var_val_pair.first);
    else {
      auto op = var_val_pair.first->get_op();
      assert(op.prim_op == smt::Extract);
      auto child = *(var_val_pair.first->begin());
      varset.emplace(child);
    }
  }
} // end of get_varset_noslice


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
  for (const auto & v_slice : varset_slice) {
    const auto & var = v_slice.first;
    auto val = solver_->get_value(var);
    for(const auto & slice : v_slice.second) {
      auto slice_var = solver_->make_term(smt::Op(smt::Extract,slice.first,slice.second), var);
      auto slice_val = solver_->make_term(smt::Op(smt::Extract,slice.first,slice.second), val);
      cube.emplace(slice_var,slice_val);
    }
  }
} // end of constructor

} // end of namespace pono
