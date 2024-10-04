#include "model.h"

#include <algorithm>
#include <cassert>

#define DELIM "*#<?>#*"

namespace pono {

std::string Model::to_string() const {
  std::string ret;
  for (const auto & var_val_pair : cube) {
    if (var_val_pair.first->is_symbol())
      ret += " " + var_val_pair.first->to_string() + "=" + var_val_pair.second->to_string();
    else {
      auto op = var_val_pair.first->get_op();
      assert(op.prim_op == smt::Extract);
      auto child = *(var_val_pair.first->begin());
      auto left = op.idx0, right = op.idx1;
      ret += " " + child->to_string() + "["+ std::to_string(left) + ":"+  std::to_string(right) +"]=" + var_val_pair.second->to_string();
    }
  }
  return ret;
}

std::string Model::get_var_canonical_string() const {
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

std::string Model::compute_vars_noslice_canonical_string(const std::unordered_set<smt::Term> & varset) {
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

void Model::compute_varset_noslice(const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice,
  std::unordered_set<smt::Term> & varset) 
{
  for (const auto & var_bits_pair : varset_slice) {
    varset.emplace(var_bits_pair.first);
  }
} // end of get_varset_noslice


void Model::to_expr_conj(smt::SmtSolver & btor_solver_, smt::TermVec & out) const {
  for (const auto & var_val_pair : cube) {
    auto eq = btor_solver_->make_term(smt::Equal, var_val_pair.first, var_val_pair.second);
    out.push_back(eq);
  }
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
      ret = solver_->make_term(smt::And, eq, ret);
    else
      ret = eq;
  } 
  return ret;
}

Model::Model(smt::SmtSolver & solver_,
  const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice, 
  PerVarInfo * var_info_ptr) : var_info_(var_info_ptr)
{
  for (const auto & v_slice : varset_slice) {
    const auto & var = v_slice.first;
    auto val = solver_->get_value(var);
    for(const auto & slice : v_slice.second) {
      assert(slice.first>=slice.second);
      for (unsigned idx = slice.second; idx <= slice.first; ++ idx) {
        auto slice_var = solver_->make_term(smt::Op(smt::Extract,idx,idx), var);
        auto slice_val = solver_->make_term(smt::Op(smt::Extract,idx,idx), val);
        cube.emplace(slice_var,slice_val);
      }
    }
  }
} // end of constructor


std::ostream & operator<< (std::ostream & os, const Model & m) { return (os << m.to_string()); }

} // end of namespace pono
