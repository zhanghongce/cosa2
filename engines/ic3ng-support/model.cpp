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

  // finally, if no assumptions, remove all inputs
  // for (const auto & eq : conjs) {
  //   smt::Term slice_symb;
  //   smt::Term symb;
  //   if(eq->get_op().prim_op == smt::PrimOp::Equal) {
  //     auto lhs = *(eq->begin());
  //     auto rhs = *(++(eq->begin()));
  //     auto noslice_lhs = (lhs->get_op().prim_op == smt::PrimOp::Extract) ? *(lhs->begin()) : lhs;
  //     auto noslice_rhs = (rhs->get_op().prim_op == smt::PrimOp::Extract) ? *(rhs->begin()) : rhs;
  //     assert(noslice_lhs->is_symbol() || noslice_rhs->is_symbol());
  //     symb = noslice_lhs->is_symbol() ? noslice_lhs : noslice_rhs;
  //     slice_symb = noslice_lhs->is_symbol() ? lhs : rhs;
  //   } else if (eq->get_op().prim_op == smt::PrimOp::Not || eq->get_op().prim_op == smt::PrimOp::BVNot) {
  //     slice_symb = symb = *(eq->begin());
  //     symb = (symb->get_op().prim_op == smt::PrimOp::Extract) ? *(symb->begin()) : symb;
  //     assert(symb->is_symbol());
  //   } else {
  //     assert(eq->is_symbol());
  //     slice_symb = symb = eq;
  //   }
  // }
  // for (const auto & var_val_pair : cube) {
  //   if (var_val_pair.first->is_symbol())
  //     ret += " " + var_val_pair.first->to_string() + "=" + var_val_pair.second->to_string();
  //   else {
  //     auto op = var_val_pair.first->get_op();
  //     assert(op.prim_op == smt::Extract);
  //     auto child = *(var_val_pair.first->begin());
  //     auto left = op.idx0, right = op.idx1;
  //     ret += " " + child->to_string() + "["+ std::to_string(left) + ":"+  std::to_string(right) +"]=" + var_val_pair.second->to_string();
  //   }
  // }

// std::string Model::get_var_canonical_string() const {
//   std::vector<std::string> varnames;
//   for (const auto & var_val_pair : cube) {
//     if (var_val_pair.first->is_symbol())
//       varnames.push_back(var_val_pair.first->to_string());
//     else {
//       auto op = var_val_pair.first->get_op();
//       assert(op.prim_op == smt::Extract);
//       auto child = *(var_val_pair.first->begin());
//       auto left = op.idx0, right = op.idx1;
//       assert(child->is_symbol());
//       varnames.push_back(child->to_string()+"["+ std::to_string(left) + ":"+  std::to_string(right) +"]");
//     }
//   }
//   // sort
//   std::sort(varnames.begin(),varnames.end());
//   std::string ret;
//   for(const auto & n : varnames)
//     ret += n + DELIM;
//   return ret;
// }

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

// void Model::get_varset(std::unordered_set<smt::Term> & varset) const {
//   for (const auto & var_val_pair : cube)
//     varset.emplace(var_val_pair.first);
// }

// void Model::compute_varset_noslice(const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset_slice,
//   std::unordered_set<smt::Term> & varset) 
// {
//   for (const auto & var_bits_pair : varset_slice) {
//     varset.emplace(var_bits_pair.first);
//   }
// } // end of get_varset_noslice


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
