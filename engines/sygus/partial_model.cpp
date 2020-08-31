/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief parital eval tree
 **
 ** 
 **/

#include "utils/logger.h"
#include "utils/container_shortcut.h"
#include "utils/str_util.h"
#include "partial_model.h"

#include <cassert>
#include <algorithm> 

namespace cosa {


// ------------------------------- // 
//
//    Model
//
// ------------------------------- // 

std::ostream & operator<< (std::ostream & os, const Model & m) {
  for (auto && v_val : m.cube ) {
    os << "" << v_val.first->to_string() << "= "
              << v_val.second->to_string() << "";
    os << " , ";
  }
  return os;
}


std::string Model::to_string() const {
  std::string ret;
  for (auto && v_val : cube ) {
    ret += v_val.first->to_string()  + "= " +
       v_val.second->to_string() ;
    ret += " , ";
  }
  return ret;
}

std::string Model::vars_to_canonical_string() const {
  std::vector<std::string> vars;
  for (auto && v_val : cube) {
    vars.push_back(v_val.first->to_string());
  }
  std::sort(vars.begin(), vars.end());
  return ::cosa::sygus::Join(vars, "?<*>?"); // hope it won't appear in the the var names
}

void Model::get_varset(std::unordered_set<smt::Term> & varset) const {
  for (auto && v_val : cube) {
    varset.insert(v_val.first);
  }
}

Model::Model(smt::SmtSolver & solver_, const std::unordered_set<smt::Term> & vars) {
  for (smt::Term v : vars) {
    smt::Term val = solver_->get_value(v);
    cube.insert(std::make_pair(v,val));
  }
}

bool Model::erase_var(const smt::Term & v) {
  if (cube.size() == 1)
    return false; // will not erase it in this case

  size_t erased = cube.erase(v);
  if (erased == 1) {
    expr_btor_ = NULL;
    expr_msat_ = NULL;
  }
  return erased == 1;
}

#define NOT(x)    (solver_->make_term(smt::Not, (x)))
#define EQ(x, y)  (solver_->make_term(smt::Equal, (x), (y)))
#define AND(x, y) (solver_->make_term(smt::And, (x), (y)))
#define OR(x, y)  (solver_->make_term(smt::Or, (x), (y)))

smt::Term Model::to_expr(const cube_t & c, smt::SmtSolver & solver_) {
  smt::Term ret = nullptr;
  for (auto && v_val : c ) {
    if (ret == nullptr)
      ret = EQ(v_val.first, v_val.second);
    else
      ret = AND(ret, EQ(v_val.first, v_val.second));
  }
  return ret;
}


smt::Term Model::bool_to_bv(const smt::Term & t, smt::SmtSolver & solver_)
{
  if (t->get_sort()->get_sort_kind() == smt::BOOL) {
    smt::Sort bv1sort = solver_->make_sort(smt::BV, 1);
    return solver_->make_term(
        smt::Ite, t, solver_->make_term(1, bv1sort), solver_->make_term(0, bv1sort));
  } else {
    return t;
  }
}

smt::Term Model::bv_to_bool(const smt::Term & t, smt::SmtSolver & solver_)
{
  smt::Sort sort = t->get_sort();
  if (sort->get_sort_kind() == smt::BV) {
    if (sort->get_width() != 1) {
      throw CosaException("Can't convert non-width 1 bitvector to bool.");
    }
    return solver_->make_term(
        smt::Equal, t, solver_->make_term(1, solver_->make_sort(smt::BV, 1)));
  } else {
    return t;
  }
}

smt::Term Model::to_expr_translate(
    const cube_t & c, smt::SmtSolver & solver_,
    smt::TermTranslator & to_msat) {

  smt::Term ret = nullptr;
  for (auto && v_val : c ) {
    auto var_msat = to_msat.transfer_term(v_val.first, false);
    auto val_msat = to_msat.transfer_term(v_val.second, false);
    if ( var_msat->get_sort()->get_sort_kind() != 
         val_msat->get_sort()->get_sort_kind()) {
      if (var_msat->get_sort()->get_sort_kind() == smt::BV) {
        assert(var_msat->get_sort()->get_width() == 1);
        assert(val_msat->get_sort()->get_sort_kind() == smt::BOOL);
        val_msat = bool_to_bv(val_msat, solver_);
      } else if ( var_msat->get_sort()->get_sort_kind() == smt::BOOL ) {
        assert(val_msat->get_sort()->get_sort_kind() == smt::BV);
        assert(val_msat->get_sort()->get_width() == 1);
        val_msat = bv_to_bool(val_msat, solver_);
      } else
        assert(false); // we cannot handle this case
    }

    if (ret == nullptr)
      ret = EQ(var_msat, val_msat);
    else
      ret = AND(ret, EQ(var_msat, val_msat));
  }
  return ret;
}

smt::Term Model::to_expr(smt::SmtSolver & solver_) {
  return to_expr(this->cube, solver_);
}

smt::Term Model::to_expr_btor(smt::SmtSolver & btor_solver_) {
  if ( expr_btor_ == nullptr )
    expr_btor_ = to_expr(btor_solver_);
  return expr_btor_;
}

smt::Term Model::to_expr_msat(smt::SmtSolver & msat_solver_, smt::TermTranslator & to_msat ) {
  if (expr_msat_ == nullptr)
    expr_msat_ = to_expr_translate(this->cube, msat_solver_, to_msat);
  return expr_msat_;
}


// ------------------------------- // 
//
//    PartialModelGen
//
// ------------------------------- // 

PartialModelGen::PartialModelGen(smt::SmtSolver & solver):
  solver_(solver) {
  // do nothing
}

PartialModelGen::~PartialModelGen() {
  for (auto ptr : node_allocation_table_) {
    assert (ptr);
    delete (ptr);
  }
}

void PartialModelGen::GetPartialModel(const smt::Term & ast, cube_t & m, bool use_cache) {
  GetVarList(ast, use_cache);

  for (smt::Term v : dfs_vars_) {
    smt::Term val = solver_->get_value(v);
    m.insert(std::make_pair(v,val));
  }
}


void PartialModelGen::GetVarList(const smt::Term & ast, bool use_cache ) {
  dfs_walked_.clear();
  dfs_vars_.clear();
  use_cache_ = use_cache;
  dfs_walk(ast);
}


void PartialModelGen::GetVarList(const smt::Term & ast, 
  std::unordered_set<smt::Term> & out_vars, bool use_cache ) {

  dfs_walked_.clear();
  dfs_vars_.clear();
  use_cache_ = use_cache;
  dfs_walk(ast);
  out_vars.insert(dfs_vars_.begin(), dfs_vars_.end());
}


void PartialModelGen::GetVarListForAsts(const smt::TermVec & asts, 
  smt::UnorderedTermSet & out_vars, bool use_cache ) {
  dfs_walked_.clear();
  dfs_vars_.clear();
  use_cache_ = use_cache;
  for (const auto & ast : asts)
    dfs_walk(ast);
  out_vars.insert(dfs_vars_.begin(), dfs_vars_.end());
}

static inline bool is_all_zero(const std::string & s)  {
  assert(s.substr(0, 2) == "#b");
  for (auto pos = s.begin()+2; pos != s.end(); ++ pos)
    if (*pos != '0')
      return false;
  return true;
}

static inline bool is_all_one(const std::string & s, uint64_t w)  {
  assert(s.substr(0, 2) == "#b");
  assert (s.length() - 2 <= w);
  if (s.length() - 2 < w) // if it has fewer zeros
    return false;
  for (auto pos = s.begin()+2; pos != s.end(); ++ pos)
    if (*pos != '1')
      return false;
  return true;  
}


#define ARG2(a1,a2)            \
      auto ptr = ast->begin();    \
      auto a1  = *(ptr++);      \
      auto a2  = *(ptr++);      \
      assert (ptr == ast->end()); 

#define ARG3(a1,a2,a3)            \
      auto ptr = ast->begin();    \
      auto a1  = *(ptr++);      \
      auto a2  = *(ptr++);      \
      auto a3  = *(ptr++);      \
      assert (ptr == ast->end());

void PartialModelGen::dfs_walk(const smt::Term & ast ) {
  // std::cout << "[DEBUG] expr : " << ast->to_string() << std::endl;
  if (IN(ast, dfs_walked_)) {
    // std::cout << "[DEBUG] cached." << std::endl;
    return;
  }
  dfs_walked_.insert(ast);

  if (use_cache_) {
    CondVarBuffer * buf = CheckCache(ast);
    if (buf)
      InterpretCache(buf, dfs_vars_);
  }

  smt::Op op = ast->get_op();
  if (op.is_null()) { // this is the root node
    if (ast->is_symbolic_const()) {
      dfs_vars_.insert(ast);
    }
  } else {
    if (op.prim_op == smt::PrimOp::Ite)  {
      ARG3(cond, texpr, fexpr)
      auto cond_val = solver_->get_value(cond);
      assert(cond_val->is_value());
      if (cond_val->to_int()) {
        dfs_walk(cond);
        dfs_walk(texpr);
      }
      else {
        dfs_walk(cond);
        dfs_walk(fexpr);
      }
    } else if (op.prim_op == smt::PrimOp::Implies) {
      ARG2(left,right)
      auto cond_left = solver_->get_value(left);
      auto cond_right = solver_->get_value(right);
      assert(cond_left->is_value() && cond_right->is_value());
      if (!(cond_left->to_int())) // if it is false
        dfs_walk(left);
      else if (cond_right->to_int()) {
        dfs_walk(right);
      } else {
        dfs_walk(left);
        dfs_walk(right);        
      }
    } else if (op.prim_op == smt::PrimOp::And) {
      ARG2(left,right)
      auto cond_left = solver_->get_value(left);
      auto cond_right = solver_->get_value(right);
      assert(cond_left->is_value() && cond_right->is_value());
      if (!(cond_left->to_int())) // if it is false
        dfs_walk(left);
      else if (!(cond_right->to_int())) {
        dfs_walk(right);
      } else {
        dfs_walk(left);
        dfs_walk(right);
      }
    } else if (op.prim_op == smt::PrimOp::Or) {
      ARG2(left,right)
      auto cond_left = solver_->get_value(left);
      auto cond_right = solver_->get_value(right);
      assert(cond_left->is_value() && cond_right->is_value());
      if (cond_left->to_int()) // if it is true
        dfs_walk(left);
      else if (cond_right->to_int()) {
        dfs_walk(right);
      } else  { // it is 0, so both matter
        dfs_walk(left);
        dfs_walk(right);
      }
    } else if (op.prim_op == smt::PrimOp::BVAnd || op.prim_op == smt::PrimOp::BVNand) {
      ARG2(left,right)
      auto cond_left = solver_->get_value(left);
      auto cond_right = solver_->get_value(right);
      assert(cond_left->is_value() && cond_right->is_value());
      std::string left_val = cond_left->to_string();
      std::string right_val = cond_right->to_string();

      if (is_all_zero(left_val)) // if all zeros
        dfs_walk(left);
      else if (is_all_zero(right_val)) {
        dfs_walk(right);
      } else { // it is 0, so both matter
        dfs_walk(left);
        dfs_walk(right);
      }

    } else if (op.prim_op == smt::PrimOp::BVOr  || op.prim_op == smt::PrimOp::BVNor) {
      ARG2(left,right)
      auto cond_left = solver_->get_value(left);
      auto cond_right = solver_->get_value(right);
      assert(cond_left->is_value() && cond_right->is_value());
      std::string left_val = cond_left->to_string();
      std::string right_val = cond_right->to_string();

      if (is_all_one(left_val, left->get_sort()->get_width())) // if all ones
        dfs_walk(left);
      else if (is_all_one(right_val, right->get_sort()->get_width())) {
        dfs_walk(right);
      } else { // it is 0, so both matter
        dfs_walk(left);
        dfs_walk(right);
      }
    } else if (op.prim_op == smt::PrimOp::BVMul) {
      ARG2(left,right)
      auto cond_left = solver_->get_value(left);
      auto cond_right = solver_->get_value(right);
      assert(cond_left->is_value() && cond_right->is_value());
      std::string left_val = cond_left->to_string();
      std::string right_val = cond_right->to_string();

      if (is_all_zero(left_val)) // if all ones
        dfs_walk(left);
      else if (is_all_zero(right_val)) {
        dfs_walk(right);
      } else { // it is not 0, so both matter
        dfs_walk(left);
        dfs_walk(right);
      }
    }
    else {
      for (const auto & arg : *ast)
        dfs_walk(arg);
    }
  } // end non-variable case
} // end of PartialModelGen::dfs_walk

void PartialModelGen::CacheNode(const smt::Term & ast) {
  // another dfs, go to each leaf (even it has been walked?)
  if (IN(ast, node_buffer_))
    return;
  cur_node_ = new CondVarBuffer;
  node_allocation_table_.push_back(cur_node_);

  dfs_variable_stack_.clear();
  dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
  dfs_bufwalk(ast, nullptr);
  assert(dfs_variable_stack_.size() == 1);
  cur_node_->vars.insert(
    dfs_variable_stack_.back().begin(),
    dfs_variable_stack_.back().end());
  
  node_buffer_.insert(std::make_pair(ast, cur_node_));
}

void PartialModelGen::InterpretCache(CondVarBuffer * n, std::unordered_set<smt::Term> & var)  {
  for(auto & v : n->vars)
    var.insert(v);
  auto pos = n->condition_map.begin();
  for (auto & cond_vars_pair : n->condition_map) {
    auto cond = solver_->get_value(cond_vars_pair.first)->to_int();
    if (cond) {
      for (auto && v : cond_vars_pair.second)
        var.insert(v);
    }
  }
} // InterpretCache

CondVarBuffer * PartialModelGen::CheckCache(const smt::Term & ast) const {
  auto pos = node_buffer_.find(ast);
  if (pos == node_buffer_.end())
    return NULL;
  return pos->second;
}

void PartialModelGen::cur_node_insert_back(const smt::Term & cond) {
  assert(cur_node_); // not NULL
  assert(cond != nullptr);
  cur_node_->condition_map[cond].insert(
    dfs_variable_stack_.back().begin(),
    dfs_variable_stack_.back().end());
}

bool PartialModelGen::not_in_parent_vars(const smt::Term & var) {
  for (auto && vs : dfs_variable_stack_) {
    if (IN(var, vs))
      return false;
  }
  return true;
}

#define ANDx(x, y) (((x) == nullptr )? (y) : (solver_->make_term(smt::And, (x), (y))))

void PartialModelGen::dfs_bufwalk(const smt::Term & ast, const smt::Term & cond_so_far) {

  smt::Op op = ast->get_op();
  if (op.is_null()) { // this is the root node
    if (ast->is_symbolic_const()) {
      // TODO: check parent stacks
      if (not_in_parent_vars(ast))
        dfs_variable_stack_.back().insert(ast);
    }
  } else {
    if (op.prim_op == smt::PrimOp::Ite)  {
      ARG3(cond, texpr, fexpr)
      dfs_bufwalk(cond, cond_so_far);

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto l_cond = ANDx(cond_so_far, cond);
      dfs_bufwalk(texpr, l_cond);
      cur_node_insert_back(l_cond);
      dfs_variable_stack_.pop_back();

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto r_cond = ANDx(cond_so_far, NOT(cond));
      dfs_bufwalk(fexpr, r_cond);
      cur_node_insert_back(r_cond);
      dfs_variable_stack_.pop_back();

    } else if (op.prim_op == smt::PrimOp::Implies) {
      ARG2(left,right)

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto l_cond = ANDx(cond_so_far, OR(NOT(left),NOT(right)) );
      dfs_bufwalk(left, l_cond);
      cur_node_insert_back(l_cond);
      dfs_variable_stack_.pop_back();

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto r_cond = ANDx(cond_so_far, left);
      dfs_bufwalk(right, r_cond);
      cur_node_insert_back(r_cond);
      dfs_variable_stack_.pop_back();

    } else if (op.prim_op == smt::PrimOp::And) {
      ARG2(left,right)

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto l_cond = ANDx(cond_so_far, OR(NOT(left),(right)) );
      dfs_bufwalk(left, l_cond);
      cur_node_insert_back(l_cond);
      dfs_variable_stack_.pop_back();

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto r_cond = ANDx(cond_so_far, left);
      dfs_bufwalk(right, r_cond);
      cur_node_insert_back(r_cond);
      dfs_variable_stack_.pop_back();

    } else if (op.prim_op == smt::PrimOp::Or) {
      ARG2(left,right)

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto l_cond = ANDx(cond_so_far, OR((left),NOT(right)) );
      dfs_bufwalk(left, l_cond);
      cur_node_insert_back(l_cond);
      dfs_variable_stack_.pop_back();
      
      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto r_cond = ANDx(cond_so_far, NOT(left));
      dfs_bufwalk(right, r_cond);
      cur_node_insert_back(r_cond);
      dfs_variable_stack_.pop_back();

    } else if (op.prim_op == smt::PrimOp::BVAnd || op.prim_op == smt::PrimOp::BVNand) {
      ARG2(left,right)

      auto zero = solver_->make_term(0, ast->get_sort() );

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto l_cond = ANDx(cond_so_far, OR(EQ(left, zero), NOT(EQ(right, zero))) );
      dfs_bufwalk(left, l_cond);
      cur_node_insert_back(l_cond);
      dfs_variable_stack_.pop_back();
      
      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto r_cond = ANDx(cond_so_far, NOT(EQ(left, zero)) );
      dfs_bufwalk(right, r_cond);
      cur_node_insert_back(r_cond);
      dfs_variable_stack_.pop_back();

    } else if (op.prim_op == smt::PrimOp::BVOr  || op.prim_op == smt::PrimOp::BVNor) {
      ARG2(left,right)
      
      std::string binary_all_one;
      for (uint64_t idx = 0; idx < ast->get_sort()->get_width(); ++ idx)
        binary_all_one += "1";
      auto allone = solver_->make_term(binary_all_one, ast->get_sort(), 2 );

      dfs_variable_stack_.push_back(std::unordered_set<smt::Term>());
      auto l_cond = ANDx(cond_so_far, OR(EQ(left, allone), NOT(EQ(right, allone))) );
      dfs_bufwalk(left, l_cond);
      cur_node_insert_back(l_cond);
      dfs_variable_stack_.pop_back();

      auto r_cond = ANDx(cond_so_far, NOT(EQ(left, allone)) );
      dfs_bufwalk(right, r_cond);
      cur_node_insert_back(r_cond);
      dfs_variable_stack_.pop_back();

    } else {
      for (const auto & arg : *ast)
        dfs_bufwalk(arg, cond_so_far);
    }
  } // end non-variables
} // dfs_bufwalk



} // namespace cosa