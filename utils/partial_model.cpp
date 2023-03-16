/*********************                                                  */
/*! \file partial_model.cpp
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class for performing dynamic cone of influence reduction based
**        on the model from the solver. This is essentially extracting a
**        partial model.
**
**/

#include "utils/partial_model.h"
#include "utils/str_util.h"
#include "smt-switch/boolector_factory.h"
#include "engines/prover.h"
#include "smt/available_solvers.h"
#include "assert.h"

namespace pono {

IC3Formula PartialModelGen::GetPartialModel(const smt::Term & ast) {
  GetVarList(ast);

  smt::Term conj;
  smt::TermVec conjvec;
  for (smt::Term v : dfs_vars_) {
    smt::Term val = solver_->get_value(v);
    auto eq = solver_->make_term(smt::Op(smt::PrimOp::Equal), v,val );
    conjvec.push_back( eq );
    if (conj) {
      conj = solver_->make_term(smt::Op(smt::PrimOp::And), conj, eq);
    } else {
      conj = eq;
    }
  }
  return IC3Formula(conj, conjvec, false /*not a disjunction*/ );
} // GetPartialModel to ic3formula


std::pair<IC3Formula,syntax_analysis::IC3FormulaModel> 
    PartialModelGen::GetPartialModelInCube(const smt::Term & ast) {
  
  GetVarList(ast);

  std::unordered_map<smt::Term, smt::Term> cube;

  smt::Term conj;
  smt::TermVec conjvec;
  for (smt::Term v : dfs_vars_) {
    smt::Term val = solver_->get_value(v);
    cube.emplace(v,val);
    auto eq = solver_->make_term(smt::Op(smt::PrimOp::Equal), v,val );
    conjvec.push_back( eq );
    if (conj) {
      conj = solver_->make_term(smt::Op(smt::PrimOp::And), conj, eq);
    } else {
      conj = eq;
    }
  }

  return std::make_pair(IC3Formula(conj, conjvec,
      false /*not a disjunction*/ ), 
    syntax_analysis::IC3FormulaModel(std::move(cube), conj));
}

void PartialModelGen::GetVarList(const smt::Term & ast ) {
  dfs_walked_.clear();
  dfs_vars_.clear();
  dfs_walk(ast);
}


void PartialModelGen::GetVarList(const smt::Term & ast, 
  std::unordered_set<smt::Term> & out_vars ) {

  dfs_walked_.clear();
  dfs_vars_.clear();
  dfs_walk(ast);
  out_vars.insert(dfs_vars_.begin(), dfs_vars_.end());
}

void PartialModelGen::GetVarList_coi(const smt::Term & ast, 
  std::unordered_set<smt::Term> & out_vars,std::vector <std::pair<smt::Term,std::pair<int,int>>> & varset_slice) {

  dfs_walked_.clear();
  dfs_vars_.clear();
  term_leaf_map.clear();
  std::vector <std::pair<smt::Term,std::vector<std::pair<int,int>>>> varset_slice_walk;
  dfs_walk_deep(ast,varset_slice_walk);
  for(const auto walk_slice:varset_slice_walk){
    for(const auto pair: walk_slice.second){
      varset_slice.push_back(std::make_pair(walk_slice.first,pair));
    }
  }
  out_vars.insert(dfs_vars_.begin(), dfs_vars_.end());
}


void PartialModelGen::GetVarListForAsts(const smt::TermVec & asts, 
  smt::UnorderedTermSet & out_vars ) {
  dfs_walked_.clear();
  dfs_vars_.clear();
  for (const auto & ast : asts)
    dfs_walk(ast);
  out_vars.insert(dfs_vars_.begin(), dfs_vars_.end());
}


/* Internal Function */
bool static extract_decimal_width(const std::string & s,
  std::string & decimal, std::string & width)
{
  if(s.substr(0,5) != "(_ bv")
    return false;
  auto space_idx = s.find(' ', 5);
  if(space_idx == std::string::npos )
    return false;
  auto rpara_idx = s.find(')', space_idx);
  if(rpara_idx == std::string::npos )
    return false;

  decimal = s.substr(5,space_idx-5);
  width = s.substr(space_idx+1,rpara_idx-(space_idx+1));
  assert(!width.empty());
  return true;
}


static std::string get_all_one(unsigned width) {
  std::vector<char> out = {1};

  for (unsigned idx = 1; idx < width; ++idx) {
    syntax_analysis::mul2(out);
    syntax_analysis::add1(out);
  }

  std::string ret;
  for (auto pos = out.rbegin(); pos != out.rend(); ++pos) {
    ret += *pos + '0';
  }
  return ret;
}

bool static convert_to_boolean_and_check(
  const std::string & decimal, const std::string & width, bool _0or1) {

  static std::unordered_map<unsigned, std::string> width2fullones;

  if (!_0or1) {
    for (auto c : decimal)
      if (c != '0')
        return false;
    return true;
  } // if 0, requires 0,00,000

  auto width_i = syntax_analysis::StrToULongLong(width,10);
  assert(width_i != 0);
  auto fullone_pos = width2fullones.find(width_i);
  if (fullone_pos == width2fullones.end()) {
    fullone_pos = width2fullones.emplace( width_i , get_all_one(width_i) ).first;
  }
  return decimal == fullone_pos->second;
}

/* Internal Function */
static inline bool is_all_zero(const std::string & s)  {
  if (s == "true")
    return false;
  if (s == "false")
    return true;
  assert (s.length() > 2);
  if (s.substr(0,2) == "#b") {
    for (auto pos = s.begin()+2; pos != s.end(); ++ pos)
      if (*pos != '0')
        return false;
    return true;
  } // else
  std::string decimal, width;
  bool conv_succ = extract_decimal_width(s, decimal, width);
  assert(conv_succ);

  return convert_to_boolean_and_check(decimal, width, false);
}

static inline void push_extracted_bit(std::vector<std::pair<int,int>> & extracted_bit,int site){

  if(!extracted_bit.empty()){
    auto pair = extracted_bit.back();
    if(pair.first==site-1){
      extracted_bit.pop_back();
      extracted_bit.push_back(std::make_pair(site,pair.second));
    }
    else{
      extracted_bit.push_back(std::make_pair(site,site));
    }
  }
  else{
    extracted_bit.push_back(std::make_pair(site,site));
  }    
}


static inline void detect_partial_zero(const std::string & left,const std::string & right,const std::vector<std::pair<int,int>> & extracted_bit,std::vector<std::pair<int,int>> & extracted_bit_left, std::vector<std::pair<int,int>>  & extracted_bit_right){
  assert ((left.length() > 2)&&(right.length() > 2));
  if (left.substr(0,2) == "#b") {
    for(const auto extract:extracted_bit){
      auto left_bound = extract.first;
      auto right_bound = extract.second;
      auto site = right_bound;
      for (auto pos = left.rbegin()+right_bound; pos != left.rbegin()+left_bound+1; ++ pos){
        if (*pos == '0'){
          push_extracted_bit(extracted_bit_left,site);
        }
        else if(right.substr(site,site+1) =="0"){
          push_extracted_bit(extracted_bit_right,site);
        }
        else{
          push_extracted_bit(extracted_bit_left,site);
          push_extracted_bit(extracted_bit_right,site);
        }
        site = site + 1;
      }
    }
  }
}

static inline void detect_partial_one(const std::string & left,const std::string & right,const std::vector<std::pair<int,int>> & extracted_bit,std::vector<std::pair<int,int>> & extracted_bit_left, std::vector<std::pair<int,int>>  & extracted_bit_right){
  assert ((left.length() > 2)&&(right.length() > 2));
  if (left.substr(0,2) == "#b") {
    for(const auto extract:extracted_bit){
      auto left_bound = extract.first;
      auto right_bound = extract.second;
      auto site = right_bound;
      for (auto pos = left.rbegin()+right_bound; pos != left.rbegin()+left_bound+1; ++ pos){
        if (*pos == '1'){
          push_extracted_bit(extracted_bit_left,site);
        }
        else if(right.substr(site,site+1) =="1"){
          push_extracted_bit(extracted_bit_right,site);
        }
        else{
          push_extracted_bit(extracted_bit_left,site);
          push_extracted_bit(extracted_bit_right,site);
        }
        site = site + 1;
      }
    }
  }
}



/* Internal Function */
static inline bool is_all_one(const std::string & s, uint64_t w)  {
  if (s == "true")
    return true;
  if (s == "false")
    return false;

  assert (s.length() > 2);
  if (s.substr(0,2) == "#b") {
    assert (s.length() - 2 <= w);
    if (s.length() - 2 < w) // if it has fewer zeros
      return false;
    for (auto pos = s.begin()+2; pos != s.end(); ++ pos)
      if (*pos != '1')
        return false;
    return true;  
  }
  std::string decimal, width;
  bool conv_succ = extract_decimal_width(s, decimal, width);
  assert(conv_succ);

  return convert_to_boolean_and_check(decimal, width, true);
}

/* Internal Macros */

#define ARG1(a1)            \
      auto ptr = ast->begin();    \
      auto a1  = *(ptr++);      \
      assert (ptr == ast->end()); 

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


void PartialModelGen::dfs_walk(const smt::Term & input_ast) {
  smt::TermVec node_stack_;
  node_stack_.push_back(input_ast);
  while(!node_stack_.empty()) {
    const auto & ast = node_stack_.back();
    if (dfs_walked_.find(ast) != dfs_walked_.end()) {
      node_stack_.pop_back();
      continue;
    }
    dfs_walked_.insert(ast);

    smt::Op op = ast->get_op();
    if (op.is_null()) { // this is the root node
      if (ast->is_symbolic_const()) {
        dfs_vars_.insert(ast);
      }
      node_stack_.pop_back(); // no need to wait for the next time
      continue;
    } else { // non variable/non constant case
      if (op.prim_op == smt::PrimOp::Ite)  {
        ARG3(cond, texpr, fexpr)
        auto cond_val = solver_->get_value(cond);
        assert(cond_val->is_value());
        if ( is_all_one(cond_val->to_string(),1) ) {
          node_stack_.push_back(cond);
          node_stack_.push_back(texpr);
        }
        else {
          node_stack_.push_back(cond);
          node_stack_.push_back(fexpr);
        }
      } else if (op.prim_op == smt::PrimOp::Implies) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        if (!( is_all_one(cond_left->to_string(),1) )) // if it is false
          node_stack_.push_back(left);
        else if ( is_all_one(cond_right->to_string(), 1) ) {
          node_stack_.push_back(right);
        } else {
          node_stack_.push_back(left);
          node_stack_.push_back(right);
        }
      } else if (op.prim_op == smt::PrimOp::And) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        if (!( is_all_one(cond_left->to_string(),1) )) // if it is false
          node_stack_.push_back(left);
        else if (!(is_all_one(cond_right->to_string(), 1))) {
          node_stack_.push_back(right);
        } else {
          node_stack_.push_back(left);
          node_stack_.push_back(right);
        }
      } else if (op.prim_op == smt::PrimOp::Or) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        if (is_all_one(cond_left->to_string(),1)) // if it is true
          node_stack_.push_back(left);
        else if (is_all_one(cond_right->to_string(), 1)) {
          node_stack_.push_back(right);
        } else  { // it is 0, so both matter
          node_stack_.push_back(left);
          node_stack_.push_back(right);
        }
      } else if (op.prim_op == smt::PrimOp::BVAnd || op.prim_op == smt::PrimOp::BVNand) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        std::string left_val = cond_left->to_string();
        std::string right_val = cond_right->to_string();

        if (is_all_zero(left_val)) // if all zeros
          node_stack_.push_back(left);
        else if (is_all_zero(right_val)) {
          node_stack_.push_back(right);
        } else { // it is 0, so both matter
          node_stack_.push_back(left);
          node_stack_.push_back(right);
        }

      } else if (op.prim_op == smt::PrimOp::BVOr  || op.prim_op == smt::PrimOp::BVNor) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        std::string left_val = cond_left->to_string();
        std::string right_val = cond_right->to_string();

        if (is_all_one(left_val, left->get_sort()->get_width())) // if all ones
          node_stack_.push_back(left);
        else if (is_all_one(right_val, right->get_sort()->get_width())) {
          node_stack_.push_back(right);
        } else { // it is 0, so both matter
          node_stack_.push_back(left);
          node_stack_.push_back(right);
        }
      } else if (op.prim_op == smt::PrimOp::BVMul) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        std::string left_val = cond_left->to_string();
        std::string right_val = cond_right->to_string();

        if (is_all_zero(left_val)) // if all zeros
          node_stack_.push_back(left);
        else if (is_all_zero(right_val)) {
          node_stack_.push_back(right);
        } else { // it is not 0, so both matter
          node_stack_.push_back(left);
          node_stack_.push_back(right);
        }
      }
      else {
        for (const auto & arg : *ast)
          node_stack_.push_back(arg);
      }
    } // end non-variable case
  } // while ( not empty )
} // end of PartialModelGen::dfs_walk


void PartialModelGen::dfs_walk_deep(const smt::Term & input_ast,std::vector <std::pair<smt::Term,std::vector<std::pair<int,int>>>> & varset_slice) {
  std::vector <std::pair<smt::Term,std::vector<std::pair<int,int>>>> node_stack_;
  std::vector <bool> using_extract_track;
  
  auto btorsolver = create_solver(smt::BTOR);
  auto transferer = smt::TermTranslator(btorsolver);
  std::vector<std::pair<int,int>> node_pairs;
  bool using_extracted = false;
  bool same_parent;
  auto sort = input_ast->get_sort();
  if(sort->to_string()=="Bool"){
    node_pairs.push_back(std::make_pair(0,0));
    node_stack_.push_back(std::make_pair(input_ast,node_pairs));
    using_extract_track.push_back(using_extracted);
  }
  else{
    auto width = sort->get_width();
    node_pairs.push_back(std::make_pair(width-1,0));
    node_stack_.push_back(std::make_pair(input_ast,node_pairs));
    using_extract_track.push_back(using_extracted);
  }
  while(!node_stack_.empty()) {
    const auto & ast = node_stack_.back().first;
    const auto ast_copy = node_stack_.back().first;
    const auto extracted_bit =  node_stack_.back().second;
    using_extracted = using_extract_track.back();
    if ((dfs_walked_.find(ast) != dfs_walked_.end())&&(ast->is_symbolic_const()==false)) {//TODO: need to add another constraints, that is ast->is_symbolic_const()
      node_stack_.pop_back();
      using_extract_track.pop_back();
      continue;
    }
    dfs_walked_.insert(ast);

    smt::Op op = ast->get_op();
    if (op.is_null()) { // this is the root node
      if (ast->is_symbolic_const()) {
        auto ast_recoder = node_stack_.back();
        varset_slice.push_back(ast_recoder);
        dfs_vars_.insert(ast);
      }
      // using_extracted = false;
      node_stack_.pop_back(); // no need to wait for the next time
      using_extract_track.pop_back();
      continue;
    } else { // non variable/non constant case
      if (op.prim_op == smt::PrimOp::Ite)  {
        ARG3(cond, texpr, fexpr)
        auto cond_val = solver_->get_value(cond);
        assert(cond_val->is_value());
        // using_extracted = true;
        if ( is_all_one(cond_val->to_string(),1) ) {
          ///For the condition, we never use the extracted terms.
          push_to_node_stack(cond,ast_copy,extracted_bit,node_stack_,false,using_extract_track);
          push_to_node_stack(texpr,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        }
        else {
          push_to_node_stack(cond,ast_copy,extracted_bit,node_stack_,false,using_extract_track);
          push_to_node_stack(fexpr,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        }
      } else if (op.prim_op == smt::PrimOp::Implies) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        assert(ast->get_sort()->get_width()==1);
        using_extracted = false;
        if (!( is_all_one(cond_left->to_string(),1) )) {          
          push_to_node_stack(left,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        }
        else if ( is_all_one(cond_right->to_string(), 1) ) {
          push_to_node_stack(right,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        } else {
          push_to_node_stack(left,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track); 
          push_to_node_stack(right,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);        
        }
      } else if (op.prim_op == smt::PrimOp::And) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        assert(ast->get_sort()->get_width()==1);
        using_extracted = false;
        if (!( is_all_one(cond_left->to_string(),1) )) {
          push_to_node_stack(left,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track); 
          }
        else if (!(is_all_one(cond_right->to_string(), 1))) {
          push_to_node_stack(right,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track); 
        } else {
          push_to_node_stack(left,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
          push_to_node_stack(right,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        }
      } else if (op.prim_op == smt::PrimOp::Or) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        assert(ast->get_sort()->get_width()==1);
        using_extracted = false;
        if (is_all_one(cond_left->to_string(),1)) {
          push_to_node_stack(left,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        }
        else if (is_all_one(cond_right->to_string(), 1)) {
          push_to_node_stack(right,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        } else  { // it is 0, so both matter
          push_to_node_stack(left,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
          push_to_node_stack(right,ast_copy,extracted_bit,node_stack_,using_extracted,using_extract_track);
        }
      } else if (op.prim_op == smt::PrimOp::BVAnd || op.prim_op == smt::PrimOp::BVNand) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        cond_left = transferer.transfer_term(cond_left);
        cond_right = transferer.transfer_term(cond_right);
        std::string left_val = cond_left->to_string();
        std::string right_val = cond_right->to_string();
        using_extracted = true;
        if (is_all_zero(left_val)) // if all zeros
          push_to_node_stack(left,ast_copy,extracted_bit, node_stack_,using_extracted,using_extract_track);
          // node_stack_.push_back(make_pair(left,extracted_bit));
        else if (is_all_zero(right_val)) {
          push_to_node_stack(right,ast_copy,extracted_bit, node_stack_,using_extracted,using_extract_track);
        } 
        else { // it is 0, so both matter
          std::vector<std::pair<int,int>> extracted_bit_left;
          std::vector<std::pair<int,int>> extracted_bit_right;
          detect_partial_zero(left_val,right_val,extracted_bit,extracted_bit_left,extracted_bit_right);
          push_to_node_stack(left,ast_copy,extracted_bit_left, node_stack_,using_extracted,using_extract_track);
          push_to_node_stack(right,ast_copy,extracted_bit_right, node_stack_,using_extracted,using_extract_track);
        }
      } else if (op.prim_op == smt::PrimOp::BVOr  || op.prim_op == smt::PrimOp::BVNor) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        cond_left = transferer.transfer_term(cond_left);
        cond_right = transferer.transfer_term(cond_right);
        std::string left_val = cond_left->to_string();
        std::string right_val = cond_right->to_string();
        using_extracted = true;
        if (is_all_one(left_val, left->get_sort()->get_width())) // if all ones
          push_to_node_stack(left,ast_copy,extracted_bit, node_stack_,using_extracted,using_extract_track);
        else if (is_all_one(right_val, right->get_sort()->get_width())) {
          push_to_node_stack(right,ast_copy,extracted_bit, node_stack_,using_extracted,using_extract_track);
        }
        else { // it is 0, so both matter        
          std::vector<std::pair<int,int>> extracted_bit_left;
          std::vector<std::pair<int,int>> extracted_bit_right;
          detect_partial_one(left_val,right_val,extracted_bit,extracted_bit_left,extracted_bit_right);
          push_to_node_stack(left,ast_copy,extracted_bit_left, node_stack_,using_extracted,using_extract_track);
          push_to_node_stack(right,ast_copy,extracted_bit_right, node_stack_,using_extracted,using_extract_track);
        }
      } else if (op.prim_op == smt::PrimOp::BVMul) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        cond_left = transferer.transfer_term(cond_left);
        cond_right = transferer.transfer_term(cond_right);
        std::string left_val = cond_left->to_string();
        std::string right_val = cond_right->to_string();
        using_extracted = true;
        if (is_all_zero(left_val)) // if all zeros
          push_to_node_stack(left,ast_copy,extracted_bit, node_stack_,using_extracted,using_extract_track);
          // node_stack_.push_back(make_pair(left,extracted_bit));
        else if (is_all_zero(right_val)) {
          push_to_node_stack(right,ast_copy,extracted_bit, node_stack_,using_extracted,using_extract_track);
        }
        else { // it is 0, so both matter
          std::vector<std::pair<int,int>> extracted_bit_left;
          std::vector<std::pair<int,int>> extracted_bit_right;
          detect_partial_zero(left_val,right_val,extracted_bit,extracted_bit_left,extracted_bit_right);
          push_to_node_stack(left,ast_copy,extracted_bit_left, node_stack_,using_extracted,using_extract_track);
          push_to_node_stack(right,ast_copy,extracted_bit_right, node_stack_,using_extracted,using_extract_track);
        }
      }
      else if((op.prim_op== smt::PrimOp::Extract)){
        auto b = op.idx0;
        auto p = op.idx1;
        for (const auto & arg : *ast){
          using_extracted = true;
          std::vector<std::pair<int,int>> new_extracted_bit;
          get_extract(extracted_bit,new_extracted_bit,b,p);
          if(!new_extracted_bit.empty())
            push_to_node_stack(arg,ast_copy,new_extracted_bit,node_stack_,using_extracted,using_extract_track);
        }       
      }
      else if((op.prim_op== smt::PrimOp::Concat)){
        ARG2(left,right);
        assert((left->get_sort()->to_string())!="Bool");
        assert((right->get_sort()->to_string())!="Bool");
        auto width_left = left->get_sort()->get_width();
        auto width_right = right->get_sort()->get_width();
        // using_extracted = true;
        std::vector<std::pair<int,int>> new_extracted_left;
        std::vector<std::pair<int,int>> new_extracted_right;
        get_concat_extract(extracted_bit,new_extracted_left,new_extracted_right,width_left,width_right);
        if(!new_extracted_left.empty()){
          push_to_node_stack(left,ast_copy,new_extracted_left,node_stack_,using_extracted,using_extract_track);
        }
        if(!new_extracted_right.empty()){
          push_to_node_stack(right,ast_copy,new_extracted_right,node_stack_,using_extracted,using_extract_track);
        }
      }
      else if((op.prim_op== smt::PrimOp::Zero_Extend)){
        ARG1(back);
        auto width_back = back->get_sort()->get_width();
        // auto count = 0;
        auto width_extend = op.idx0;
        std::vector<std::pair<int,int>> new_extracted_const;
        std::vector<std::pair<int,int>> new_extracted_back;
        // using_extracted = true;
        get_concat_extract(extracted_bit,new_extracted_const,new_extracted_back,width_extend,width_back);
        if(!new_extracted_back.empty()){
          push_to_node_stack(back,ast_copy, new_extracted_back,node_stack_,using_extracted,using_extract_track);
        }
      }
      else {
        if((op.prim_op== smt::PrimOp::BVComp)||(op.prim_op== smt::PrimOp::Distinct)||((op.prim_op== smt::PrimOp::BVUlt)||(op.prim_op==smt::Equal))){
          using_extracted = false;
        }
        for (const auto & arg : *ast){
          push_to_node_stack(arg, ast_copy, extracted_bit,node_stack_,using_extracted,using_extract_track);
          }
      }
    } // end non-variable case
  } // while ( not empty )
} // end of PartialModelGen::dfs_walk

void PartialModelGen::get_extract(const std::vector<std::pair<int,int>> old_extracts, std::vector<std::pair<int,int>> & new_extracts,const int left_bit, const int right_bit){
  for(const auto old_extract: old_extracts){
    auto left_old = old_extract.first; 
    auto right_old = old_extract.second;
    // if((left_old<=left_bit)&&(left_old>=right_bit)){
    //   if(right_old<=right_bit){
    //     new_extracts.push_back(std::make_pair(left_old,right_bit));
    //   }
    //   else{
    //     new_extracts.push_back(std::make_pair(left_old,right_old));
    //   }
    // }
    // else if((right_old<=left_bit)&&(left_old>=left_bit)){
    //   if(right_old<=right_bit){
    //     new_extracts.push_back(std::make_pair(left_bit,right_bit));
    //   }
    //   else{
    //     new_extracts.push_back(std::make_pair(left_bit,right_old));
    //   }
    // }
    new_extracts.push_back(std::make_pair(right_bit+left_old,right_bit+right_old));
    assert(right_bit+left_old<=left_bit);
  }
}

std::vector<smt::Term> PartialModelGen::previous_extracted(const smt::Term ast, const smt::Term arg){
  if(term_leaf_map.find(arg)==term_leaf_map.end()){
    assert(ast!=nullptr);
    term_leaf_map[arg]= ast;
    return {arg};
  }
  else if((term_leaf_map[arg]==ast)||(arg->is_value())||(arg->is_symbolic_const())){
    return {arg};
  }
  else{
    std::vector<smt::Term> traces;
    traces.push_back(arg);
    while(!traces.empty()){
      std::vector<smt::Term> new_traces;
      for(auto map=term_leaf_map.begin();map!=term_leaf_map.end();++map){
        for(const auto trace: traces){
        if(trace->compare(map->second)){
          new_traces.push_back(map->first);
        }
        }
      }
      traces.swap(new_traces);
      if(traces.empty()){
        return new_traces;
      }
    }
  }
}
void PartialModelGen::get_concat_extract(const std::vector<std::pair<int,int>> old_extracts, std::vector<std::pair<int,int>> & new_extracts_left,
std::vector<std::pair<int,int>> & new_extracts_right,
const int left_width, const int right_width){
  for(const auto old_extract: old_extracts){
    auto left_old = old_extract.first; 
    auto right_old = old_extract.second;
    if(right_width-1<right_old){
        new_extracts_left.push_back(std::make_pair(left_old-right_width,right_old-right_width));
    }
    else if(right_width-1>=left_old){
        new_extracts_right.push_back(std::make_pair(left_old,right_old));
    }
    else{
        new_extracts_left.push_back(std::make_pair(left_old-right_width,0));
        new_extracts_right.push_back(std::make_pair(right_width-1,right_old));
    }    
  }
}

void PartialModelGen::push_to_node_stack(const smt::Term arg,const smt::Term ast, const std::vector<std::pair<int,int>> extract_bit, 
          std::vector <std::pair<smt::Term,std::vector<std::pair<int,int>>>> & node_stack_,bool using_extracted,std::vector<bool> & using_extract_track){
    auto previous_result = previous_extracted(ast,arg);
    std::vector<std::pair<int,int>> new_extract_bit;
    if((previous_result.size()==1)&&(previous_result.back()==arg)){
      auto sort = arg->get_sort();
      if(sort->to_string()=="Bool"){       
        new_extract_bit.push_back(std::make_pair(0,0));
        node_stack_.push_back(std::make_pair(arg,new_extract_bit));
        using_extract_track.push_back(using_extracted);
      }
      else{
        if(using_extracted){
          node_stack_.push_back(std::make_pair(arg,extract_bit));
          using_extract_track.push_back(using_extracted);
        }
        else{
        auto width = sort->get_width();
        new_extract_bit.push_back(std::make_pair(width-1,0));
        node_stack_.push_back(std::make_pair(arg,new_extract_bit));
        using_extract_track.push_back(using_extracted);
        }
      }
    }
    else{
      for(const auto result:previous_result){
        assert(result->is_symbolic_const()||result->is_value());
        auto width = result->get_sort()->get_width();
        new_extract_bit.push_back(std::make_pair(width-1,0));
        node_stack_.push_back(std::make_pair(result,new_extract_bit));
        using_extract_track.push_back(false);
      }
    }

}


} // namespace pono
