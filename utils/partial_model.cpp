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


static std::vector<std::pair<int, int>> merge_intervals(const std::vector<std::pair<int, int>> &intervals) {
    if (intervals.empty()) {
        return {};
    }

    std::vector<std::pair<int, int>> sorted_intervals = intervals;
    // Sort by the second value (the smaller one) in descending order
    std::sort(sorted_intervals.begin(), sorted_intervals.end(), [](const auto &a, const auto &b) {
        return a.second > b.second;
    });

    std::vector<std::pair<int, int>> merged_intervals;
    merged_intervals.push_back(sorted_intervals[0]);

    for (size_t i = 1; i < sorted_intervals.size(); ++i) {
        auto &last_merged_interval = merged_intervals.back();
        if (sorted_intervals[i].first >= last_merged_interval.second - 1) {
            last_merged_interval.second = std::min(sorted_intervals[i].second, last_merged_interval.second);
            last_merged_interval.first = std::max(sorted_intervals[i].first, last_merged_interval.first);
        } else {
            merged_intervals.push_back(sorted_intervals[i]);
        }
    }
    return merged_intervals;
}

void PartialModelGen::GetVarListForAsts_in_bitlevel(const std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> & input_asts_slices, 
    std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & out) {
  dfs_walked_extract.clear();
  std::unordered_map<smt::Term,pair_set> varset_slices;
  for (const auto & ast_slice_pair : input_asts_slices) {
    for (const auto & h_l_pair : ast_slice_pair.second)
      dfs_walk_bitlevel(ast_slice_pair.first, h_l_pair.first, h_l_pair.second, varset_slices);
  }
  for (const auto & var_slice_pair : varset_slices) {
    std::vector<std::pair<int,int>> intervals(var_slice_pair.second.begin(), var_slice_pair.second.end());
    auto merged_intervals = merge_intervals(intervals);
    out.emplace(var_slice_pair.first, merged_intervals);    
  }
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

  static std::unordered_map<unsigned, std::string> width2fullones; // a map that stores the string for all ones of different widths

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

// #b0000 -> 0000
// (_ bvX W) -> X in binary (W-wide)
static inline std::string to_unified_bvconst(const std::string & s) {
  if (s.substr(0,2) == "#b")
    return s.substr(2);
  
  std::string decimal, width;
  bool conv_succ = extract_decimal_width(s, decimal, width);
  assert(conv_succ);
  
  auto binary = syntax_analysis::decimal_to_binary(decimal);
  auto width_int = syntax_analysis::StrToULongLong(width,10);
  if(binary.length() < width_int)
     binary.insert(0, width_int - binary.size(), '0');
  return binary;
}


void find_consecutive_zeros_ones(std::string s, 
  const std::vector<std::pair<int, int>> &ranges,  
  std::vector<std::pair<int, int>> & ranges_of_zeros,
  std::vector<std::pair<int, int>> & ranges_of_ones) {
  
  std::reverse(s.begin(),s.end());
  for (const auto & msb_lsb_pair : ranges )  {
    auto msb = msb_lsb_pair.first;
    auto lsb = msb_lsb_pair.second;
    assert(lsb >= 0 && msb < s.length() && msb >= lsb);

    int prev_i = lsb;
    for (int i = lsb+1; i<=msb+1; ++i) {
      if (s[i] != s[prev_i] || i == msb+1) {
        if (s[prev_i]  == '0')
          ranges_of_zeros.push_back({i-1, prev_i});
        else
          ranges_of_ones.push_back({i-1,prev_i});
        prev_i = i;
      }
    }
  }
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


void PartialModelGen::dfs_walk(const smt::Term & input_ast ) {
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


void PartialModelGen::dfs_walk_bitlevel(const smt::Term & input_ast, int high, int low, 
    std::unordered_map<smt::Term, pair_set> & varset_slice) {
  std::vector <std::pair<smt::Term,std::pair<int,int>>> node_stack_;
  
  // push the root node
  auto sort = input_ast->get_sort();
  auto input_width = sort->get_sort_kind() == smt::SortKind::BOOL ? 1 : sort->get_width();
  assert(high >= low && low >= 0 && high < input_width);
  node_stack_.push_back({input_ast,{high, low}});

  while(!node_stack_.empty()) {
    auto ast = node_stack_.back().first;
    auto extracted_bit = node_stack_.back().second;
    auto width = (ast->get_sort()->get_sort_kind() == smt::SortKind::BOOL) ? 1 : ast->get_sort()->get_width();
    assert(extracted_bit.second >= 0 && extracted_bit.first >= extracted_bit.second && extracted_bit.first < width);
    
    // check if we have walked this node (w. the same extracted_bit)
    auto pos = dfs_walked_extract.find(ast);
    if(pos != dfs_walked_extract.end() && (pos->second.find(extracted_bit) != pos->second.end()) ) {
      node_stack_.pop_back();
      continue;
    }
    dfs_walked_extract[ast].insert(extracted_bit);

    smt::Op op = ast->get_op();
    if (op.is_null()) { // this is the root node
      if (ast->is_symbolic_const()) {
        varset_slice[ast].insert(extracted_bit);
      }
      // using_extracted = false;
      node_stack_.pop_back(); // no need to wait for the next time
      continue;
    } else { // non variable/non constant case
      if (op.prim_op == smt::PrimOp::Ite)  {
        ARG3(cond, texpr, fexpr)
        auto cond_val = solver_->get_value(cond);
        assert(cond_val->is_value());
        // using_extracted = true;
        if ( is_all_one(cond_val->to_string(),1) ) {
          ///For the condition, we never use the extracted terms.
          node_stack_.push_back({cond,{0,0}});
          node_stack_.push_back({texpr, extracted_bit});
        }
        else {
          node_stack_.push_back({cond,{0,0}});
          node_stack_.push_back({fexpr, extracted_bit});
        }
      } else if (op.prim_op == smt::PrimOp::Implies) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        assert(ast->get_sort()->get_sort_kind() == smt::SortKind::BOOL || ast->get_sort()->get_width()==1);
        if (!( is_all_one(cond_left->to_string(),1) )) {       
          node_stack_.push_back({left, {0,0}});
        }
        else if ( is_all_one(cond_right->to_string(), 1) ) {  
          node_stack_.push_back({right, {0,0}});
        } else {
          node_stack_.push_back({left, {0,0}});
          node_stack_.push_back({right, {0,0}});      
        }
      } else if (op.prim_op == smt::PrimOp::And) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        assert(ast->get_sort()->get_sort_kind() == smt::SortKind::BOOL || ast->get_sort()->get_width()==1);
        if (!( is_all_one(cond_left->to_string(),1) )) {  
          node_stack_.push_back({left, {0,0}});
        } else if (!(is_all_one(cond_right->to_string(), 1))) {
          node_stack_.push_back({right, {0,0}});
        } else {
          node_stack_.push_back({left, {0,0}});
          node_stack_.push_back({right, {0,0}});
        }
      } else if (op.prim_op == smt::PrimOp::Or) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        assert(ast->get_sort()->get_sort_kind() == smt::SortKind::BOOL || ast->get_sort()->get_width()==1);
        if (is_all_one(cond_left->to_string(),1)) {
          node_stack_.push_back({left, {0,0}});
        }
        else if (is_all_one(cond_right->to_string(), 1)) {
          node_stack_.push_back({right, {0,0}});
        } else  { // it is 0, so both matter
          node_stack_.push_back({left, {0,0}});
          node_stack_.push_back({right, {0,0}});
        }
      } else if (op.prim_op == smt::PrimOp::BVAnd || op.prim_op == smt::PrimOp::BVNand) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        std::string left_val = to_unified_bvconst(cond_left->to_string());
        std::string right_val = to_unified_bvconst(cond_right->to_string());
        // TODO: 
        std::vector<std::pair<int, int>> left_zero, left_one;
        find_consecutive_zeros_ones(left_val, {extracted_bit}, left_zero, left_one);
        for(const auto & z: left_zero) { // track left is okay
          node_stack_.push_back({left,z});
        }
        std::vector<std::pair<int, int>> right_zero, right_one;
        find_consecutive_zeros_ones(right_val, left_one, right_zero, right_one);
        for(const auto & z: right_zero) { // track right is okay
          node_stack_.push_back({right,z});
        }
        for(const auto & both_one: right_one) {
          node_stack_.push_back({left, both_one});
          node_stack_.push_back({right, both_one});
        }
      } else if (op.prim_op == smt::PrimOp::BVOr  || op.prim_op == smt::PrimOp::BVNor) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        std::string left_val = to_unified_bvconst(cond_left->to_string());
        std::string right_val = to_unified_bvconst(cond_right->to_string());
        // TODO: 
        std::vector<std::pair<int, int>> left_zero, left_one;
        find_consecutive_zeros_ones(left_val, {extracted_bit}, left_zero, left_one);
        for(const auto & one: left_one) { // track left is okay
          node_stack_.push_back({left,one});
        }
        std::vector<std::pair<int, int>> right_zero, right_one;
        find_consecutive_zeros_ones(right_val, left_zero, right_zero, right_one);
        for(const auto & one: right_one) { // track right is okay
          node_stack_.push_back({right,one});
        }
        for(const auto & both_zero: right_zero) {
          node_stack_.push_back({left, both_zero});
          node_stack_.push_back({right, both_zero});
        }
      } else if (op.prim_op == smt::PrimOp::BVMul) {
        ARG2(left,right)
        auto cond_left = solver_->get_value(left);
        auto cond_right = solver_->get_value(right);
        assert(cond_left->is_value() && cond_right->is_value());
        std::string left_val = cond_left->to_string();
        std::string right_val = cond_right->to_string();
        auto left_w = left->get_sort()->get_width();
        auto right_w = right->get_sort()->get_width();
        if (is_all_zero(left_val)) // if all zeros
          node_stack_.push_back({left, {left_w-1,0}});
          // node_stack_.push_back(make_pair(left,extracted_bit));
        else if (is_all_zero(right_val)) 
          node_stack_.push_back({right, {right_w-1,0}});
        else {
          node_stack_.push_back({left, {left_w-1,0}});
          node_stack_.push_back({right, {right_w-1,0}});
        }
      } else if (op.prim_op == smt::PrimOp::BVAdd) {
        ARG2(left,right)
        auto msb = extracted_bit.first;
        node_stack_.push_back({left, {msb,0}}); // []
        node_stack_.push_back({right, {msb,0}});
      } else if (op.prim_op == smt::PrimOp::BVNot) {
        ARG1(back)
        node_stack_.push_back({back, extracted_bit}); // []
      } else if (op.prim_op == smt::PrimOp::BVXor || op.prim_op == smt::PrimOp::BVXnor) {
        ARG2(left, right)
        node_stack_.push_back({left, extracted_bit}); // []
        node_stack_.push_back({right, extracted_bit}); // []
      } else if((op.prim_op== smt::PrimOp::Extract)) { // WIP
        auto b = op.idx0;
        auto p = op.idx1;
        auto msb = extracted_bit.first;
        auto lsb = extracted_bit.second;
        for (const auto & arg : *ast)
          node_stack_.push_back({arg, {p+msb,p+lsb}});
      }
      else if((op.prim_op== smt::PrimOp::Concat)){
        ARG2(left,right);
        auto width_left = left->get_sort()->get_width();
        auto width_right = right->get_sort()->get_width();
        auto msb = extracted_bit.first;
        auto lsb = extracted_bit.second;
        if(lsb >= width_right) {
          // work on left
          node_stack_.push_back({left, {msb-width_right, lsb-width_right}});
        } else if (msb <width_right) {
          // work on right
          node_stack_.push_back({right, {msb, lsb}});
        } else {
          // left and right
          node_stack_.push_back({left, {msb-width_right, 0}});
          node_stack_.push_back({right, {width_right-1, lsb}});
        }
      }
      else if(op.prim_op== smt::PrimOp::Zero_Extend || op.prim_op== smt::PrimOp::Sign_Extend){
        ARG1(back);
        auto width_back = back->get_sort()->get_width();
        // auto count = 0;
        auto width_extend = op.idx0;
        auto msb = extracted_bit.first;
        auto lsb = extracted_bit.second;
        if (msb >= width_back)
          node_stack_.push_back({back, {width_back-1, lsb}});
        else 
          node_stack_.push_back({back, {msb, lsb}});
      }
      else {
        // if((op.prim_op== smt::PrimOp::BVComp)||(op.prim_op== smt::PrimOp::Distinct)||((op.prim_op== smt::PrimOp::BVUlt)||(op.prim_op==smt::Equal)))
        for (const auto & arg : *ast) {
          auto arg_width = (arg->get_sort()->get_sort_kind() == smt::SortKind::BOOL) ? 1 : arg->get_sort()->get_width();
          node_stack_.push_back({arg,{arg_width-1,0}});
        }
      }
    } // end non-variable case
  } // while ( not empty )
} // end of PartialModelGen::dfs_walk



} // namespace pono
