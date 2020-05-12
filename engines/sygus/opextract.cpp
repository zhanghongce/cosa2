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
 ** \brief Operator extractor
 **
 ** 
 **/
 
#include "opextract.h"
#include "container_shortcut.h"

#include <cassert>
#include <queue>

namespace cosa {

namespace sygus{ 

bool operator==(const concat_t & a, const concat_t & b) {
  return ( (a.width1 == b.width1) && (a.width2 == b.width2) );
}
bool operator==(const extract_t & a, const extract_t & b) {
  return ( (a.h == b.h) && (a.l == b.l) && (a.input_width == b.input_width) );
}
bool operator==(const rotate_t & a, const rotate_t & b) {
  return ( (a.op == b.op) && (a.param == b.param) );
}
bool operator==(const extend_t & a, const extend_t & b) {
  return ( (a.input_width == b.input_width) && (a.op == b.op) && (a.totalwidth == b.totalwidth) );
}

template <class T>
inline size_t hash_combine(std::size_t seed, const T& v)
{
    std::hash<T> hasher;
    seed ^= hasher(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
    return seed;
}

size_t concat_hash::operator() (const concat_t & t) const {
  std::hash<uint64_t> hasher;
  return hash_combine(hasher(t.width2), t.width2);
}

size_t extract_hash::operator() (const extract_t & t) const {
  std::hash<uint64_t> hasher;
  return hash_combine(hash_combine(hasher(t.h), t.l), t.input_width);
}

size_t rotate_hash::operator() (const rotate_t & t) const {
  std::hash<uint64_t> hasher;
  return hash_combine(hasher(t.param), t.op);
}

size_t extend_hash::operator() (const extend_t & t) const {
  std::hash<uint64_t> hasher;
  return hash_combine(hash_combine(hasher(t.input_width), t.totalwidth), t.op);
}


} // namespace sygus


// ------------------------------------------------------

bool OpExtractor::Skip(const smt::Term & ast) {
  return IN(ast, walked_nodes_);
}

#define ARG1            \
      auto ptr = ast->begin();    \
      auto a1  = *(ptr++);      \
      assert (ptr == ast->end());

#define ARG2            \
      auto ptr = ast->begin();    \
      auto a1  = *(ptr++);      \
      auto a2  = *(ptr++);      \
      assert (ptr == ast->end());

void OpExtractor::PreChild(const smt::Term & ast) {
  walked_nodes_.insert(ast); // pre insert is okay
  auto sort_kind = ast->get_sort()->get_sort_kind() ;
  uint64_t width;
  
  if ( sort_kind == smt::SortKind::BOOL)
    width = 0;
  else if (sort_kind == smt::SortKind::BV)
    width = ast->get_sort()->get_width();
  else
    return; // we don't handle other cases

  if ( !IN(width, constructs) )
    constructs.insert(std::make_pair(width, sygus::BvConstructs()));
  sygus::BvConstructs & cnstr = constructs.at(width);

  if(ast->is_symbolic_const()) {
    // use ast->to_string()
    cnstr.symbol_names.insert(std::make_pair(ast->to_string(), ast));
  } else if (ast->is_value()) {
    // use ast->to_string()
    cnstr.constants.insert(ast->to_string());
  } else { // we will hope it is op
    smt::Op op;
    try {
      op = ast->get_op();
    } catch (NotImplementedException) {
      // op will be initialized correctly
      // so do nothing here
    }
  // op_unary, op_comp, op_concat, op_extract, op_rotate, op_extend
    // does not handle ite, repeat, convert, select, store ...
    switch (op.prim_op) {
      case smt::PrimOp::Not:
      case smt::PrimOp::BVNeg:
      case smt::PrimOp::BVNot:
        cnstr.op_unary.insert(op.prim_op); break;
      case smt::PrimOp::And:
      case smt::PrimOp::Or:
      case smt::PrimOp::Xor:
      case smt::PrimOp::Implies:
      case smt::PrimOp::Iff:
      case smt::PrimOp::BVAnd:
      case smt::PrimOp::BVOr:
      case smt::PrimOp::BVXor:
      case smt::PrimOp::BVNor:
      case smt::PrimOp::BVXnor:
      case smt::PrimOp::BVNand:
      case smt::PrimOp::BVAdd:
      case smt::PrimOp::BVSub:
      case smt::PrimOp::BVMul:
      case smt::PrimOp::BVUdiv:
      case smt::PrimOp::BVSdiv:
      case smt::PrimOp::BVUrem:
      case smt::PrimOp::BVSrem:
      case smt::PrimOp::BVSmod:
      case smt::PrimOp::BVShl:
      case smt::PrimOp::BVAshr:
      case smt::PrimOp::BVLshr:
        cnstr.op_binary.insert(op.prim_op); break;

      case smt::PrimOp::BVComp: // equal
        cnstr.op_comp.insert(smt::PrimOp::BVComp); break;
      case smt::PrimOp::Equal:
      case smt::PrimOp::Distinct:
      case smt::PrimOp::BVUlt:
      case smt::PrimOp::BVUle:
      case smt::PrimOp::BVUgt:
      case smt::PrimOp::BVUge:
      case smt::PrimOp::BVSlt:
      case smt::PrimOp::BVSle:
      case smt::PrimOp::BVSgt:
      case smt::PrimOp::BVSge:
        cnstr.op_comp.insert(op.prim_op); break;

      case smt::PrimOp::Concat:
        {
          ARG2
          cnstr.op_concat.insert(sygus::concat_t(a1->get_sort()->get_width(),a2->get_sort()->get_width())); 
        }
        break;
      case smt::PrimOp::Extract:
        assert (op.num_idx == 2);
        {
          ARG1
          cnstr.op_extract.insert(sygus::extract_t(a1->get_sort()->get_width(),op.idx0,op.idx1)); 
        }
        break;
      
      case smt::PrimOp::Zero_Extend:
        assert (op.num_idx == 1);
        {
          ARG1
          cnstr.op_extend.insert(sygus::extend_t(op.prim_op, op.idx0, a1->get_sort()->get_width())); 
        }
        break;

      case smt::PrimOp::Sign_Extend:
        assert (op.num_idx == 1);
        {
          ARG1
          cnstr.op_extend.insert(sygus::extend_t(op.prim_op, op.idx0, a1->get_sort()->get_width())); 
        }
        break;


      case smt::PrimOp::Rotate_Left:
      case smt::PrimOp::Rotate_Right:
        assert (op.num_idx == 1);
        cnstr.op_rotate.insert(sygus::rotate_t(op.prim_op, op.idx0));
        break;
      default: // do nothing
        break;
    } //  switch (op.prim_op)
  } // if it is op
} // OpExtractor::PreChild

void OpExtractor::PostChild(const smt::Term & ast) {

}


void OpExtractor::RemoveUnusedWidth() {
  typedef uint64_t width_t;
  //std::unordered_set<width_t> start_set;
  std::unordered_map<width_t, std::unordered_set<width_t>> use_map;

  std::unordered_set<width_t> reachable_set;
  std::queue<width_t> q;


  for (auto && width_cnstr : constructs) {
    auto width = width_cnstr.first;
    const auto & cnstr = width_cnstr.second;
    if (!cnstr.constants.empty() || 
        !cnstr.symbol_names.empty()) {
      q.push(width);
      use_map[width].insert(width);
    }
    if (!cnstr.op_unary.empty() || !cnstr.op_binary.empty() || !cnstr.op_concat.empty())
      use_map[width].insert(width);
    for (const auto & exd: cnstr.op_extend)
      use_map[width].insert(exd.input_width);
    for (const auto & extract: cnstr.op_extract)
      use_map[width].insert(extract.input_width);
    for (const auto & concats: cnstr.op_concat) {
      use_map[width].insert(concats.width1);      
      use_map[width].insert(concats.width2);      
    }   
  }

  // now do the graph reach algorithm
  while(!q.empty()) {
    width_t cur = q.front();
    q.pop();

    for (auto dstw : use_map[cur]) {
      if(!IN(dstw,reachable_set )) {
        reachable_set.insert(dstw);
        q.push(dstw);
      }
    }
  } // while queue is not empty
  auto pos = constructs.begin();
  while (pos != constructs.end()) {
    if (IN(pos->first, reachable_set))
      ++pos;
    else
      pos = constructs.erase(pos);
  } // remove not in reachable set

} // RemoveUnusedWidth


} // namespace cosa