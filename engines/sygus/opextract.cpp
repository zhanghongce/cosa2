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
#include "utils/container_shortcut.h"

#include <cassert>

namespace cosa {

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


  if(ast->is_symbolic_const()) {
    // use ast->to_string()
    constructs.insert_symbol(width, ast->to_string());
  } else if (ast->is_value()) {
    // use ast->to_string()
    constructs.insert_const(width, ast->to_string());
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
        constructs.insert_op_unary(width, op.prim_op); break;
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
        constructs.insert_op_binary(width, op.prim_op); break;
      case smt::PrimOp::BVComp: // equal 
        constructs.insert_op_comp(width, smt::PrimOp::Equal); break;
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
        constructs.insert_op_comp(width, op.prim_op); break;
      case smt::PrimOp::Concat:
        {
          ARG2
          constructs.insert_concat(width, sygus::concat_t(a1->get_sort()->get_width(),a2->get_sort()->get_width())); break;
        }
        break;
      case smt::PrimOp::Extract:
        assert (op.num_idx == 2);
        {
          ARG1
          constructs.insert_extract(width, sygus::extract_t(a1->get_sort()->get_width(),op.idx0,op.idx1)); 
        }
        break;
      
      case smt::PrimOp::Zero_Extend:
        assert (op.num_idx == 1);
        {
          ARG1
          constructs.insert_extend(width, sygus::extend_t(op.prim_op, op.idx0, a1->get_sort()->get_width()));
        }
        break;

      case smt::PrimOp::Sign_Extend:
        assert (op.num_idx == 1);
        {
          ARG1
          constructs.insert_extend(width, sygus::extend_t(op.prim_op, op.idx0, a1->get_sort()->get_width()));
        }
        break;


      case smt::PrimOp::Rotate_Left:
      case smt::PrimOp::Rotate_Right: {
        assert (op.num_idx == 1);
        constructs.insert_rotate(width, sygus::rotate_t(op.prim_op, op.idx0));
        break; }
      default: // do nothing
        break;
    } //  switch (op.prim_op)
  } // if it is op
} // OpExtractor::PreChild

void OpExtractor::PostChild(const smt::Term & ast) {

}


} // namespace cosa