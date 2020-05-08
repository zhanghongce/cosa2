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

namespace cosa {


bool OpExtractor::Skip(const smt::Term & ast) {
  return IN(ast, walked_nodes_);
}

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
  } else if (ast->is_value()) {
    // use ast->to_string()
  } else { // we will hope it is op
    smt::Op op;
    try {
      op = ast->get_op();
    } catch (NotImplementedException) {
      // op will be initialized correctly
    }

    switch (op.prim_op) {
      case smt::PrimOp::Not:
      case smt::PrimOp::BVNeg:
      case smt::PrimOp::BVNot:

      case smt::PrimOp::And:
      case smt::PrimOp::Or:
      case smt::PrimOp::Xor:


    }
/*


  And = 0,
  Or,
  Xor,
  Implies,
  Iff, // bool's -> bool
  
  Ite, // ???

  Equal,
  Distinct,

  Concat,
  Extract,
  BVNot,
  BVNeg,
  BVAnd,
  BVOr,
  BVXor,
  BVNand,
  BVNor,
  BVXnor,
  BVComp,
  BVAdd,
  BVSub,
  BVMul,
  BVUdiv,
  BVSdiv,
  BVUrem,
  BVSrem,
  BVSmod,
  BVShl,
  BVAshr,
  BVLshr,
  BVUlt,
  BVUle,
  BVUgt,
  BVUge,
  BVSlt,
  BVSle,
  BVSgt,
  BVSge,
  Zero_Extend,
  Sign_Extend,
  Repeat,
  Rotate_Left,
  Rotate_Right,
*/
  }
}

void OpExtractor::PostChild(const smt::Term & ast) {

}


} // namespace cosa