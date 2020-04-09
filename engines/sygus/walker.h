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
 ** \brief term walker -- extract op/var or setup parital eval tree
 **
 ** 
 **/


#pragma once

#include "smt-switch/smt.h"

namespace cosa {

class Walker {

public:
  void Walk(const smt::Term & ast);
  void WalkRecursion(const smt::Term & ast);
  // if you want to buffer and avoid further walk
  // Skip is your chance to do that, return true
  // if already buffered
  virtual bool Skip(const smt::Term & ast) = 0;
  virtual void PreChild(const smt::Term & ast) = 0;
  virtual void PostChild(const smt::Term & ast) = 0;
}; // OpWalker




}  // namespace cosa