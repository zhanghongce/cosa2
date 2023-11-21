/*********************                                                        */
/*! \file property_if.h
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Frontend for properties in 
**       (define-fun assertion.0 ...) or (define-fun assumption.0 ...)
**
**
**/

#pragma once

#include <iostream>

#include "assert.h"
#include "core/rts.h"
#include "smt-switch/smt.h"
#include "smt-switch/smtlib_reader.h"
#include "utils/exceptions.h"

namespace pono {
class PropertyInterface : public smt::SmtLibReader
{
 public:
  PropertyInterface(std::string filename, TransitionSystem & ts);

  typedef SmtLibReader super;

  smt::Term AddAssertions(const smt::Term &in) const;

  smt::Term get_assertion() const { return assertions_.at(0); }


 protected:
  // overloaded function, used when arg list of function is parsed
  // NOTE: | |  pipe quotes are removed.
  virtual smt::Term register_arg(const std::string & name, const smt::Sort & sort) override;

  std::string filename_;

  TransitionSystem & ts_;

  smt::TermVec assertions_;

};

}  // namespace pono
