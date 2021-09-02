/*********************                                                        */
/*! \file property_if.cpp
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Frontend for the Verification Modulo Theories (VMT) format.
**        See https://vmt-lib.fbk.eu/ for more information.
**
**
**/

#include "frontends/property_if.h"

using namespace smt;
using namespace std;

namespace pono {

PropertyInterface::PropertyInterface(std::string filename, TransitionSystem & ts)
    : super(ts.get_solver()), filename_(filename), ts_(ts)
{
  set_logic_all();
  int res = parse(filename_);
  assert(!res);  // 0 means success

  for(const auto & n_prop : defs_){
      if(n_prop.first.find("assertion.") == 0)
        assertions_.push_back(n_prop.second);
      if(n_prop.first.find("assumption.") == 0)
        assumptions_.push_back(n_prop.second);
  }
}


smt::Term PropertyInterface::register_arg(const std::string & name, const smt::Sort & sort) {
  auto tmpvar = ts_.lookup(name);
  arg_param_map_.add_mapping(name, tmpvar);
  return tmpvar; // we expect to get the term in the transition system.
}

smt::Term PropertyInterface::AddAssertions(const smt::Term &in) const{
  auto ret = in;
  for(const auto & t : assertions_) {
    ret = ts_.make_term(smt::And, ret, t);
  }
  return ret;
}

void PropertyInterface::AddAssumptionsToTS() {
  for(const auto & t : assumptions_)
    ts_.add_constraint(t);
}



}  // namespace pono
