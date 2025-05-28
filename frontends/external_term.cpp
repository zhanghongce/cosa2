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

#include "frontends/external_term.h"

using namespace smt;
using namespace std;

namespace pono {

ExternalTermInterface::ExternalTermInterface(const std::string & filename, TransitionSystem & ts)
    : super(ts.get_solver()), filename_(filename), ts_(ts)
{
  set_logic_all();
  int res = parse(filename_);
  assert(!res);  // 0 means success

  for(const auto & n_prop : defs_){
      // for proving aids
      if(n_prop.first.find("assertion.") == 0) // augmenting assertions
        assertions_.push_back(n_prop.second);
      if(n_prop.first.find("predicate.") == 0)
        predicates_.push_back(n_prop.second);
      if(n_prop.first.find("f1clause.") == 0)
        clauses_.push_back(n_prop.second);
      
      // For augmenting transition systems
      if(n_prop.first.find("assumption.") == 0)
        assumptions_.push_back(n_prop.second);
  }
}


smt::Term ExternalTermInterface::register_arg(const std::string & name, const smt::Sort & sort) {
  auto pos = ts_.named_terms().find(name);
  if (pos == ts_.named_terms().end()) {
    pos = ts_.named_terms().find("|"+name+"|");
  }
  if (pos == ts_.named_terms().end()) {
    throw PonoException("Cannot find term named: " + name);
  }
  
  arg_param_map_.add_mapping(name, pos->second);
  return pos->second; // we expect to get the term in the transition system.
}

smt::Term ExternalTermInterface::AddAssertions(const smt::Term &in) const{
  auto ret = in;
  for(const auto & t : assertions_) {
    ret = ts_.make_term(smt::And, ret, t);
  }
  return ret;
}

void ExternalTermInterface::AddAssumptionsToTS() {
  for(const auto & t : assumptions_)
    ts_.add_constraint(t);
}

}  // namespace pono
