/*********************                                                  */
/*! \file cex_generalizer.h
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Abstract class for enumerating axioms over a transition system
**        it does not modify the transition system, instead only returning
**        violated axioms sufficient for ruling out abstract counterexamples.
**
**/
#pragma once

#include <vector>

#include "smt-switch/smt.h"
#include "core/ts.h"
#include "frontends/btor2_encoder.h"

namespace pono {

class CexGeneralizer {
public:
  typedef std::vector<smt::UnorderedTermMap> CexTraceType;

protected:
  /// The generalized counterexample trace
  CexTraceType generalized_cex;

  /// Insert a variable-value pair at time t to the counterexample trace
  void cex_trace_insert(size_t k, const smt::Term & var, const smt::Term & val);
  /// Convert val to binary format
  std::string as_bits(std::string val);
  /// Print a variable-value map (according to the variable order in ts)
  void print_btor_vals_at_time(
    const smt::TermVec & variable_ordering,
    const smt::UnorderedTermMap & valmap,
    unsigned int time);

public:
  CexGeneralizer(const TransitionSystem & ts,
                 const BTOR2Encoder & btor_enc,
                 const CexTraceType & cex);
  
  const CexTraceType & get_cex_trace() const { return generalized_cex; }

  /// Print counterexample trace
  void print_witness_btor(const BTOR2Encoder & btor_enc,
                        const CexTraceType & cex);

}; // end of CexGeneralizer

} // namespace pono
