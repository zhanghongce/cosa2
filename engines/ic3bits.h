/*********************                                                  */
/*! \file ic3bits.h
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bit-level IC3 implementation that splits bitvector variables
**        into the individual bits for bit-level cubes/clauses
**        However, the transition system itself still uses bitvectors
**/

#pragma once

#include "engines/ic3.h"
#include "utils/syntax_analysis.h"
#include "utils/partial_model.h"

namespace pono {

class IC3Bits : public IC3
{
 public:
  // itp_se is the SolverEnum for the interpolator

  IC3Bits(const Property & p,
          const TransitionSystem & ts,
          const smt::SmtSolver & s,
          PonoOptions opt = PonoOptions());

  virtual ~IC3Bits() {}

  typedef IC3 super;

  void initialize() override;

 protected:

  smt::TermVec state_bits_;  ///< boolean variables + bit-vector variables
                             ///< split into individual bits

  PartialModelGen partial_model_getter;
  bool has_assumptions;
  bool keep_var_in_partial_model(const smt::Term & v) const;
  void build_ts_related_info();
  smt::Term next_curr_replace(const smt::Term & in) const { return ts_.solver()->substitute(in, nxt_state_updates_); }

  smt::UnorderedTermMap nxt_state_updates_; // a map from prime var -> next
  smt::UnorderedTermSet no_next_vars_; //  the inputs that appear to be state variables
  std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> constraints_curr_var_; // constraints (mapped to the current variables)
  // virtual method overrides

  IC3Formula get_model_ic3formula() const override;

  bool ic3formula_check_valid(const IC3Formula & u) const override;

  void check_ts() const override;

  virtual void predecessor_generalization(size_t i,
                                          const smt::Term & c,
                                          IC3Formula & pred) override;

  IC3Formula ExtractPartialModel(const smt::Term & p);

};

}  // namespace pono
