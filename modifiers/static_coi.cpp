/*********************                                                  */
/*! \file coi.cpp
** \verbatim
** Top contributors (to current version):
**   Florian Lonsing, Makai Mann
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class for performing cone of influence reduction
**
**
**/

#include "modifiers/static_coi.h"
#include "utils/term_walkers.h"


#include "assert.h"
#include "smt-switch/utils.h"
#include "utils/logger.h"

using namespace smt;
using namespace std;

namespace pono {

StaticConeOfInfluence::StaticConeOfInfluence(TransitionSystem & ts,
                                             const TermVec & to_keep,
                                             int verbosity)
    : ts_(ts), verbosity_(verbosity), coi_(ts_, verbosity_)
{
  logger.log(1, "Starting static cone-of-influence (COI) analysis:");
  logger.log(1, "  - input variables: {}", ts_.inputvars().size());
  logger.log(1, "  - state variables: {}", ts_.statevars().size());
  logger.log(1, "  - constraints: {}", ts_.constraints().size());

  // compute the cone-of-influence based on the given variables
  orig_num_statevars_ = ts_.statevars().size();
  orig_num_inputvars_ = ts_.inputvars().size();
  coi_.compute_coi(to_keep);

  const UnorderedTermSet & statevars_in_coi = coi_.statevars_in_coi();
  const UnorderedTermSet & inputvars_in_coi = coi_.inputvars_in_coi();
  assert(statevars_in_coi.size() <= ts_.statevars().size());
  assert(inputvars_in_coi.size() <= ts_.inputvars().size());

  ts_.rebuild_trans_based_on_coi(statevars_in_coi, inputvars_in_coi);

  // NOTE: Cannot expect ts_.statevars().size() == statevars_in_coi.size()
  //       because, we cannot remove state variables from system that
  //       occur in init. This is because COI ignores init, and removing
  //       them would make the TS ill-formed. This should not affect
  //       performance though, since they were removed from trans
  assert(inputvars_in_coi.size() == ts_.inputvars().size());

  logger.log(
      1,
      "COI analysis completed: {} remaining input variables, {} original",
      inputvars_in_coi.size(),
      orig_num_inputvars_);
  logger.log(
      1,
      "COI analysis completed: {} remaining state variables, {} original",
      statevars_in_coi.size(),
      orig_num_statevars_);
  logger.log(1,
             "COI analysis note: state variables occurring in init will "
             "not be removed from system");
}

bool AstHasUF(const smt::Term &t, smt::SmtSolver s) {
    TermOpCollector collector(s);
    UnorderedTermSet termset;
    collector.find_matching_terms(t, {smt::PrimOp::Apply}, termset);
    return !(termset.empty());
}

void RegsInAst_coi(const smt::Term &t, smt::UnorderedTermSet & ret, const TransitionSystem & ts) {
    UnorderedTermSet varset;
    get_free_symbols(t, varset);
    for(const auto & var : varset)
        if(ts.statevars().find(var) != ts.statevars().end())
            ret.insert(var);
}


bool UninterpretedFuncCOICover(const TransitionSystem & ts, const Property & prop, unsigned bound) {
    auto bad = prop.prop();
    if(AstHasUF(bad, ts.solver()))
        return true;

    smt::UnorderedTermSet reg_set;
    RegsInAst_coi(bad, reg_set, ts);

    smt::UnorderedTermSet reg_visited;
    
    for (size_t idx = 0; idx <= bound; ++ idx) {
        smt::UnorderedTermSet new_reg_to_visit;
        for (const auto & reg : reg_set) {
            auto pos = ts.state_updates().find(reg);
            if (pos == ts.state_updates().end())  // this is likely
                continue;  // because ts_ may promote input variables
            auto next_func = pos->second;
            if(AstHasUF(next_func, ts.solver()))
                return true;
            RegsInAst_coi(next_func, new_reg_to_visit, ts);
            reg_visited.insert(reg);
        }
        reg_set.clear();
        for (const auto & reg : new_reg_to_visit) {
            if (reg_visited.find(reg) == reg_visited.end()) {
                reg_set.insert(reg);
            }
        }
    }
    return false;
}

}  // namespace pono
