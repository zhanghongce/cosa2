/*********************                                                  */
/*! \file prophecy_modifier.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Class for adding prophecy variables that predict a value some
**        constant number of steps before a property violation.
**/

#include "modifiers/prophecy_modifier.h"

using namespace smt;
using namespace std;

namespace pono {

ProphecyModifier::ProphecyModifier(TransitionSystem & ts)
    : ts_(ts), solver_(ts_.solver()), hm_(ts_)
{
}

pair<Term, Term> ProphecyModifier::get_proph(const Term & target, size_t delay)
{
  // first use history variables to delay target
  Term hist_var = hm_.get_hist(target, delay);

  // now add a prophecy variable which targets that history variable
  string name = "proph_" + target->to_string() + "_" + std::to_string(delay);
  Term proph_var = ts_.make_statevar(name, target->get_sort());
  // make it frozen
  ts_.assign_next(proph_var, proph_var);

  return { proph_var, hist_var };
}
smt::Term abstract_op(const smt::Term & in ,const smt::SmtSolver & solver_)// the file def 
//abs_op add slover_ here
{
  // 1. create function name
  // 2. extract the sort (type) of children
  // 3. make_sort
  // 4. make_symbol
  // 5. make_term(Apply,...)
  // return the result of 5
  // collect children ,opetatonum ite,three operators,
  string op_str = "un_func";
  SortVec sv;
  for ( auto it = in->begin(); it != in->end(); ++it){
  auto sort = (*it)->get_sort();
  sv.push_back(sort);
}
  sv.push_back(in -> get_sort());
  // do abstraction part ,bilud name
  Term abs_op;  //
      Sort func_sort =
        solver_->make_sort(FUNCTION, sv);  // make_sort and make_symbol directly
    abs_op = solver_->make_symbol(op_str, func_sort);


  TermVec args = { abs_op };
  args.insert(args.end(), in ->begin(), in->end());
  auto res = solver_->make_term(Apply, args);
 // make_term

return res;
}
}  // namespace pono
