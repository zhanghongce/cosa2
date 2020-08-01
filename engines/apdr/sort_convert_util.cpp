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
 ** \brief bv bool converter
 **
 **
 **/
 
#include "sort_convert_util.h"

#include "utils/exceptions.h"

namespace cosa {

smt::Term bv_to_bool_msat(const smt::Term & t, const smt::SmtSolver & itp_solver_ )
{
  smt::Sort sort = t->get_sort();
  if (sort->get_sort_kind() == smt::SortKind::BV) {
    if (sort->get_width() != 1) {
      throw CosaException("Can't convert non-width 1 bitvector to bool.");
    }
    return itp_solver_->make_term(
        smt::Equal, t, itp_solver_->make_term(1, itp_solver_->make_sort(smt::BV, 1)));
  } else {
    return t;
  }
}

smt::Term bool_to_bv_msat(const smt::Term & t, const smt::SmtSolver & itp_solver_ ) {

  smt::Sort sort = t->get_sort();
  if (sort->get_sort_kind() == smt::SortKind::BOOL) {
    auto bv1sort = itp_solver_->make_sort(smt::SortKind::BV, 1);
    return itp_solver_->make_term(
        smt::Ite, t, itp_solver_->make_term(1,bv1sort), itp_solver_->make_term(0,bv1sort));
  } else {
    return t;
  }
}


} // namespace cosa


