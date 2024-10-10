#pragma once

#include "smt-switch/smt.h"


// var info:
//     produce available predicates
//
// cex : map -> var info
//       maximum frame it gets
//       which predicate it has tried


// first try: control bit + predicates, if insufficient, add data bits
// struct PerCexInfo{
// };

struct PerCexInfo {
  smt::TermVec preds_to_use;
};

struct PerVarInfo {
  std::unordered_set<smt::Term> vars_noslice_in_cex;
  std::string vars_noslice_canonical_string;

  bool related_info_populated;
  smt::Term related_trans;
  smt::TermVec preds_w_subset_vars;
  smt::TermVec preds_w_related_vars;

  PerVarInfo(std::unordered_set<smt::Term> && vars, std::string && hashstring):
    vars_noslice_in_cex(vars), vars_noslice_canonical_string(hashstring), related_info_populated(false)
   {}
};

