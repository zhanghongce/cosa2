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

struct PerVarInfo {
  std::unordered_set<smt::Term> vars_noslice_in_cex;
  std::string vars_noslice_canonical_string;
  PerVarInfo(std::unordered_set<smt::Term> && vars, std::string && hashstring):
    vars_noslice_in_cex(vars), vars_noslice_canonical_string(hashstring)
   {}
};

