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
  
  PerCexInfo(smt::TermVec && pred) : preds_to_use(pred) {}
};

struct PerUnslicedVarInfo { // `unsliced` means the variables without `extract`
  std::unordered_set<smt::Term> vars_in_cex;
  std::string vars_canonical_string;

  unsigned ref_count; // we want to know, if the CTIs are often about a certain vars or not
                      // this is not used for memory management
                      // because once a cex is generated, it will not be deleted anyway

  bool related_info_populated;
  smt::Term related_trans;
  smt::TermVec preds_w_subset_vars;
  smt::TermVec preds_w_related_vars;

  PerUnslicedVarInfo(std::unordered_set<smt::Term> && vars, const std::string & hashstring) :
    vars_in_cex(std::move(vars)), vars_canonical_string(hashstring),
    ref_count(0), related_info_populated(false) {   }
};

struct PerSlicedVarInfo {
  std::unordered_set<smt::Term> slicedvars_in_cex;
  std::string vars_canonical_string;
  PerUnslicedVarInfo * unsliced_varinfo;

  PerSlicedVarInfo(std::unordered_set<smt::Term> && vars, const std::string & hashstring,
    PerUnslicedVarInfo * unsliced_varptr
  ):
    slicedvars_in_cex(std::move(vars)), vars_canonical_string(hashstring), 
    unsliced_varinfo(unsliced_varptr)
   {}
};


