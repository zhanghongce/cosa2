/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Variable to Terms Cache
 **
 ** 
 **/
 
#include "var_term_manager.h"
#include "term_extract.cpp"
#include "engines/apdr/config.h"
#include "utils/container_shortcut.h"
#include "utils/multitimer.h"

namespace cosa {

namespace unsat_enum {

// will distinguish constants and terms because we don't need c==c or c=/=c
const PerVarsetInfo & VarTermManager::GetAllTermsForVarsInModel(Model * m) {

  std::string var_string = m->vars_to_canonical_string();
  auto pos = terms_cache_.find(var_string);
  if ( pos != terms_cache_.end() )  {
    return pos->second;
  }
  
  GlobalTimer.RegisterEventStart("TermWalk", 0);
  unsigned nterm_walked = 0;

  bool collect_constant = width_to_constants_.empty();
  std::unordered_set<smt::Term> varset;
  m->get_varset(varset);
  // now TERM_EXTRACT_DEPTH
  TermExtractor extractor(varset, collect_constant, GlobalAPdrConfig.TERM_EXTRACT_DEPTH);
  for (auto && t : terms_to_check_)
    extractor.WalkBFS(t);

  if (collect_constant) {
    const auto w_c_map = extractor.GetConstants();
    for (const auto & width_constvec_pair : w_c_map) {
      for (const auto & c : width_constvec_pair.second)  {
        auto cnstr_str = c->to_raw_string();
        if (!IN(cnstr_str, constants_strings_)) {
          constants_strings_.insert(cnstr_str);
          width_to_constants_[width_constvec_pair.first].push_back(c);
        }
      }
    }
  } // if collect constnats

  auto & term_cache_item = terms_cache_[var_string];
  const auto & terms = extractor.GetTerms();

  assert(!varset.empty());
  assert(!terms.empty());

  for (auto && w_t_pair : terms) {
    auto width = w_t_pair.first;
    const auto & tvec = w_t_pair.second;
    for(auto && t : tvec) {
      auto tstr = t->to_raw_string();
      if (!IN(tstr, term_cache_item.terms_strings )){
        term_cache_item.terms_strings.insert(tstr);
        term_cache_item.terms[width].terms.push_back(t);
        ++ nterm_walked;
      }     
    } // end for each term
  } // end for terms

  // insert constants to 
  for (auto && w_cs_pair : width_to_constants_) {
    auto width = w_cs_pair.first;
    const auto &cvec = w_cs_pair.second;
    for (auto && c : cvec) {
      term_cache_item.terms_strings.insert(c->to_raw_string());
      term_cache_item.terms[width].constants.push_back(c);
      ++ nterm_walked;
    }
  } // end of for each width_constant_pair

  GlobalTimer.RegisterEventEnd("TermWalk", nterm_walked);
  return term_cache_item;
} // GetAllTermsFor

// Later you may need to insert

} // namespace unsat_enum

} // namespace cosa
