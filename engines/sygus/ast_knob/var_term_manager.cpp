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

// return delta(#terms)
unsigned VarTermManager::GetMoreTerms(Model * pre, Model * post) {
  // decide the policy
  assert(pre && post);
  std::string var_string = post->vars_to_canonical_string();
  assert(IN(var_string, terms_cache_)); // should already done this

  PerVarsetInfo & varset_info = terms_cache_.at(var_string);
  switch(varset_info.state.stage) {
    case PerVarsetInfo::state_t::WPARTIAL:
      // increase to WALL
      {
        unsigned nterm_walked = insert_from_termsmap_w_width(
          varset_info.terms_buffer /*IN*/, varset_info /*OUT*/, varset_info.state.partial_width_done, (unsigned)(-1) );
        if (nterm_walked != 0)
          return nterm_walked;
      } // else will continue to WALL (same as from cex)
    case PerVarsetInfo::state_t::WALL:
      // increase to FROMCEX
      varset_info.state.stage = PerVarsetInfo::state_t::FROMCEX;
      // and do the same as FROMCEX, so continue
    case PerVarsetInfo::state_t::FROMCEX:
      // stay FROMCEX, just try if we can do anything more
      return learn_terms_from_cex(pre, post, varset_info);
    default:
      assert(false);
  }
  assert(false);
} // GetMoreTerms

// we just won't compute canonical_string twice
const PerVarsetInfo & VarTermManager::SetupTermsForVar(
  Model * m, const std::string & canonical_string) {

  bool collect_constant = width_to_constants_.empty();
  std::unordered_set<smt::Term> varset;
  m->get_varset(varset);
  // now TERM_EXTRACT_DEPTH
  TermExtractor extractor(varset, collect_constant, GlobalAPdrConfig.TERM_EXTRACT_DEPTH);
  for (auto && t : terms_to_check_)
    extractor.WalkBFS(t);
  
  if (collect_constant)
    insert_from_constmap(extractor.GetConstants());
  // if collect constants

  terms_cache_t::iterator pos; bool succ;
  std::tie(pos, succ) = terms_cache_.emplace(canonical_string, 
    PerVarsetInfo(PerVarsetInfo::state_t::EMPTY, extractor.GetTerms()));
  auto & term_cache_item = pos->second;
  const auto & terms = pos->second.terms_buffer; // extractor.GetTerms();

  assert(!varset.empty());
  assert(!terms.empty());

  unsigned nterm_walked = 0;
  unsigned width_start = 0;
  unsigned width_end = GlobalAPdrConfig.INITIAL_TERM_WIDTH;
  do{
    nterm_walked += insert_from_termsmap_w_width(terms /*IN*/, term_cache_item /*OUT*/, width_start, width_end );
    width_start += GlobalAPdrConfig.INITIAL_TERM_INC;
    width_end += GlobalAPdrConfig.INITIAL_TERM_INC;
  } while(nterm_walked <= GlobalAPdrConfig.ACCUMULATED_TERM_BOUND);

  pos->second.state.stage = PerVarsetInfo::state_t::WPARTIAL;
  pos->second.state.partial_width_done = width_start; // the start of next time

  return term_cache_item;
} // SetupTermsForVar


// will distinguish constants and terms because we don't need c==c or c=/=c
const PerVarsetInfo & VarTermManager::GetAllTermsForVarsInModel(Model * m) {

  std::string var_string = m->vars_to_canonical_string();
  auto pos = terms_cache_.find(var_string);
  if ( pos != terms_cache_.end() )  {
    return pos->second;
  }

  return SetupTermsForVar(m, var_string);
} // GetAllTermsFor

// Later you may need to insert

// -------------------------------------------------------------------------

unsigned VarTermManager::insert_from_termsmap_w_width(
  const std::map<unsigned, smt::TermVec> & terms /*IN*/, PerVarsetInfo & term_cache_item /*OUT*/ , 
  unsigned width_bound_low /*IN*/, unsigned width_bound_high /*IN*/) 
{
  unsigned nterm_walked = 0;
  for (auto && w_t_pair : terms) {
    auto width = w_t_pair.first;
    if (! (width >= width_bound_low && width < width_bound_high))
      continue;

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
    if (! (width >= width_bound_low && width < width_bound_high))
      continue;

    const auto &cvec = w_cs_pair.second;
    for (auto && c : cvec) {
      term_cache_item.terms_strings.insert(c->to_raw_string());
      term_cache_item.terms[width].constants.push_back(c);
      ++ nterm_walked;
    }
  } // end of for each width_constant_pair
  return nterm_walked;
} // insert_from_termsmap_w_width

void VarTermManager::insert_from_constmap(const PerVarsetInfo::width_term_map_t & w_c_map) {
  for (const auto & width_constvec_pair : w_c_map) {
    for (const auto & c : width_constvec_pair.second)  {
      auto cnstr_str = c->to_raw_string();
      if (!IN(cnstr_str, constants_strings_)) {
        constants_strings_.insert(cnstr_str);
        width_to_constants_[width_constvec_pair.first].push_back(c);
      }
    }
  }
} // insert_from_constmap


} // namespace unsat_enum

} // namespace cosa
