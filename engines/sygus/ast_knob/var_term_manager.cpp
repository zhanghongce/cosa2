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
#include "term_extract.h"
#include "term_learning.h"
#include "engines/apdr/config.h"
#include "utils/container_shortcut.h"
#include "utils/multitimer.h"

#include <cassert>

namespace cosa {

namespace unsat_enum {

// return delta(#terms)
unsigned VarTermManager::GetMoreTerms(Model * pre, Model * post, TermLearner & term_learner) {
  // decide the policy
  assert(pre && post);
  std::string var_string = post->vars_to_canonical_string();
  assert(IN(var_string, terms_cache_)); // should already done this

  PerVarsetInfo & varset_info = terms_cache_.at(var_string);
  
  assert(varset_info.state.stage != PerVarsetInfo::state_t::EXTRACTBITS);
  assert(GlobalAPdrConfig.TERM_MODE != GlobalAPdrConfig.VAR_C_EXT);
  // if we already extract bits, we should be forever good

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
      {
        auto nterms = term_learner.learn_terms_from_cex(pre, post, varset_info);
        if (nterms != 0)
          return nterms;
        // else
        varset_info.state.stage = PerVarsetInfo::state_t::EXTRACTBITS;
      }
    case PerVarsetInfo::state_t::EXTRACTBITS:
      return term_learner.vars_extract_bit_level(post, varset_info);
    default:
      assert(false);
  }
  assert(false);
} // GetMoreTerms

// we just won't compute canonical_string twice
const PerVarsetInfo & VarTermManager::SetupTermsForVarModelNormal(
  Model * m, const std::string & canonical_string) {

  bool collect_constant = width_to_constants_.empty();
  std::unordered_set<smt::Term> varset;
  m->get_varset(varset);

  terms_cache_t::iterator pos; bool succ;
  std::tie(pos, succ) = terms_cache_.emplace(canonical_string, 
    PerVarsetInfo(PerVarsetInfo::state_t::EMPTY));

  // now TERM_EXTRACT_DEPTH
  TermExtractor extractor(varset, collect_constant, 
    GlobalAPdrConfig.TERM_EXTRACT_DEPTH, 
    pos->second.terms_buffer,
    pos->second.all_terms);

  for (auto && t : terms_to_check_)
    extractor.WalkBFS(t);
  
  if (collect_constant)
    insert_from_constmap(extractor.GetConstants());
  // if collect constants

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
const PerVarsetInfo & VarTermManager::GetAllTermsForVarsInModel(Model * m , smt::SmtSolver & s) {

  std::string var_string = m->vars_to_canonical_string();
  auto pos = terms_cache_.find(var_string);
  if ( pos != terms_cache_.end() )  {
    return pos->second;
  }
  if (GlobalAPdrConfig.TERM_MODE == GlobalAPdrConfig.FROM_DESIGN_LEARN_EXT)
    return SetupTermsForVarModelNormal(m, var_string);
  if (GlobalAPdrConfig.TERM_MODE == GlobalAPdrConfig.VAR_C_EXT)
    return SetupTermsForVarModeExt(m, var_string, s);
  assert(false);
} // GetAllTermsFor

// Later you may need to insert

// -------------------------------------------------------------------------


const PerVarsetInfo & VarTermManager::SetupTermsForVarModeExt(
  Model * m, const std::string & canonical_string, smt::SmtSolver & solver_) {
  

  bool collect_constant = width_to_constants_.empty();
  std::unordered_set<smt::Term> varset;
  m->get_varset(varset);

  terms_cache_t::iterator pos; bool succ;
  std::tie(pos, succ) = terms_cache_.emplace(canonical_string, 
    PerVarsetInfo(PerVarsetInfo::state_t::EXTRACTBITS));

  if (collect_constant) {
    // now TERM_EXTRACT_DEPTH
    ConstantExtractor extractor(width_to_constants_, constants_strings_);

    for (auto && t : terms_to_check_)
      extractor.WalkBFS(t);
    
    // -> width_to_constants_
    // todo make sure bit-1 has 1 and only 1 value
  }
  // if collect constants

  auto & term_cache_item = pos->second;
  // const auto & terms = term_cache_item.terms; // extractor.GetTerms();

  assert(!varset.empty());

  // insert vars and their extracts
  insert_vars_and_extracts(term_cache_item, varset, solver_);

  if (term_cache_item.terms.find(1) == term_cache_item.terms.end()  ||
        term_cache_item.terms.at(1).constants.empty()) {
    auto c0 = solver_->make_term(0);
    term_cache_item.terms_strings.insert(c0->to_raw_string());
    term_cache_item.terms[1].constants.push_back(c0);
  }

  return term_cache_item;

} // SetupTermsForVar



// -------------------------------------------------------------------------

void VarTermManager::insert_vars_and_extracts(
  PerVarsetInfo & term_cache_item /*OUT*/ , const smt::UnorderedTermSet & varset, smt::SmtSolver & solver_  ) 
{
  for (const auto & v : varset) {
    unsigned width;
    if (v->get_sort()->get_sort_kind() == smt::SortKind::BOOL )
      width = 1;
    else if (v->get_sort()->get_sort_kind() == smt::SortKind::BV )
      width = v->get_sort()->get_width();
    else
      continue;
    auto res = term_cache_item.terms_strings.insert(v->to_raw_string());
    if(res.second) {
      term_cache_item.terms[width].terms.push_back(v);
      if (width > 1) {
        for (unsigned idx = 0; idx < width; ++idx) {
          auto t = solver_->make_term(smt::Op(smt::PrimOp::Extract, idx, idx), v);
          auto res = term_cache_item.terms_strings.insert(t->to_raw_string());
          if (res.second)
            term_cache_item.terms[1].terms.push_back(t);
        } // for each bit       
      } // if width > 1
    } // if insert successful    
  } // for each var
} // insert_vars_and_extracts

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
      auto ins_res = term_cache_item.terms_strings.insert(tstr);
      if (ins_res.second) { // if indeed inserted
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
      auto ins_res = term_cache_item.terms_strings.insert(c->to_raw_string());
      if(ins_res.second) {
        term_cache_item.terms[width].constants.push_back(c);
        ++ nterm_walked;
      } // end if really inserted
    }
  } // end of for each width_constant_pair
  return nterm_walked;
} // insert_from_termsmap_w_width

void VarTermManager::insert_from_constmap(const PerVarsetInfo::width_term_map_t & w_c_map) {
  for (const auto & width_constvec_pair : w_c_map) {
    for (const auto & c : width_constvec_pair.second)  {
      auto cnstr_str = c->to_raw_string();
      auto ins_res = constants_strings_.insert(cnstr_str);
      if (ins_res.second) // if insertion is successful
        width_to_constants_[width_constvec_pair.first].push_back(c);
    }
  }
} // insert_from_constmap


} // namespace unsat_enum

} // namespace cosa
