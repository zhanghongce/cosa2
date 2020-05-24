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
 ** \brief SyGuS Query Generator
 **
 ** 
 **/
 
#pragma once
 
#include "apdr/config.h"
#include "sygus/partial_model.h"
#include "sygus/opextract.h"
#include <core/ts.h>

#include <string_view> 

namespace cosa {
 
namespace sygus {
 
// cex vars with that or fewer variables
// fact vars with that or more variables (the extra ones will be dropped)


// the buffer class for T, INIT and etc.
class SyGuSTransBuffer {

protected:
  std::string primal_var_def_;
  std::string prime_var_def_;
  std::string input_var_def_;

  std::string trans_def_;
  std::string trans_use_;
  std::string init_def_;
  std::string init_use_;
  
  std::string state_arg_def_;
  std::string state_arg_use_;

  std::unordered_map<std::string, std::string> state_to_next_map_;

public:
  // you also need to know this to generate the right arg lists
  const TransitionSystem & ts_msat_; // could be the btor one
  const TransitionSystem & ts_btor_; // could be the btor one
  const smt::UnorderedTermSet & states_;
  const smt::UnorderedTermSet & next_states_;
  const smt::UnorderedTermSet & inputs_;
  
  SyGuSTransBuffer (const TransitionSystem & ts_msat, const TransitionSystem & ts_btor);

  std::string_view GetPrimalVarDef() const{ return primal_var_def_; }
  std::string_view GetPrimeVarDef() const { return prime_var_def_; }
  std::string_view GetInputVarDef() const { return input_var_def_; }

  std::string_view GetStateArgDef() const { return state_arg_def_; }
  std::string_view GetStateArgUse() const { return state_arg_use_; }
  std::string GetFprevDef(const smt::Term & Fprev) const;
  std::string GetFprevUse() const;
  
  std::string_view GetTransDef() const { return trans_def_; } // (define-fun Trans ((...)) () ())
  std::string_view GetTransUse() const { return trans_use_; } // (Trans ... ... ...)
  std::string_view GetInitDef()  const { return init_def_; } // (define-fun Init ((...)) () ())
  std::string_view GetInitUse()  const { return init_use_; } // (Init ... ... ...)

  std::string StateToNext(const std::string & name) const;
}; // class SyGuSTransBuffer
 

// --------------------------------------------


class SyGusQueryGen {

  typedef uint64_t width_t;
public:
  typedef std::vector<Model *> facts_t;
  typedef std::vector<Model *> cexs_t;

  SyGusQueryGen(
    const SyntaxStructureT & syntax,
    const SyGuSTransBuffer & sygus_ts_buf,
    const std::unordered_set<std::string> & keep_vars_name,
    const std::unordered_set<std::string> & remove_vars_name
  );
  
  void GenToFile(
    const smt::Term & prevF,
    const facts_t & facts_all, // internal filters
    const cexs_t  & cex_to_block,
    const smt::Term & prop_to_imply,
    bool assert_in_prevF,
    std::ostream &fout,
    const std::string & additional_info);

protected:
  // -- get on demand
  // smt::Term prev_;
  // const facts_t & facts_;
  // const cexs_t  & cexs_;
  const SyntaxStructureT & syntax_;
  const SyGuSTransBuffer & sygus_ts_buf_;
  std::unordered_map<uint64_t, std::unordered_set<std::string>> 
    new_variable_set_;

  std::string inv_def_var_list;
  std::string inv_use_var_list;
  std::string inv_use;
  std::string inv_use_next;

  std::vector<std::string> ordered_vars;
  std::vector<std::string> ordered_vars_next;
  std::unordered_set<std::string> vars_kept;

  // generate the synth-fun part
  // use : new_variable_set_, syntax_, inv_def_var_list
  // create : syntax_constraints
  std::string syntax_constraints;
  void generate_syntax_cnstr_string();
  // output : reachable_width
  std::unordered_set<width_t> reachable_width;
  void remove_unused_width();
  
  bool contains_extra_var(Model * m) const;
  // no need for contains fewer var because
  // we can iterate through the vars

  bool dump_cex_block(
    const cexs_t  & cex_to_block, 
    const SyGuSTransBuffer & sygus_ts_buf,
    std::ostream & os);
  
  bool dump_fact_allow(
    const facts_t  & facts_all, 
    const SyGuSTransBuffer & sygus_ts_buf,
    std::ostream & os);
  
  void dump_inv_imply_prop(
    const smt::Term & prop, 
    const SyGuSTransBuffer & sygus_ts_buf,
    std::ostream & os) ;

};  // class SyGusQueryGen
 
 
} // namespace sygus
 
} // namespace cosa
