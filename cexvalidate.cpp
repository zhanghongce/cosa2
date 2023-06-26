/*********************                                                        */
/*! \file
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <csignal>
#include <iostream>
#include "assert.h"

#ifdef WITH_PROFILING
#include <gperftools/profiler.h>
#endif

#include "smt-switch/boolector_factory.h"
#ifdef WITH_MSAT
#include "smt-switch/msat_factory.h"
#endif
#include "core/fts.h"
#include "frontends/btor2_encoder.h"
#include "frontends/smv_encoder.h"
#include "frontends/vmt_encoder.h"
#include "frontends/property_if.h"
#include "frontends/cex_info_json.h"
#include "modifiers/control_signals.h"
#include "modifiers/mod_ts_prop.h"
#include "modifiers/prop_monitor.h"
#include "modifiers/static_coi.h"
#include "options/options.h"
#include "printers/btor2_witness_printer.h"
#include "printers/vcd_witness_printer.h"
#include "smt-switch/logging_solver.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/timestamp.h"
#include "utils/make_provers.h"
#include "utils/ts_analysis.h"
#include "utils/term_analysis.h"
#include "json/json.hpp"
#include <fstream>
#include <filesystem>
#include <queue>
#include "utils/filter.h"
using namespace pono;
using namespace smt;
using namespace std;

ProverResult check_for_inductiveness_bmc(PonoOptions pono_options,
                        const Term & prop_old,
                        const TransitionSystem & original_ts,
                        const SmtSolver & solver_old,
                        std::vector<UnorderedTermMap> & cex,
                        SolverEnum se,
                        bool need_cex,
                        BTOR2Encoder btor_enc)
{
  // create a solver for this
  auto new_solver = create_solver_for(BTOR, BMC, true,false);
  // FunctionalTransitionSystem new_fts(new_solver);
  TermTranslator to_new_solver(new_solver);
  TermTranslator to_old_solver(solver_old);
  FunctionalTransitionSystem new_fts(original_ts,to_new_solver);
  std::vector<UnorderedTermMap> local_cex;
  std::string filename_origin = pono_options.smt_path_ + "/" + "inv_origin.smt2";
  // Term prop = new_solver.transfer_term(prop_old);
  Term prop = to_new_solver.transfer_term(prop_old);

  // get property name before it is rewritten
  const string prop_name = new_fts.get_name(prop);
  logger.log(1, "Solving property: {}", prop_name);
  logger.log(3, "INIT:\n{}", new_fts.init());
  logger.log(3, "TRANS:\n{}", new_fts.trans());

  // modify the transition system and property based on options
  if (!pono_options.clock_name_.empty()) {
    Term clock_symbol = new_fts.lookup(pono_options.clock_name_);
    toggle_clock(new_fts, clock_symbol);
  }
  if (!pono_options.reset_name_.empty()) {
    std::string reset_name = pono_options.reset_name_;
    bool negative_reset = false;
    if (reset_name.at(0) == '~') {
      reset_name = reset_name.substr(1, reset_name.length() - 1);
      negative_reset = true;
    }
    Term reset_symbol = new_fts.lookup(reset_name);
    if (negative_reset) {
      SortKind sk = reset_symbol->get_sort()->get_sort_kind();
      reset_symbol = (sk == BV) ? new_solver->make_term(BVNot, reset_symbol)
                                : new_solver->make_term(Not, reset_symbol);
    }
    Term reset_done = add_reset_seq(new_fts, reset_symbol, pono_options.reset_bnd_);
    // guard the property with reset_done
    prop = new_fts.solver()->make_term(Implies, reset_done, prop);
  }


  if (pono_options.static_coi_) {
    /* Compute the set of state/input variables related to the
       bad-state property. Based on that information, rebuild the
       transition relation of the transition system. */
    StaticConeOfInfluence coi(new_fts, { prop }, pono_options.verbosity_);
  }

  if (pono_options.pseudo_init_prop_) {
    new_fts = pseudo_init_and_prop(new_fts, prop);
  }
  // pono_options.promote_inputvars_ = false;
  if (pono_options.promote_inputvars_) {
    new_fts = promote_inputvars(new_fts);
    assert(!new_fts.inputvars().size());
  }

  if (!new_fts.only_curr(prop)) {
    logger.log(1,
               "Got next state or input variables in property. "
               "Generating a monitor state.");
    prop = add_prop_monitor(new_fts, prop);
  }

  if (pono_options.assume_prop_) {
    // NOTE: crucial that pseudo_init_prop and add_prop_monitor passes are
    // before this pass. Can't assume the non-delayed prop and also
    // delay it
    prop_in_trans(new_fts, prop);
  }

  Property p(new_solver, prop, prop_name);

  // end modification of the transition system and property

  Engine eng = BMC;

  std::shared_ptr<Prover> prover;
  if (pono_options.cegp_abs_vals_) {
    prover = make_cegar_values_prover(eng, p, new_fts, new_solver, pono_options);
  } else if (pono_options.ceg_bv_arith_) {
    prover = make_cegar_bv_arith_prover(eng, p, new_fts, new_solver, pono_options);
  } else if (pono_options.ceg_prophecy_arrays_) {
    prover = make_ceg_proph_prover(eng, p, new_fts, new_solver, pono_options);
  } else {
    prover = make_prover(eng, p, new_fts, new_solver, pono_options);
  }
  assert(prover);
//TODO: W
  // TODO: handle this in a more elegant way in the future
  //       consider calling prover for CegProphecyArrays (so that underlying
  //       model checker runs prove unbounded) or possibly, have a command line
  //       flag to pick between the two
  ProverResult r;
  if (pono_options.engine_ == MSAT_IC3IA)
  {
    // HACK MSAT_IC3IA does not support check_until
    r = prover->prove();
  }
  else
  {
    r = prover->check_until(15);
  }
  // if((r == FALSE)&&(need_cex == true)){
  //   bool success = prover->witness(local_cex);
  //   std::cout<< " The bmc check failure"<<std::endl;
  //   print_witness_btor(btor_enc, local_cex, new_fts);
  //   VCDWitnessPrinter vcdprinter(new_fts, local_cex);
  //   vcdprinter.dump_trace_to_file("env_failure.vcd");
  // }
  return r;
}

// bool check_previous(Term prop_filter, UnorderedTermSet prop_check)
// {
//   for (auto prop:prop_check){
//     if(prop->to_string()== prop_filter->to_string())
//       return true;
//   }
//   return false;
// }


void write_inv_to_file(const smt::Term & invar, ostream & outf ,unsigned step, const std::string & varname_prefix) {
    auto cvc5solver = smt::Cvc5SolverFactory::create(true);
    auto transferer = smt::TermTranslator(cvc5solver);
    auto invar_in_cvc5 = transferer.transfer_term(invar);

    smt::UnorderedTermSet varset;
   
    varset = get_free_symbols(invar_in_cvc5);
    auto invar_varname_rewritten = varname_prefix.empty() ?
      invar_in_cvc5 : name_changed(invar_in_cvc5, varset, cvc5solver, varname_prefix);
    auto varset_new = get_free_symbols(invar_varname_rewritten);
    auto varset_origin = get_free_symbols(invar_in_cvc5);
    std::string sort_list,sort_list_origin;
    smt_lib2_front(varset_new, sort_list);
    smt_lib2_front(varset_origin, sort_list_origin);
    std::string step_char = to_string(step);
    outf<<"(define-fun assumption." << step_char << " ("<<sort_list<<") Bool "<<invar_varname_rewritten->to_string()<<")"<<endl;
    // outf_origin<<"(define-fun assumption." << step_char << " ("<<sort_list_origin<<") Bool "<<invar_in_cvc5->to_string()<<")"<<endl;
}

ProverResult check_prop(PonoOptions pono_options,
                        const Term & prop_old,
                        const TransitionSystem & original_ts,
                        const SmtSolver & solver_old,
                        std::vector<UnorderedTermMap> & cex,
                        SolverEnum se,
                        Engine e,
                        unsigned step,
                        const std::string & varname_prefix)
{
  // create a solver for this
  auto new_solver = create_solver_for(se, e, false,false);
  TermTranslator to_new_solver(new_solver);
  TermTranslator to_old_solver(solver_old);
  FunctionalTransitionSystem new_fts(original_ts,to_new_solver);
  std::vector<UnorderedTermMap> local_cex;
  Term prop = to_new_solver.transfer_term(prop_old);

  // get property name before it is rewritten
  const string prop_name = new_fts.get_name(prop);
  logger.log(1, "Solving property: {}", prop_name);
  logger.log(3, "INIT:\n{}", new_fts.init());
  logger.log(3, "TRANS:\n{}", new_fts.trans());

  // modify the transition system and property based on options
  if (!pono_options.clock_name_.empty()) {
    Term clock_symbol = new_fts.lookup(pono_options.clock_name_);
    toggle_clock(new_fts, clock_symbol);
  }
  if (!pono_options.reset_name_.empty()) {
    std::string reset_name = pono_options.reset_name_;
    bool negative_reset = false;
    if (reset_name.at(0) == '~') {
      reset_name = reset_name.substr(1, reset_name.length() - 1);
      negative_reset = true;
    }
    Term reset_symbol = new_fts.lookup(reset_name);
    if (negative_reset) {
      SortKind sk = reset_symbol->get_sort()->get_sort_kind();
      reset_symbol = (sk == BV) ? new_solver->make_term(BVNot, reset_symbol)
                                : new_solver->make_term(Not, reset_symbol);
    }
    Term reset_done = add_reset_seq(new_fts, reset_symbol, pono_options.reset_bnd_);
    // guard the property with reset_done
    prop = new_fts.solver()->make_term(Implies, reset_done, prop);
  }


  if (pono_options.static_coi_) {
    /* Compute the set of state/input variables related to the
       bad-state property. Based on that information, rebuild the
       transition relation of the transition system. */
    StaticConeOfInfluence coi(new_fts, { prop }, pono_options.verbosity_);
  }

  if (pono_options.pseudo_init_prop_) {
    new_fts = pseudo_init_and_prop(new_fts, prop);
  }

  if (pono_options.promote_inputvars_) {
    new_fts = promote_inputvars(new_fts);
    assert(!new_fts.inputvars().size());
  }

  if (!new_fts.only_curr(prop)) {
    logger.log(1,
               "Got next state or input variables in property. "
               "Generating a monitor state.");
    prop = add_prop_monitor(new_fts, prop);
  }

  if (pono_options.assume_prop_) {
    // NOTE: crucial that pseudo_init_prop and add_prop_monitor passes are
    // before this pass. Can't assume the non-delayed prop and also
    // delay it
    prop_in_trans(new_fts, prop);
  }

  Property p(new_solver, prop, prop_name);

  // end modification of the transition system and property

  Engine eng = pono_options.engine_;

  std::shared_ptr<Prover> prover;
  if (pono_options.cegp_abs_vals_) {
    prover = make_cegar_values_prover(eng, p, new_fts, new_solver, pono_options);
  } else if (pono_options.ceg_bv_arith_) {
    prover = make_cegar_bv_arith_prover(eng, p, new_fts, new_solver, pono_options);
  } else if (pono_options.ceg_prophecy_arrays_) {
    prover = make_ceg_proph_prover(eng, p, new_fts, new_solver, pono_options);
  } else {
    prover = make_prover(eng, p, new_fts, new_solver, pono_options);
  }
  assert(prover);

  // TODO: handle this in a more elegant way in the future
  //       consider calling prover for CegProphecyArrays (so that underlying
  //       model checker runs prove unbounded) or possibly, have a command line
  //       flag to pick between the two
  ProverResult r;
  if (pono_options.engine_ == MSAT_IC3IA)
  {
    // HACK MSAT_IC3IA does not support check_until
    r = prover->prove();
  }
  else
  {
    r = prover->check_until(pono_options.bound_);
  }

  if (r == FALSE && pono_options.witness_) {
    bool success = prover->witness(local_cex);
    if (!success) {
      logger.log(
          0,
          "Only got a partial witness from engine. Not suitable for printing.");
    }
  }

  Term invar;
  if (r == TRUE && (pono_options.show_invar_ || pono_options.check_invar_)) {
    std::ofstream outf_origin("envinv_origin.smt2", std::ofstream::out | std::ofstream::app);
    std::ofstream outf("envinv.smt2", std::ofstream::out | std::ofstream::app);
    try {
      invar = prover->invar();

    }
    catch (PonoException & e) {
      std::cout << "Engine " << pono_options.engine_
                << " does not support getting the invariant." << std::endl;
      outf << "(noinvar)" << endl;      
    }


    if (pono_options.check_invar_ && invar) {
      bool invar_passes = check_invar(new_fts, p.prop(), invar);
      std::cout << "Invariant Check " << (invar_passes ? "PASSED" : "FAILED")
                << std::endl;
      if (!invar_passes) {
        // shouldn't return true if invariant is incorrect
        throw PonoException("Invariant Check FAILED");
      }
    }

    if ( invar) {
      write_inv_to_file(invar, outf, step, varname_prefix);
    }

  }
    

  if (r == TRUE && pono_options.show_invar_ && invar) {
    logger.log(0, "INVAR: {}", invar);
  }


  // now translate cex back to original 
  for (const auto & frame: local_cex) {
    cex.push_back(UnorderedTermMap());
    for(const auto & var_val : frame) {
      cex.back().emplace(to_old_solver.transfer_term(var_val.first, false), 
                         to_old_solver.transfer_term(var_val.second, false));
    }
  }

  return r;
}

bool check_for_inductiveness(const Term & prop, const TransitionSystem & ts) {
  return true;
  // below does nothing!
  Term init = ts.init();
  Term trans = ts.trans();
  const auto & s = ts.solver();
  s->push();
    s->assert_formula(init);
    s->assert_formula(s->make_term(Not, prop));
    auto r = s->check_sat();
  s->pop();
  if (r.is_sat())
    return false;
  
  s->push();
    s->assert_formula(prop);
    s->assert_formula(trans);
    s->assert_formula(s->make_term(Not, ts.next(prop)));
    r = s->check_sat();
  s->pop();
  if (r.is_sat())
    return false;

  return true;
}


int main(int argc, char ** argv)
{

  PonoOptions pono_options;
  ProverResult res = pono_options.parse_and_set_options(argc, argv);
  pono_options.engine_ = IC3_BITS;
  pono_options.verbosity_ = 1;
  pono_options.show_invar_ = true;
  pono_options.check_invar_ = true;

  if (res == ERROR) return res;
  // expected result returned by option parsing and setting is
  // 'pono::UNKNOWN', indicating that options were correctly set and
  // 'ERROR' otherwise, e.g. wrong command line options or
  // incompatible options were passed
  assert(res == pono::UNKNOWN);

  // set logger verbosity -- can only be set once
  logger.set_verbosity(pono_options.verbosity_);


    // no logging by default
    // could create an option for logging solvers in the future

    // HACK bool_model_generation for IC3IA breaks CegProphecyArrays
    // longer term fix will use a different solver in CegProphecyArrays,
    // but for now just force full model generation in that case

  SmtSolver s = create_solver_for(pono_options.smt_solver_,
                                  pono_options.engine_,
                                  true,
                                  pono_options.ceg_prophecy_arrays_);

  if (pono_options.logging_smt_solver_) {
    s = make_shared<LoggingSolver>(s);
    // TODO consider setting base-context-1 for BTOR here
    //      to allow resetting assertions
  }

  // limitations with COI
  if (pono_options.static_coi_) {
    if (pono_options.pseudo_init_prop_) {
      // Issue explained here:
      // https://github.com/upscale-project/pono/pull/160 will be resolved
      // once state variables removed by COI are removed from init then should
      // do static-coi BEFORE mod-init-prop
      logger.log(0,
                  "Warning: --mod-init-prop and --static-coi don't work "
                  "well together currently.");
    }
  }
  // default options for IC3SA
  if (pono_options.engine_ == IC3SA_ENGINE || pono_options.engine_ == SYGUS_PDR) {
    // IC3SA expects all state variables
    pono_options.promote_inputvars_ = true;
  }

  // TODO: make this less ugly, just need to keep it in scope if using
  //       it would be better to have a generic encoder
  //       and also only create the transition system once

  logger.log(2, "Parsing BTOR2 file: {}", pono_options.filename_);
  FunctionalTransitionSystem fts(s);
  BTOR2Encoder btor_enc(pono_options.filename_, fts);
  Term prop;
  CexInfoForEnvInvSyn cexinfo("invsyn-config.json", "COI.txt");
  logger.log(0, "Datapath reg: {} , aux var removal: {}, COI in range: {}", 
    cexinfo.datapath_elements_.size(), 
    cexinfo.auxvar_removal_.size(),
    cexinfo.COI_to_consider_.size());
  
  // HERE we load the assumptions from environment invariant synthesis
  if(!pono_options.property_file_.empty()) {
    PropertyInterface prop_if (pono_options.property_file_,fts);
    prop_if.AddAssumptionsToTS();
    logger.log(0, "TODO: currently will not add assertions in separate property file.");
    // prop = prop_if.AddAssertions(prop);
  } 
  if(btor_enc.propvec().size() != 0)
    logger.log(0, "Ignoring existing property in BTOR2.");

  QedCexParser cexreader(
    cexinfo.cex_path_, 
    cexinfo.module_name_filter_,  // will only keep var with this as the prefix
    cexinfo.module_name_removal_, // will remove this prefix
    fts);
  
  FilterConcat filter;
  unsigned max_width = 32;
  filter.filters.push_back(std::make_shared<NameFilter>(cexinfo.auxvar_removal_, fts, false));
  filter.filters.push_back(std::make_shared<SliceFilter>(cexinfo.COI_to_consider_, fts));
  auto COI_filter = filter.filters.back(); // mark this down and we should not remove it, so later we will check this
  // filter.filters.push_back(std::make_shared<NameFilter>(cexinfo.datapath_elements_, fts, false));
  filter.filters.push_back(std::make_shared<MaxWidthFilter>(max_width, fts));

  prop = cexreader.cex2property(filter);
  bool inductiveness;
  while( (inductiveness = check_for_inductiveness(prop, fts)) == true && max_width > 1 ) {
    max_width /= 2;
    filter.filters.push_back(std::make_shared<MaxWidthFilter>(max_width, fts));
    prop = cexreader.cex2property(filter);
    cout << "Reducing w: " << max_width << " F:" << filter.to_string() << endl;
  }

  // if (inductiveness) {
  //   std::vector<std::string> varset;
  //   cexreader.get_remaining_var(filter, varset);
  //   std::sort(varset.begin(), varset.end());
  //   do {
  //     auto newsize = varset.size() / 2;
  //     varset.resize(newsize);
  //     filter.filters.push_back(std::make_shared<NameFilter>(varset, fts, true));
  //     cout << "Reducing F:" << filter.to_string() << endl;
  //     prop = cexreader.cex2property(filter);
  //   }while( (inductiveness = check_for_inductiveness(prop, fts)) == true && varset.size() > 1 );
  // }


  vector<UnorderedTermMap> cex;
  if(pono_options.step_>0){
    vector<UnorderedTermMap> cex;
    AntFilter ant_filter("COI_ant.txt",std::string("RTL."),fts);
    prop = cexreader.cex2property_ant(filter,ant_filter);
    int switch_mode = 0;
    if(prop!=nullptr){
      cout << "PROPERTY:" << prop->to_string()<< ", with open Ant filter." << endl;
      switch_mode = 1;
    }
    else{
      cout << "Ant filter cannot be used in this stage." << endl;
      prop = cexreader.cex2property(filter);
      cout << "PROPERTY:" << prop->to_string() << ", without open Ant filter."<<endl;
      switch_mode = 2;
    }
    ProverResult res_bmc;
    vector<UnorderedTermMap> cex_bmc;
    while((res_bmc = check_for_inductiveness_bmc(pono_options, prop, fts, s, cex_bmc, pono_options.smt_solver_,true,btor_enc)) == false){
      if(switch_mode == 2){
        if (filter.filters.back() == COI_filter)
          throw PonoException("Removing COI filter! Something is wrong here!");
        filter.filters.pop_back();
        cout << "Reachable, removing filter, after: " << filter.to_string() << endl;
        switch_mode = 0;
      }
      if((switch_mode == 1)||((prop = cexreader.cex2property_ant(filter,ant_filter))==nullptr)){
        cout << "Reachable, removing Ant filter" << endl;
        prop = cexreader.cex2property(filter);
        cout << "Now work on PROPERTY:" << prop->to_string() <<", without open Ant filter." << endl;
        switch_mode = 2;
      }
      else{
        prop = cexreader.cex2property_ant(filter,ant_filter);
        cout << "Now work on PROPERTY:" << prop->to_string() <<", with open Ant filter." << endl;
        switch_mode = 1;
      }
      cex_bmc.clear();      
    }
    while (  (res = check_prop(pono_options, prop, fts, s, cex, 
        pono_options.smt_solver_, pono_options.engine_, pono_options.step_, cexinfo.module_name_removal_)) == FALSE 
    && !filter.filters.empty()) {
      if (filter.filters.back() == COI_filter)
        throw PonoException("Removing COI filter! Something is wrong here!");
      if(switch_mode == 2){
        filter.filters.pop_back();
        cout << "Reachable, removing filter, after: " << filter.to_string() << endl;
        switch_mode = 0;
      }
      if((switch_mode == 1)||((prop = cexreader.cex2property_ant(filter,ant_filter))==nullptr)){
        cout << "Reachable, removing Ant filter" << endl;
        prop = cexreader.cex2property(filter);
        cout << "Now work on PROPERTY:" << prop->to_string() <<", without open Ant filter." << endl;
        switch_mode = 2;
      }
      else{
        prop = cexreader.cex2property_ant(filter,ant_filter);
        cout << "Now work on PROPERTY:" << prop->to_string() <<", with open Ant filter." << endl;
        switch_mode = 1;
      }
      cex.clear();
    // TODO: s->reset();
    }
  }
  

  else{
    ProverResult res_bmc;
    vector<UnorderedTermMap> cex_bmc;
    while((res_bmc = check_for_inductiveness_bmc(pono_options, prop, fts, s, cex_bmc, pono_options.smt_solver_,true,btor_enc)) == false){
      if (filter.filters.back() == COI_filter)
        throw PonoException("Removing COI filter! Something is wrong here!");
        filter.filters.pop_back();
        cout << "Reachable, removing filter, after: " << filter.to_string() << endl;
        prop = cexreader.cex2property(filter);
        cout << "Now work on PROPERTY:" << prop->to_string() <<", without open Ant filter." << endl;
      cex_bmc.clear();      
    }
      cout << "PROPERTY:" << prop->to_string() << endl;
      while (  (res = check_prop(pono_options, prop, fts, s, cex, 
          pono_options.smt_solver_, pono_options.engine_, pono_options.step_, cexinfo.module_name_removal_)) == FALSE 
      && !filter.filters.empty()) {
        if (filter.filters.back() == COI_filter)
          throw PonoException("Removing COI filter! Something is wrong here!");
        filter.filters.pop_back();
        cout << "Reachable, removing filter, after: " << filter.to_string() << endl;
        prop = cexreader.cex2property(filter);
        cex.clear();
        cout << "Now work on PROPERTY:" << prop->to_string() << endl;
        // TODO: s->reset();
      }
  }


  assert ( filter.filters.empty() || res != FALSE);
  assert ( res != ERROR);

  std::ofstream resultf("result.txt");
  // print btor output
  if (res == FALSE) {
    cout << "reachable" << endl;
    resultf << "reachable" << endl;
    assert(pono_options.witness_ || !cex.size());
    if (cex.size()) {
      // if we expect only the first state
      // we don't have the input on every cycle
      // access will be out of range, so let's
      // disable it
      if(!pono_options.witness_first_state_only_)
        print_witness_btor(btor_enc, cex, fts);
      if (!pono_options.vcd_name_.empty()) {
        VCDWitnessPrinter vcdprinter(fts, cex);
        vcdprinter.dump_trace_to_file(pono_options.vcd_name_);
      }
    }

  } else if (res == TRUE) {
    cout << "unreachable" << endl;
    resultf << "unreachable" << endl;
  } else {
    assert(res == pono::UNKNOWN);
    cout << "unknown" << endl;
    resultf << "unknown" << endl;
  }

  return res;
}
