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
#include <fstream>
using namespace pono;
using namespace smt;
using namespace std;

ProverResult check_prop(PonoOptions pono_options,
                        const Term & prop_old,
                        const TransitionSystem & original_ts,
                        const SmtSolver & solver_old,
                        std::vector<UnorderedTermMap> & cex,
                        SolverEnum se,
                        Engine e)
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
    try {
      invar = prover->invar();
    }
    catch (PonoException & e) {
      std::cout << "Engine " << pono_options.engine_
                << " does not support getting the invariant." << std::endl;
    }
  }
    

  if (r == TRUE && pono_options.show_invar_ && invar) {
    logger.log(0, "INVAR: {}", invar);
  }

  if (r == TRUE && pono_options.check_invar_ && invar) {
    bool invar_passes = check_invar(new_fts, p.prop(), invar);
    std::cout << "Invariant Check " << (invar_passes ? "PASSED" : "FAILED")
              << std::endl;
    if (!invar_passes) {
      // shouldn't return true if invariant is incorrect
      throw PonoException("Invariant Check FAILED");
    }
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

/*

    auto pos1 = vars.find(var_name);

    auto pos2 = ts_.named_terms().find(var_name);
    assert(pos2 != ts_.named_terms().end());
    auto var = pos2->second;
    auto pos3 = terms.find(var);

    std::string varname_from_smt2 = var->to_raw_string();
    if(varname_from_smt2.length() > 2 && varname_from_smt2.front() == '|' 
      && varname_from_smt2.back() == '|' )
      varname_from_smt2 = varname_from_smt2.substr(1, varname_from_smt2.length() -2 );
    auto pos4 = vars.find(varname_from_smt2);

    bool in_vars  = pos1 != vars.end() || pos4 != vars.end();
    bool in_terms = pos3 != terms.end();
    if (must_in && !in_vars && !in_terms)
      continue;
    if (!must_in && (in_vars || in_terms))
      continue;
*/

class Filter {
public:
  virtual bool operator()(const std::string & n) const = 0;
  virtual std::string to_string() const = 0;
  virtual ~Filter() {}
};

class MaxWidthFilter : public Filter {
protected:
  unsigned width_;
  const TransitionSystem & ts_;
public:
  MaxWidthFilter(unsigned w, const TransitionSystem & ts) : width_(w), ts_(ts) { }
  bool operator()(const std::string & n) const override {
    auto pos = ts_.named_terms().find(n);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    if ( var->get_sort()->get_sort_kind() != SortKind::BV )
      return true;
    if (var->get_sort()->get_width() <= width_ )
      return true;
    return false;
  }
  std::string to_string() const override {
    return "[W<" + std::to_string(width_) +"]";
  }
};

class NameFilter : public Filter{
protected:
  unordered_set<string> varset;
  const TransitionSystem & ts_;
  bool must_in_;
public:
  NameFilter(const vector<string> & v, const TransitionSystem & ts, bool must_in) : ts_(ts), must_in_(must_in)
     { varset.insert(v.begin(), v.end()); }
  bool operator()(const std::string & n) const {
    auto pos1 = varset.find(n);
    auto pos2 = ts_.named_terms().find(n);
    assert(pos2 != ts_.named_terms().end());
    auto var = pos2->second;

    std::string varname_from_smt2 = var->to_raw_string();
    if(varname_from_smt2.length() > 2 && varname_from_smt2.front() == '|' 
      && varname_from_smt2.back() == '|' )
      varname_from_smt2 = varname_from_smt2.substr(1, varname_from_smt2.length() -2 );
    auto pos3 = varset.find(varname_from_smt2);

    bool in_vars  = pos1 != varset.end() || pos3 != varset.end();
    if(must_in_ && !in_vars)
      return false;
    if (!must_in_ && in_vars)
      return false;
    return true;
  }
  std::string to_string() const override {
    if(must_in_)
      return "[Keep " + std::to_string(varset.size()) +" V]";
    return "[rm " + std::to_string(varset.size()) +"V]";
  }
};

struct FilterConcat : public Filter{
  list<shared_ptr<Filter>> filters;
  bool operator()(const std::string & n) const override {
    for (const auto & f : filters) {
      if (!(*f)(n))
        return false;
    }
    return true;
  }
  std::string to_string() const override {
    std::string ret;
    for (const auto & f : filters) 
      ret += f->to_string();
    return ret;
  }
};

int main(int argc, char ** argv)
{
  auto begin_time_stamp = timestamp();

  PonoOptions pono_options;
  ProverResult res = pono_options.parse_and_set_options(argc, argv);
  pono_options.engine_ = IC3_BITS;
  pono_options.show_invar_ = true;
  pono_options.check_invar_ = false;

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
                                  false,
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
  CexInfoForEnvInvSyn cexinfo("invsyn-config.json");
  logger.log(0, "Datapath reg: {} , aux var removal: {}", cexinfo.datapath_elements_.size(), cexinfo.auxvar_removal_.size());
  
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
    cexinfo.module_name_filter_,
    cexinfo.module_name_removal_,
    fts);
  
  FilterConcat filter;
  unsigned max_width = 32;
  filter.filters.push_back(std::make_shared<NameFilter>(cexinfo.auxvar_removal_, fts, false));
  filter.filters.push_back(std::make_shared<NameFilter>(cexinfo.datapath_elements_, fts, false));
  filter.filters.push_back(std::make_shared<MaxWidthFilter>(max_width, fts));
  prop = cexreader.cex2property(filter);
  bool inductiveness;
  while( (inductiveness = check_for_inductiveness(prop, fts)) == true && max_width > 1 ) {
    max_width /= 2;
    filter.filters.push_back(std::make_shared<MaxWidthFilter>(max_width, fts));
    prop = cexreader.cex2property(filter);
    cout << "Reducing w: " << max_width << " F:" << filter.to_string() << endl;
  }

  if (inductiveness) {
    std::vector<std::string> varset;
    cexreader.get_remaining_var(filter, varset);
    std::sort(varset.begin(), varset.end());
    do {
      auto newsize = varset.size() / 2;
      varset.resize(newsize);
      filter.filters.push_back(std::make_shared<NameFilter>(varset, fts, true));
      cout << "Reducing F:" << filter.to_string() << endl;
      prop = cexreader.cex2property(filter);
    }while( /*(inductiveness = check_for_inductiveness(prop, fts)) == true &&*/ varset.size() > 1 );
  }

  cout << "PROPERTY:" << prop->to_string() << endl;

  vector<UnorderedTermMap> cex;
  while (  (res = check_prop(pono_options, prop, fts, s, cex, 
      pono_options.smt_solver_, pono_options.engine_)) == FALSE && !filter.filters.empty()) {
    filter.filters.pop_back();
    cout << "Reachable, removing filter, after: " << filter.to_string() << endl;
    prop = cexreader.cex2property(filter);
    cex.clear();
    cout << "Now work on PROPERTY:" << prop->to_string() << endl;
    // TODO: s->reset();
  }

  assert ( filter.filters.empty() || res != FALSE);
  assert ( res != ERROR);

  // print btor output
  if (res == FALSE) {
    cout << "reachable" << endl;
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
  } else {
    assert(res == pono::UNKNOWN);
    cout << "unknown" << endl;
  }

  if (pono_options.print_wall_time_) {
    auto end_time_stamp = timestamp();
    auto elapsed_time = timestamp_diff(begin_time_stamp, end_time_stamp);
    std:cout << "Pono wall clock time (s): " <<
      time_duration_to_sec_string(elapsed_time) << std::endl;
  }

  return res;
}
