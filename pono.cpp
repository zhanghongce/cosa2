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
#include "utils/str_util.h"
#include <fstream>
#include <filesystem>
using namespace pono;
using namespace smt;
using namespace std;
namespace fs = std::filesystem;

ProverResult check_prop(PonoOptions pono_options,
                        Term & prop,
                        TransitionSystem & ts,
                        const SmtSolver & s,
                        std::vector<UnorderedTermMap> & cex,
                        Term & original_trans)
{
  // get property name before it is rewritten
  const string prop_name = ts.get_name(prop);
  logger.log(1, "Solving property: {}", prop_name);
  logger.log(3, "INIT:\n{}", ts.init());
  logger.log(3, "TRANS:\n{}", ts.trans());

  // modify the transition system and property based on options
  if (!pono_options.clock_name_.empty()) {
    Term clock_symbol = ts.lookup(pono_options.clock_name_);
    toggle_clock(ts, clock_symbol);
  }
  if (!pono_options.reset_name_.empty()) {
    std::string reset_name = pono_options.reset_name_;
    bool negative_reset = false;
    if (reset_name.at(0) == '~') {
      reset_name = reset_name.substr(1, reset_name.length() - 1);
      negative_reset = true;
    }
    Term reset_symbol = ts.lookup(reset_name);
    if (negative_reset) {
      SortKind sk = reset_symbol->get_sort()->get_sort_kind();
      reset_symbol = (sk == BV) ? s->make_term(BVNot, reset_symbol)
                                : s->make_term(Not, reset_symbol);
    }
    Term reset_done = add_reset_seq(ts, reset_symbol, pono_options.reset_bnd_);
    // guard the property with reset_done
    prop = ts.solver()->make_term(Implies, reset_done, prop);
  }


  if (pono_options.static_coi_) {
    /* Compute the set of state/input variables related to the
       bad-state property. Based on that information, rebuild the
       transition relation of the transition system. */
    StaticConeOfInfluence coi(ts, { prop }, pono_options.verbosity_);
  }

  if (pono_options.pseudo_init_prop_) {
    ts = pseudo_init_and_prop(ts, prop);
  }

  if (pono_options.promote_inputvars_) {
    ts = promote_inputvars(ts);
    assert(!ts.inputvars().size());
  }

  if (!ts.only_curr(prop)) {
    logger.log(1,
               "Got next state or input variables in property. "
               "Generating a monitor state.");
    prop = add_prop_monitor(ts, prop);
  }

  if (pono_options.assume_prop_) {
    // NOTE: crucial that pseudo_init_prop and add_prop_monitor passes are
    // before this pass. Can't assume the non-delayed prop and also
    // delay it
    prop_in_trans(ts, prop);
  }

  Property p(s, prop, prop_name);

  // end modification of the transition system and property

  Engine eng = pono_options.engine_;

  std::shared_ptr<Prover> prover;
  if (pono_options.cegp_abs_vals_) {
    prover = make_cegar_values_prover(eng, p, ts, s, pono_options);
  } else if (pono_options.ceg_bv_arith_) {
    prover = make_cegar_bv_arith_prover(eng, p, ts, s, pono_options);
  } else if (pono_options.ceg_prophecy_arrays_) {
    prover = make_ceg_proph_prover(eng, p, ts, s, pono_options);
  } else {
    prover = make_prover(eng, p, ts, s, pono_options);
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
    bool success = prover->witness(cex);
    if (!success) {
      logger.log(
          0,
          "Only got a partial witness from engine. Not suitable for printing.");
    }
    if(pono_options.dynamic_coi_check_){
      bool res_COI = prover->check_coi(original_trans);
      if(!res_COI) {
          std::vector<smt::UnorderedTermMap> coi_cex;
          prover->coi_failure_witness(coi_cex);
          VCDWitnessPrinter vcdprinter(ts, coi_cex);
          vcdprinter.dump_trace_to_file("COI_failure.vcd");
          // throw PonoException("COI check failed!");
      } else
        logger.log(0, "COI check passed");
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
    bool invar_passes = check_invar(ts, p.prop(), invar);
    std::cout << "Invariant Check " << (invar_passes ? "PASSED" : "FAILED")
              << std::endl;
    if (!invar_passes) {
      // shouldn't return true if invariant is incorrect
      throw PonoException("Invariant Check FAILED");
    }
  }
  return r;
}

int extract_num(const std::string &n) {
  // __auxvar?
  // 012345678
  size_t idx;
  for(idx=8;idx<n.length();++idx) {
    if(!( n.at(idx) >= '0' && n.at(idx)<='9'))
      break;
  }
  return syntax_analysis::StrToULongLong( n.substr(8,idx), 10 );
}

void IF_ILA_CHECK_LOAD_ADDITIONAL_ASSUMPTIONS(FunctionalTransitionSystem & fts, Term & original_trans) {
  auto iend_pos = fts.named_terms().find("__IEND__");
  bool find_iend = iend_pos != fts.named_terms().end();
  original_trans = fts.trans();
  
  if(!find_iend)
    return;

  auto iend_term = iend_pos->second;
  const static std::string aux_var_ends_type1 = "__recorder_sn_cond";
  const static std::string aux_var_ends_type2 = "__recorder_sn_condmet";
  unordered_map<int, vector<Term>> sn_cond_condmet_pair;

  auto & slv = fts.get_solver();
  // HZ note: replacing back to true seems to be not okay?
  // auto term_true = slv->make_term(true);
  // { // replace existing constraints to true in fts.trans
  //   UnorderedTermMap subst;
  //   for(const auto & c_next_pair : fts.constraints()) {
  //     subst.emplace(c_next_pair.first, term_true);
  //     // if (c_next_pair.second)
  //     //  subst.emplace(fts.next(c_next_pair.first), term_true);
  //   }
  //   original_trans = slv->AbsSmtSolver::substitute(original_trans, subst);
  // }


  for (const auto & n_term_pair : fts.named_terms()) {
    const auto & n = n_term_pair.first;
    if(n.find("__auxvar") == 0 && n.length() >= aux_var_ends_type1.length() && 
        n.compare(n.length() - aux_var_ends_type1.length(), aux_var_ends_type1.length(), aux_var_ends_type1) == 0) {
      auto auxvarnum =  extract_num(n);
      sn_cond_condmet_pair[auxvarnum].push_back(n_term_pair.second);
    }
    else if(n.find("__auxvar") == 0 && n.length() >= aux_var_ends_type2.length() && 
        n.compare(n.length() - aux_var_ends_type2.length(), aux_var_ends_type2.length(), aux_var_ends_type2) == 0) {
      auto auxvarnum =  extract_num(n);
      sn_cond_condmet_pair[auxvarnum].push_back(n_term_pair.second);
    }
  }
  if (sn_cond_condmet_pair.empty())
    return;

  Term consq;
  for (const auto & idx_termvec_pair : sn_cond_condmet_pair) {
    const auto & termv = idx_termvec_pair.second;
    assert(termv.size() == 2);
    auto consq_sub = slv->make_term(Or, termv.at(0), termv.at(1));

    if(consq == nullptr)
      consq = consq_sub;
    else
      consq = slv->make_term(And, consq, consq_sub);
  }
  Term assumption =  slv->make_term(Implies,  iend_term, consq);
  // this is adding `IEND => ( __auxvarXXX__recorder_sn_cond || __auxvarXXX__recorder_sn_condmet)`
  logger.log(0, "ILA wrapper detected!");
  // logger.log(3,"Add assumption to ila fts: {}", assumption->to_string());

  fts.add_constraint(assumption);
}


// Note: signal handlers are registered only when profiling is enabled.
void profiling_sig_handler(int sig)
{
  std::string signame;
  switch (sig) {
    case SIGINT: signame = "SIGINT"; break;
    case SIGTERM: signame = "SIGTERM"; break;
    case SIGALRM: signame = "SIGALRM"; break;
    default:
      throw PonoException(
          "Caught unexpected signal"
          "in profiling signal handler.");
  }
  logger.log(0, "\n Signal {} received\n", signame);
#ifdef WITH_PROFILING
  ProfilerFlush();
  ProfilerStop();
#endif
  // Switch back to default handling for signal 'sig' and raise it.
  signal(sig, SIG_DFL);
  raise(sig);
}


ProverResult check_prop_inv(PonoOptions pono_options,
                        Term & prop,
                        TransitionSystem & ts,
                        const SmtSolver & s,
                        std::vector<UnorderedTermMap> & cex,
                        int step)
{
  // get property name before it is rewritten
  const string prop_name = ts.get_name(prop);
  logger.log(1, "Solving property: {}", prop_name);
  logger.log(3, "INIT:\n{}", ts.init());
  logger.log(3, "TRANS:\n{}", ts.trans());

  // modify the transition system and property based on options
  if (!pono_options.clock_name_.empty()) {
    Term clock_symbol = ts.lookup(pono_options.clock_name_);
    toggle_clock(ts, clock_symbol);
  }
  if (!pono_options.reset_name_.empty()) {
    std::string reset_name = pono_options.reset_name_;
    bool negative_reset = false;
    if (reset_name.at(0) == '~') {
      reset_name = reset_name.substr(1, reset_name.length() - 1);
      negative_reset = true;
    }
    Term reset_symbol = ts.lookup(reset_name);
    if (negative_reset) {
      SortKind sk = reset_symbol->get_sort()->get_sort_kind();
      reset_symbol = (sk == BV) ? s->make_term(BVNot, reset_symbol)
                                : s->make_term(Not, reset_symbol);
    }
    Term reset_done = add_reset_seq(ts, reset_symbol, pono_options.reset_bnd_);
    // guard the property with reset_done
    prop = ts.solver()->make_term(Implies, reset_done, prop);
  }


  if (pono_options.static_coi_) {
    /* Compute the set of state/input variables related to the
       bad-state property. Based on that information, rebuild the
       transition relation of the transition system. */
    StaticConeOfInfluence coi(ts, { prop }, pono_options.verbosity_);
  }

  if (pono_options.pseudo_init_prop_) {
    ts = pseudo_init_and_prop(ts, prop);
  }

  if (pono_options.promote_inputvars_) {
    ts = promote_inputvars(ts);
    assert(!ts.inputvars().size());
  }

  if (!ts.only_curr(prop)) {
    logger.log(1,
               "Got next state or input variables in property. "
               "Generating a monitor state.");
    prop = add_prop_monitor(ts, prop);
  }

  if (pono_options.assume_prop_) {
    // NOTE: crucial that pseudo_init_prop and add_prop_monitor passes are
    // before this pass. Can't assume the non-delayed prop and also
    // delay it
    prop_in_trans(ts, prop);
  }

  Property p(s, prop, prop_name);

  // end modification of the transition system and property

  Engine eng = pono_options.engine_;

  std::shared_ptr<Prover> prover;
  if (pono_options.cegp_abs_vals_) {
    prover = make_cegar_values_prover(eng, p, ts, s, pono_options);
  } else if (pono_options.ceg_bv_arith_) {
    prover = make_cegar_bv_arith_prover(eng, p, ts, s, pono_options);
  } else if (pono_options.ceg_prophecy_arrays_) {
    prover = make_ceg_proph_prover(eng, p, ts, s, pono_options);
  } else {
    prover = make_prover(eng, p, ts, s, pono_options);
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
    bool success = prover->witness(cex);
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
  auto cvc5solver = smt::Cvc5SolverFactory::create(false);
  auto transferer = smt::TermTranslator(cvc5solver);
  auto invar_in_cvc5 = transferer.transfer_term(invar);

  smt::UnorderedTermSet varset;
  varset = get_free_symbols(invar_in_cvc5);
  auto invar_varname_rewritten = name_changed(invar_in_cvc5, varset, cvc5solver, "RTL.");
  auto varset_new = get_free_symbols(invar_varname_rewritten);

    // smt::UnorderedTermSet out;
    // Term new_Term;
    // std::string var_wrapper;
    // std::string sort_list = "";
    // smt::SmtSolver solver  = BoolectorSolverFactory::create(true);
    //  solver->set_logic("BV");
    //  solver->set_opt("incremental", "false");
    //  solver->set_opt("produce-models", "false");
    // name_changed(invar, new_Term,solver);
    // out = get_free_symbols(new_Term);
    std::string sort_list;
    smt_lib2_front(varset_new, sort_list);
    std::string folderPath = "/data/zhiyuany/cosa2/inductive_invariant/";
    // fs::path folderPath_p = folderPath;
    if (fs::is_directory(folderPath)==false)	
	    {
          bool a = fs::create_directory(folderPath);
	    }

    std::string filename = folderPath + "/" + "inv1" +".smt2";
    
    ofstream res(filename.c_str());
    res<<"("<<"define-fun"<<" "<<"assumption.0"<<" "<<"("<<sort_list<<")"<<" "<<"Bool"<<" "<<invar_varname_rewritten->to_string()<<")"<<endl;
    

  if (r == TRUE && pono_options.show_invar_ && invar) {
    logger.log(0, "INVAR: {}", invar_in_cvc5);
  }

  if (r == TRUE && pono_options.check_invar_ && invar) {
    bool invar_passes = check_invar(ts, p.prop(), invar);
    std::cout << "Invariant Check " << (invar_passes ? "PASSED" : "FAILED")
              << std::endl;
    if (!invar_passes) {
      // shouldn't return true if invariant is incorrect
      throw PonoException("Invariant Check FAILED");
    }
  }
  return r;
}




int main(int argc, char ** argv)
{
  auto begin_time_stamp = timestamp();

  PonoOptions pono_options;
  ProverResult res = pono_options.parse_and_set_options(argc, argv);
  if (res == ERROR) return res;
  // expected result returned by option parsing and setting is
  // 'pono::UNKNOWN', indicating that options were correctly set and
  // 'ERROR' otherwise, e.g. wrong command line options or
  // incompatible options were passed
  assert(res == pono::UNKNOWN);
  std::ifstream fin("/data/zhiyuany/cosa2/asmpt-ila.smt2");
  if(fin.is_open())
    pono_options.use_ilang_coi_constraint_file_ = true;
  // set logger verbosity -- can only be set once
  logger.set_verbosity(pono_options.verbosity_);

  // For profiling: set signal handlers for common signals to abort
  // program.  This is necessary to gracefully stop profiling when,
  // e.g., an external time limit is enforced to stop the program.
  if (!pono_options.profiling_log_filename_.empty()) {
    signal(SIGINT, profiling_sig_handler);
    signal(SIGTERM, profiling_sig_handler);
    signal(SIGALRM, profiling_sig_handler);
#ifdef WITH_PROFILING
    logger.log(
        0, "Profiling log filename: {}", pono_options.profiling_log_filename_);
    ProfilerStart(pono_options.profiling_log_filename_.c_str());
#endif
  }

#ifdef NDEBUG
  try {
#endif
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
    if (pono_options.engine_ == IC3SA_ENGINE) {
      // IC3SA expects all state variables
      pono_options.promote_inputvars_ = true;
    }

    // TODO: make this less ugly, just need to keep it in scope if using
    //       it would be better to have a generic encoder
    //       and also only create the transition system once
    string file_ext = pono_options.filename_.substr(
        pono_options.filename_.find_last_of(".") + 1);
    if (file_ext == "btor2" || file_ext == "btor") {
      logger.log(2, "Parsing BTOR2 file: {}", pono_options.filename_);
      FunctionalTransitionSystem fts(s);
      BTOR2Encoder btor_enc(pono_options.filename_, fts);
    //  auto name_terms = fts.named_terms();
    //  auto sqed = name_terms.find("RTL.sqed");
    //  if(sqed==name_terms.end())
    //   std::cout<< "Not find. "<<std::endl;
    //  else
    //   std::cout<< sqed->first << " is "<< sqed->second <<std::endl;

    Term prop;
    if (pono_options.find_environment_invariant_){
      assert(!pono_options.cex_reader_.empty());
      int step = 0;
      res = TRUE;


      PropertyInterfacecex prop_cex(pono_options, std::string("RTL"), true , fts);
      prop = prop_cex.cex_parse_to_pono_property();
      std::cout << prop->to_raw_string() << std::endl;
      vector<UnorderedTermMap> cex;
      res = check_prop_inv(pono_options, prop, fts, s, cex, step);
      step = step + 1;
      // we assume that a prover never returns 'ERROR'
      assert(res != ERROR);

      // print btor output
      if (res == FALSE) {
        cout << "sat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        assert(pono_options.witness_ || !cex.size());
        if (cex.size()) {
          print_witness_btor(btor_enc, cex, fts);
          if (!pono_options.vcd_name_.empty()) {
            VCDWitnessPrinter vcdprinter(fts, cex);
            vcdprinter.dump_trace_to_file(pono_options.vcd_name_);
          }
        }

      } else if (res == TRUE) {
        cout << "unsat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
      } else {
        assert(res == pono::UNKNOWN);
        cout << "unknown" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
    }
    }
    else{
    if ((pono_options.cex_reader_.empty())&(pono_options.property_file_.empty())){
        const TermVec & propvec = btor_enc.propvec();
        unsigned int num_props = propvec.size();
        /// YZY: I am not sure whether we need to comment the following code

        if (pono_options.prop_idx_ >= num_props) {
          throw PonoException(
              "Property index " + to_string(pono_options.prop_idx_)
              + " is greater than the number of properties in file "
              + pono_options.filename_ + " (" + to_string(num_props) + ")");
        }
    
        prop = propvec[pono_options.prop_idx_];
    }
      if(!pono_options.property_file_.empty()) {
        const TermVec & propvec = btor_enc.propvec();
        unsigned int num_props = propvec.size();
        if (num_props!=0)
          prop = propvec[pono_options.prop_idx_];
        PropertyInterface prop_if (pono_options.property_file_,fts);
        prop_if.AddAssumptionsToTS();
        prop = prop_if.AddAssertions(prop);
      }
      //////TODO: Add the transformation of the vcd at here!!!!//////////
      if(!pono_options.cex_reader_.empty()){
        PropertyInterfacecex prop_cex(pono_options, std::string("RTL"), true,fts);
        prop = prop_cex.cex_parse_to_pono_property();
        std::cout << prop->to_raw_string() << std::endl;
      }
      Term original_trans;
      vector<UnorderedTermMap> cex;
      IF_ILA_CHECK_LOAD_ADDITIONAL_ASSUMPTIONS(fts, original_trans);
      res = check_prop(pono_options, prop, fts, s, cex,original_trans);
      // we assume that a prover never returns 'ERROR'
      assert(res != ERROR);
      
      std::string filename = "/data/zhiyuany/cosa2/result_1.txt";
      // print btor output
      if (res == FALSE) {
        cout << "sat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        assert(pono_options.witness_ || !cex.size());
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect<<"step: "<<  pono_options.step_ << "sat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<<"step: "<<  pono_options.step_ << "sat" <<endl;
        }
        if (cex.size()) {
          // auto new_solver = create_solver_for(BTOR, pono_options.engine_, true,false);
          // TermTranslator to_new_solver(new_solver);
          // // TermTranslator to_old_solver(solver_);
          // FunctionalTransitionSystem new_fts(fts,to_new_solver);
          // // BTOR2Encoder btor_enc(pono_options.filename_, new_fts);
          // vector<UnorderedTermMap> btor_cex;
          // for (const auto & frame: cex) {
          //   btor_cex.push_back(UnorderedTermMap());
          //   for(const auto & var_val : frame) {
          //     btor_cex.back().emplace(to_new_solver.transfer_term(var_val.first, false), 
          //                       var_val.second);
          //   }
          // }
          print_witness_btor(btor_enc, cex, fts);
          if (!pono_options.vcd_name_.empty()) {
            VCDWitnessPrinter vcdprinter(fts, cex);
            vcdprinter.dump_trace_to_file(pono_options.vcd_name_);
          }
          // print_witness_btor(btor_enc, cex, fts);
          // cex.clear();
        }

      } else if (res == TRUE) {
        cout << "unsat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect<<"step: "<<  pono_options.step_ << "unsat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<<"step: "<<  pono_options.step_ << "unsat" <<endl;
        }
      } else {
        assert(res == pono::UNKNOWN);
        cout << "unknown" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
      }
    }
    } else if (file_ext == "smv" || file_ext == "vmt" || file_ext == "smt2") {
      logger.log(2, "Parsing SMV/VMT file: {}", pono_options.filename_);
      RelationalTransitionSystem rts(s);
      TermVec propvec;
      if (file_ext == "smv") {
        SMVEncoder smv_enc(pono_options.filename_, rts);
        propvec = smv_enc.propvec();
      } else {
        assert(file_ext == "vmt" || file_ext == "smt2");
        VMTEncoder vmt_enc(pono_options.filename_, rts);
        propvec = vmt_enc.propvec();
      }
      unsigned int num_props = propvec.size();
      if (pono_options.prop_idx_ >= num_props) {
        throw PonoException(
            "Property index " + to_string(pono_options.prop_idx_)
            + " is greater than the number of properties in file "
            + pono_options.filename_ + " (" + to_string(num_props) + ")");
      }

      Term prop = propvec[pono_options.prop_idx_];
      // get property name before it is rewritten
      Term original_trans;
      std::vector<UnorderedTermMap> cex;
      res = check_prop(pono_options, prop, rts, s, cex, original_trans);
      // we assume that a prover never returns 'ERROR'
      assert(res != ERROR);
      std::string filename = "/data/zhiyuany/cosa2/result_sat.txt";
      logger.log(
          0, "Property {} is {}", pono_options.prop_idx_, to_string(res));

      if (res == FALSE) {
        cout << "sat" << endl;
        assert(pono_options.witness_ || cex.size() == 0);
        for (size_t t = 0; t < cex.size(); t++) {
          cout << "AT TIME " << t << endl;
          for (auto elem : cex[t]) {
            cout << "\t" << elem.first << " : " << elem.second << endl;
          }
        }
        assert(pono_options.witness_ || pono_options.vcd_name_.empty());
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect<< "sat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<<"sat" <<endl;
        }
        if (!pono_options.vcd_name_.empty()) {
          VCDWitnessPrinter vcdprinter(rts, cex);
          vcdprinter.dump_trace_to_file(pono_options.vcd_name_);
        }
      } else if (res == TRUE) {
        cout << "unsat" << endl;
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect << "unsat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<< "unsat" <<endl;
        }
      } else {
        assert(res == pono::UNKNOWN);
        cout << "unknown" << endl;
      }
    } else {
      throw PonoException("Unrecognized file extension " + file_ext
                          + " for file " + pono_options.filename_);
    }
#ifdef NDEBUG
  }
  catch (PonoException & ce) {
    cout << ce.what() << endl;
    cout << "error" << endl;
    cout << "b" << pono_options.prop_idx_ << endl;
    res = ProverResult::ERROR;
  }
  catch (SmtException & se) {
    cout << se.what() << endl;
    cout << "error" << endl;
    cout << "b" << pono_options.prop_idx_ << endl;
    res = ProverResult::ERROR;
  }
  catch (std::exception & e) {
    cout << "Caught generic exception..." << endl;
    cout << e.what() << endl;
    cout << "error" << endl;
    cout << "b" << pono_options.prop_idx_ << endl;
    res = ProverResult::ERROR;
  }
#endif

  if (!pono_options.profiling_log_filename_.empty()) {
#ifdef WITH_PROFILING
    ProfilerFlush();
    ProfilerStop();
#endif
  }

  if (pono_options.print_wall_time_) {
    auto end_time_stamp = timestamp();
    auto elapsed_time = timestamp_diff(begin_time_stamp, end_time_stamp);
    std:cout << "Pono wall clock time (s): " <<
      time_duration_to_sec_string(elapsed_time) << std::endl;
  }

  return res;
}