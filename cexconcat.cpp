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
using namespace pono;
using namespace smt;
using namespace std;

std::vector<std::string> assumption_wire_name = {
"start_condition__p71__",
"start_condition__p69__",
"start_condition__p70__",
"input_map_assume___p0__",
"noreset__p1__",
"post_value_holder__p2__",
"post_value_holder__p3__",
"post_value_holder__p4__",
"post_value_holder__p5__",
"post_value_holder__p6__",
"post_value_holder__p7__",
"post_value_holder__p8__",
"post_value_holder__p9__",
"post_value_holder__p10__",
"post_value_holder__p11__",
"post_value_holder__p12__",
"post_value_holder__p13__",
"post_value_holder__p14__",
"post_value_holder__p15__",
"post_value_holder__p16__",
"post_value_holder__p17__",
"post_value_holder__p18__",
"post_value_holder__p19__",
"post_value_holder__p20__",
"post_value_holder__p21__",
"post_value_holder__p22__",
"post_value_holder__p23__",
"post_value_holder__p24__",
"post_value_holder__p25__",
"post_value_holder__p26__",
"post_value_holder__p27__",
"post_value_holder__p28__",
"post_value_holder__p29__",
"post_value_holder__p30__",
"post_value_holder__p31__",
"post_value_holder__p32__",
"post_value_holder__p33__",
"post_value_holder__p34__",
"post_value_holder__p35__",
"post_value_holder__p36__",
"post_value_holder__p37__",
"post_value_holder__p38__",
"post_value_holder__p39__",
"post_value_holder__p40__",
"post_value_holder__p41__",
"post_value_holder__p42__",
"post_value_holder__p43__",
"post_value_holder__p44__",
"post_value_holder__p45__",
"post_value_holder__p46__",
"post_value_holder__p47__",
"post_value_holder__p48__",
"post_value_holder__p49__",
"post_value_holder__p50__",
"post_value_holder__p51__",
"post_value_holder__p52__",
"post_value_holder__p53__",
"post_value_holder__p54__",
"post_value_holder__p55__",
"post_value_holder__p56__",
"post_value_holder__p57__",
"post_value_holder__p58__",
"post_value_holder__p59__",
"post_value_holder__p60__",
"post_value_holder__p61__",
"post_value_holder__p62__",
"post_value_holder__p63__",
"post_value_holder__p64__",
"post_value_holder__p65__",
"post_value_holder__p66__",
"post_value_holder__p67__",
"post_value_holder__p68__",
"variable_map_assume___p72__",
"variable_map_assume___p73__",
"variable_map_assume___p74__",
"variable_map_assume___p75__",
"variable_map_assume___p76__",
"variable_map_assume___p77__",
"variable_map_assume___p78__",
"variable_map_assume___p79__",
"variable_map_assume___p80__",
"variable_map_assume___p81__",
"variable_map_assume___p82__",
"variable_map_assume___p83__",
"variable_map_assume___p84__",
"variable_map_assume___p85__",
"variable_map_assume___p86__",
"variable_map_assume___p87__",
"variable_map_assume___p88__",
"variable_map_assume___p89__",
"variable_map_assume___p90__",
"variable_map_assume___p91__",
"variable_map_assume___p92__",
"variable_map_assume___p93__",
"variable_map_assume___p94__",
"variable_map_assume___p95__",
"variable_map_assume___p96__",
"variable_map_assume___p97__",
"variable_map_assume___p98__",
"variable_map_assume___p99__",
"variable_map_assume___p100__",
"variable_map_assume___p101__",
"variable_map_assume___p102__",
"variable_map_assume___p103__",
"variable_map_assume___p104__",
};

ProverResult check_prop(PonoOptions pono_options,
                        Term & prop,
                        TransitionSystem & ts,
                        const SmtSolver & s,
                        std::vector<UnorderedTermMap> & cex,
                        const Term & original_trans)
{
  Unroller unroller_(ts);
  int bound = 20;

  std::vector<std::tuple<int, Term, Term>> coi_info;
  { // load variable assignment
    std::ifstream fin("coi-check-rev.txt");
    if (fin.is_open()) { 
      { int n; std::string x; fin>>n>>x; assert(n==0 && x=="="); }
      int offset; fin >> offset; // read `0 = 5`
      int idx; std::string name; std::string val;
      while((fin>>idx)) {
        fin>>name; fin>>val;
        idx += offset;
        Term var_term = ts.lookup(name);
        auto sort = var_term->get_sort();
        assert(val.substr(0,2) == "#b" && val.length() > 2);
        Term val_term = ts.make_term(val.substr(2), sort, 2);
        coi_info.push_back({idx, var_term, val_term});
      }
    } else
      throw PonoException("Need `coi-check-rev.txt`");
    cout << "Loaded " << coi_info.size() << " assignments" << endl;
  }

  s->assert_formula(unroller_.at_time(ts.init(), 0));
  for (int j = 0; j < bound; j ++) {
    s->assert_formula(unroller_.at_time(ts.trans(), j));
  }
  assert(s->check_sat().is_sat());

  // now let's check COI
  s->push();
  bool is_sat = true;
  for (const auto & idx_var_val : coi_info) {
    auto idx = std::get<0>(idx_var_val);
    const auto & var = std::get<1>(idx_var_val);
    const auto & val = std::get<2>(idx_var_val);
    s->assert_formula(ts.make_term(Equal, unroller_.at_time(var, idx), val));
    cout << "@" << idx << " " << var->to_string() << " := " << val->to_string() << endl;
    if(s->check_sat().is_unsat()) {
      cout << "becomes UNSAT!" << endl;
      is_sat = false;
      break;
    }
  }

  bool stop = false;
  for (int idx = 5; idx <= 10; idx ++) {
    for (const auto & wire_name : assumption_wire_name) {
      auto a = ts.lookup(wire_name);
      s->assert_formula(unroller_.at_time(a, idx));
      cout << "Asmpt @ " << idx << " "<< wire_name << endl;
      if(s->check_sat().is_unsat()) {
        cout << "becomes UNSAT!" << endl;
        stop = true;
        break;
      }
    }
    if (stop)
      break;
  }

  s->pop();
  return ProverResult::TRUE;
  // just unroll 
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


int main(int argc, char ** argv)
{

  PonoOptions pono_options;
  ProverResult res = pono_options.parse_and_set_options(argc, argv);
  if (pono_options.vcd_name_.empty())
    pono_options.vcd_name_ = "cex.vcd";
  // in this case, we are only interested in the first state
  pono_options.witness_ = true;
  pono_options.witness_first_state_only_ = false;
  pono_options.compute_dynamic_coi_upon_cex_ = true;
  pono_options.dynamic_coi_check_ = true;
  { // dynamically check if asmpt-ila.smt2 is available or not
    std::ifstream fin("asmpt-ila.smt2");
    pono_options.use_ilang_coi_constraint_file_ = fin.is_open();
  }
  pono_options.logging_smt_solver_ = true; // it seems that logging solver helps with COI

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

  // TODO: make this less ugly, just need to keep it in scope if using
  //       it would be better to have a generic encoder
  //       and also only create the transition system once

  logger.log(2, "Parsing BTOR2 file: {}", pono_options.filename_);
  FunctionalTransitionSystem fts(s);
  BTOR2Encoder btor_enc(pono_options.filename_, fts);
  Term prop, original_trans;

  IF_ILA_CHECK_LOAD_ADDITIONAL_ASSUMPTIONS(fts, original_trans); /* This will store the original trans of fts in `original_trans`*/

  // HERE we extra the property
  if(btor_enc.propvec().size() != 1)
    throw PonoException("Expecting only one `bad` in btor2 input");
  prop = btor_enc.propvec().at(0);
  
  // HERE we load the assumptions from environment invariant synthesis
  if(!pono_options.property_file_.empty()) {
    PropertyInterface prop_if (pono_options.property_file_,fts);
    prop_if.AddAssumptionsToTS();
    prop = prop_if.AddAssertions(prop);
  } 

  vector<UnorderedTermMap> cex;
  res = check_prop(pono_options, prop, fts, s, cex, original_trans);
  // we assume that a prover never returns 'ERROR'

  return res;
}
