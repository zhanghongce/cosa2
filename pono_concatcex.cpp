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
#include "json/json.hpp"
#include <fstream>
#include <filesystem>
#include <queue>
#include "utils/filter.h"

using namespace pono;
using namespace smt;
using namespace std;

ProverResult check_prop(PonoOptions pono_options,
                        Term & prop,
                        TransitionSystem & ts,
                        const SmtSolver & s,
                        std::vector<UnorderedTermMap> & cex)
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


int main(int argc, char ** argv){
  auto begin_time_stamp = timestamp();
  PonoOptions pono_options;
  ProverResult res = pono_options.parse_and_set_options(argc, argv);
  // pono_options.witness_ = true;
  if (res == ERROR) return res;
  // expected result returned by option parsing and setting is
  // 'pono::UNKNOWN', indicating that options were correctly set and
  // 'ERROR' otherwise, e.g. wrong command line options or
  // incompatible options were passed
  assert(res == pono::UNKNOWN);
  SmtSolver s = create_solver_for(pono_options.smt_solver_,
                                    pono_options.engine_,
                                    true,
                                    pono_options.ceg_prophecy_arrays_);
    string file_ext = pono_options.filename_.substr(
        pono_options.filename_.find_last_of(".") + 1);
     Term prop;
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
    //  for(const auto name_term:name_terms){
    //   std::cout<< name_term.first << " is "<< name_term.second <<std::endl;
    //  }
     Term new_init;
     vector<UnorderedTermMap> cex;
     if(!pono_options.cex_reader_.empty()){
        PropertyInterfacecex prop_cex(pono_options, std::string("RTL"), true, fts,true);
        new_init = prop_cex.cex_parse_to_pono_property(true);
        
        auto origin_init = fts.init();  
        auto orgin_init_symbols = get_free_symbols(origin_init);
        auto new_init_symbols = get_free_symbols(new_init);
        // UnorderedTermSet out_predicate;
        // get_predicates(s,origin_init,out_predicate,true,false,false);
        std::cout << origin_init->to_raw_string() << std::endl;
        std::cout << new_init->to_raw_string() << std::endl;
        new_init = fts.make_term(And,new_init,origin_init);
        // for (const auto &origin:orgin_init_symbols){
        //   if(new_init_symbols.find(origin)!=new_init_symbols.end())
        //       continue;
        //   else{
        //     auto sort = origin->get_sort();
        //     auto width = sort->get_width();
        //     std::string value;
        //     for(auto i = 0;i<width;i++){
        //       value.append("0");
        //     }
        //     auto val = fts.make_term(value,sort,2);
        //     auto eq = fts.make_term(Equal,val,origin);
        //     new_init = fts.make_term(And,new_init,eq);
        //   }
        // }
        std::cout << new_init->to_raw_string() << std::endl;
        fts.set_init(new_init);   
      }
        auto propvec = btor_enc.propvec();
        unsigned int num_props = propvec.size();
        if (pono_options.prop_idx_ >= num_props) {
          throw PonoException(
              "Property index " + to_string(pono_options.prop_idx_)
              + " is greater than the number of properties in file "
              + pono_options.filename_ + " (" + to_string(num_props) + ")");
        }
        prop = propvec[pono_options.prop_idx_];
        res = check_prop(pono_options, prop, fts, s, cex);
     assert(res != ERROR);

      // print btor output
      if (res == FALSE) {
        cout << "sat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        assert(pono_options.witness_ || !cex.size());
        // for (size_t t = 0; t < cex.size(); t++) {
        //   cout << "AT TIME " << t << endl;
        //   for (auto elem : cex[t]) {
        //     cout << "\t" << elem.first << " : " << elem.second << endl;
        //   }
        // }
        assert(pono_options.witness_ || pono_options.vcd_name_.empty());
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
  return res;
}