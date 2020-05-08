/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann, Ahmed Irfan
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief 
 **
 ** 
 **/


#include <iostream>
#include "assert.h"

#include "optionparser.h"
#include "smt-switch/boolector_factory.h"
#ifdef WITH_MSAT
  #include "smt-switch/msat_factory.h"
#endif

#include "bmc.h"
#include "apdr/apdr.h"
#include "bmc_simplepath.h"
#include "core/fts.h"
#include "defaults.h"
#include "frontends/btor2_encoder.h"
#include "interpolant.h"
#include "kinduction.h"
#include "printers/btor2_witness_printer.h"
#include "printers/vcd_witness_printer.h"
#include "prop.h"
#include "utils/logger.h"

using namespace cosa;
using namespace smt;
using namespace std;

/************************************* Option Handling setup
 * *****************************************/
// from optionparser-1.7 examples -- example_arg.cc
enum optionIndex
{
  UNKNOWN_OPTION,
  HELP,
  ENGINE,
  BOUND,
  PROP,
  VERBOSITY,
  VCDNAME,
  // for detail config
  PDR_ITP_MODE,
  SYGUS_LEMMA_REPAIR_ON,
  SYGUS_LEMMA_GEN_ON,
  STRENGTHEN_OFF
  
};

struct Arg : public option::Arg
{
  static void printError(const char * msg1,
                         const option::Option & opt,
                         const char * msg2)
  {
    fprintf(stderr, "%s", msg1);
    fwrite(opt.name, opt.namelen, 1, stderr);
    fprintf(stderr, "%s", msg2);
  }

  static option::ArgStatus Numeric(const option::Option & option, bool msg)
  {
    char * endptr = 0;
    if (option.arg != 0 && strtol(option.arg, &endptr, 10)) {
    };
    if (endptr != option.arg && *endptr == 0) return option::ARG_OK;

    if (msg) printError("Option '", option, "' requires a numeric argument\n");
    return option::ARG_ILLEGAL;
  }

  static option::ArgStatus NonEmpty(const option::Option & option, bool msg)
  {
    if (option.arg != 0 && option.arg[0] != 0) return option::ARG_OK;

    if (msg)
      printError("Option '", option, "' requires a non-empty argument\n");
    return option::ARG_ILLEGAL;
  }
};

const option::Descriptor usage[] = {
  { UNKNOWN_OPTION,
    0,
    "",
    "",
    Arg::None,
    "USAGE: cosa2 [options] <btor file>\n\n"
    "Options:" },
  { HELP, 0, "", "help", Arg::None, "  --help \tPrint usage and exit." },
  { ENGINE,
    0,
    "e",
    "engine",
    Arg::NonEmpty,
    "  --engine, -e <engine> \tSelect engine from [bmc, bmc-sp, ind, "
    "interp, apdr]." },
  { BOUND,
    0,
    "k",
    "bound",
    Arg::Numeric,
    "  --bound, -k \tBound to check up until (default: 10)." },
  { PROP,
    0,
    "p",
    "prop",
    Arg::Numeric,
    "  --prop, -p \tProperty index to check (default: 0)." },
  { VERBOSITY,
    0,
    "v",
    "verbosity",
    Arg::Numeric,
    "  --verbosity, -v \tVerbosity for printing to standard out." },
  { VCDNAME,
    0,
    "",
    "vcd",
    Arg::NonEmpty,
    "  --vcd \tName of Value Change Dump (VCD) if witness exists." },
  // pdr configurations
  { PDR_ITP_MODE,
    0,
    "",
    "itpmode",
    Arg::Numeric,
    "  --itpmode \tInterpolant mode : 0 for normal, 3 for bit-level interpolant" },
  { SYGUS_LEMMA_REPAIR_ON,
    0,
    "",
    "sygus-repair",
    Arg::None,
    "  --sygus-repair \tEnable SyGuS for lemma repairing" },
  { SYGUS_LEMMA_GEN_ON,
    0,
    "",
    "sygus-summary",
    Arg::None,
    "  --sygus-summary \tEnable SyGuS for lemma summary" },
  { STRENGTHEN_OFF,
    0,
    "",
    "strengthen-off",
    Arg::None,
    "  --strengthen-off \tDo not try to block CTG (counterexample-to-generalization)" },
  { 0, 0, 0, 0, 0, 0 }
};
/*********************************** end Option Handling setup
 * ***************************************/

int main(int argc, char ** argv)
{
  argc -= (argc > 0);
  argv += (argc > 0);  // skip program name argv[0] if present
  option::Stats stats(usage, argc, argv);
  std::vector<option::Option> options(stats.options_max);
  std::vector<option::Option> buffer(stats.buffer_max);
  option::Parser parse(usage, argc, argv, &options[0], &buffer[0]);

  if (parse.error()) {
    return 3;
  }

  if (options[HELP] || argc == 0) {
    option::printUsage(cout, usage);
    return 2;  // unknown is 2
  }

  if (parse.nonOptionsCount() != 1) {
    option::printUsage(cout, usage);
    return 3;
  }

  bool unknown_options = false;
  for (option::Option * opt = options[UNKNOWN_OPTION]; opt; opt = opt->next()) {
    unknown_options = true;
  }

  if (unknown_options) {
    option::printUsage(cout, usage);
    return 3;
  }

  Engine engine = default_engine;
  unsigned int prop_idx = default_prop_idx;
  unsigned int bound = default_bound;
  unsigned int verbosity = default_verbosity;
  std::string vcd_name;
  unsigned int itp_mode = 0;
  bool strengthen_off = options[STRENGTHEN_OFF] != NULL;
  bool sygus_repair_on = options[SYGUS_LEMMA_REPAIR_ON] != NULL;
  bool sygus_lemma_gen_on = options[SYGUS_LEMMA_GEN_ON] != NULL;

  for (int i = 0; i < parse.optionsCount(); ++i) {
    option::Option & opt = buffer[i];
    switch (opt.index()) {
      case HELP:
        // not possible, because handled further above and exits the program
      case ENGINE: engine = to_engine(opt.arg); break;
      case BOUND: bound = atoi(opt.arg); break;
      case PROP: prop_idx = atoi(opt.arg); break;
      case VERBOSITY: verbosity = atoi(opt.arg); break;
      case VCDNAME: vcd_name = opt.arg; break;
      case UNKNOWN_OPTION:
        // not possible because Arg::Unknown returns ARG_ILLEGAL
        // which aborts the parse with an error
        break;
    }
  }

  // set logger verbosity -- can only be set once
  logger.set_verbosity(verbosity);

  string filename(parse.nonOption(0));

  try {
    SmtSolver s;
    SmtSolver second_solver;
    if (engine == INTERP) {
      #ifdef WITH_MSAT
      // need mathsat for interpolant based model checking
      s = MsatSolverFactory::create();
      second_solver = MsatSolverFactory::create_interpolating_solver();
      #else
      throw CosaException("Interpolation-based model checking requires MathSAT and "
                          "this version of cosa2 is built without MathSAT.\nPlease "
                          "setup smt-switch with MathSAT and reconfigure using --with-msat.\n"
                          "Note: MathSAT has a custom license and you must assume all "
                          "responsibility for meeting the license requirements.");
      #endif
    } else if (engine == APDR) {
      #ifdef WITH_MSAT
      // need mathsat for interpolant based model checking
      s = BoolectorSolverFactory::create();
      s->set_opt("produce-models", "true");
      s->set_opt("incremental", "true");
      Configurations::MsatInterpolatorConfiguration cfg;
      cfg.interpolation_mode = std::to_string( std::min(itp_mode,4U) );
      second_solver = MsatSolverFactory::create_interpolating_solver(cfg);
      #else
      throw CosaException("APDR-based model checking requires MathSAT and "
                          "this version of cosa2 is built without MathSAT.\nPlease "
                          "setup smt-switch with MathSAT and reconfigure using --with-msat.\n"
                          "Note: MathSAT has a custom license and you must assume all "
                          "responsibility for meeting the license requirements.");
      #endif
    } else {
      // boolector is faster but doesn't support interpolants
      s = BoolectorSolverFactory::create();
      s->set_opt("produce-models", "true");
      s->set_opt("incremental", "true");
    }

    FunctionalTransitionSystem fts(s);
    BTOR2Encoder btor_enc(filename, fts);

    FunctionalTransitionSystem * msat_fts;
    BTOR2Encoder * msat_enc;
    Property * msat_p;

    unsigned int num_bad = btor_enc.badvec().size();
    if (prop_idx >= num_bad) {
      cout << "Property index " << prop_idx;
      cout << " is greater than the number of bad tags in the btor file (";
      cout << num_bad << ")" << endl;
      return 3;
    }

    Term bad = btor_enc.badvec()[prop_idx];
    Property p(fts, s->make_term(PrimOp::Not, bad));
    logger.log(1, "Solving property: {}", p.prop());

    logger.log(3, "INIT:\n{}", fts.init());
    logger.log(3, "TRANS:\n{}", fts.trans());

    std::shared_ptr<Prover> prover;
    if (engine == BMC) {
      prover = std::make_shared<Bmc>(p, s);
    } else if (engine == BMC_SP) {
      prover = std::make_shared<BmcSimplePath>(p, s);
    } else if (engine == KIND) {
      prover = std::make_shared<KInduction>(p, s);
    } else if (engine == INTERP) {
      assert(second_solver != NULL);
      prover = std::make_shared<InterpolantMC>(p, s, second_solver);
    } else if (engine == APDR) {
      msat_fts = new FunctionalTransitionSystem(second_solver);
      msat_enc = new BTOR2Encoder(filename, *msat_fts);

      Term bad_msat = msat_enc->badvec()[prop_idx];
      msat_p = new Property(*msat_fts, second_solver->make_term(PrimOp::Not, bad_msat));

      GlobalAPdrConfig.USE_SYGUS_REPAIR = sygus_repair_on;
      GlobalAPdrConfig.USE_SYGUS_LEMMA_GEN = sygus_lemma_gen_on;
      GlobalAPdrConfig.BLOCK_CTG = !strengthen_off;
      prover = std::make_shared<Apdr> (p, s, *msat_p, second_solver,
        std::unordered_set<smt::Term>(), std::unordered_set<smt::Term> () );
    } else {
      throw CosaException("Unimplemented engine.");
    }

    ProverResult r = prover->check_until(bound);
    if (r == FALSE) {
      cout << "sat" << endl;
      cout << "b" << prop_idx << endl;
      vector<UnorderedTermMap> cex;
      if (prover->witness(cex)) {
        print_witness_btor(btor_enc, cex);
        if (!vcd_name.empty()) {
          VCDWitnessPrinter vcdprinter(btor_enc, fts, cex);
          vcdprinter.DumpTraceToFile(vcd_name);
        }
      }
      if (engine == APDR) { // clean up
        delete msat_p;
        delete msat_enc;
        delete msat_fts;
      }
      return 1;
    } else if (r == TRUE) {
      cout << "unsat" << endl;
      cout << "b" << prop_idx << endl;
      if (engine == APDR) { // clean up
        delete msat_p;
        delete msat_enc;
        delete msat_fts;
      }
      return 0;
    } else {
      cout << "unknown" << endl;
      cout << "b" << prop_idx << endl;
      if (engine == APDR) { // clean up
        delete msat_p;
        delete msat_enc;
        delete msat_fts;
      }
      return 2;
    }
  }
  catch (CosaException & ce) {
    cout << ce.what() << endl;
    cout << "unknown" << endl;
    cout << "b" << prop_idx << endl;
    return 3;
  }
  catch (SmtException & se) {
    cout << se.what() << endl;
    cout << "unknown" << endl;
    cout << "b" << prop_idx << endl;
    return 3;
  }
  catch (std::exception & e) {
    cout << "Caught generic exception..." << endl;
    cout << e.what() << endl;
    cout << "unknown" << endl;
    cout << "b" << prop_idx << endl;
    return 3;
  }

  return 3;
}
