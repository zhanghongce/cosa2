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
#include "frontends/smv_encoder.h"
#include "frontends/smt_property_parser.h"
#include "interpolant.h"
#include "kinduction.h"
#include "printers/btor2_witness_printer.h"
#include "printers/vcd_witness_printer.h"
#include "prop.h"
#include "utils/logger.h"
#include "utils/signal_handler.h"

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
  PROPFILE,
  // for detail config
  PDR_ITP_MODE,
  LEMMA_GEN_MODE,
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

struct apdr_msat_environment {
    FunctionalTransitionSystem * msat_fts;
    BTOR2Encoder * msat_enc;
    Smtlib2PropertyParser * smtprop_msat;
    smt::Term prop_msat;
    Property * msat_p;
    apdr_msat_environment(
        smt::SmtSolver & msat,
        const std::string &filename,
        const std::string &smt_prop_file,
        unsigned prop_idx ):
      msat_fts(new FunctionalTransitionSystem(msat)),
      msat_enc(new BTOR2Encoder(filename, *msat_fts, true)),
      smtprop_msat(smt_prop_file.empty()? NULL: (new Smtlib2PropertyParser(msat, *msat_fts)) ),
      prop_msat(
        smt_prop_file.empty() ? (msat_enc->propvec()[prop_idx]) :
        (smtprop_msat->ParsePropertyFromFile(smt_prop_file),smtprop_msat->propvec()[prop_idx]) ),
      msat_p(new Property(*msat_fts, prop_msat))
     {  }
     apdr_msat_environment():
      msat_fts(NULL), msat_enc(NULL), smtprop_msat(NULL), msat_p(NULL) {}
     apdr_msat_environment(apdr_msat_environment && a):
      msat_fts(a.msat_fts), msat_enc(a.msat_enc), smtprop_msat(a.smtprop_msat),
      prop_msat(a.prop_msat), msat_p(a.msat_p) {
        a.msat_fts = NULL; a.msat_enc = NULL; a.smtprop_msat = NULL; a.msat_p = NULL;
      }
    apdr_msat_environment(const apdr_msat_environment & ) = delete;
    ~apdr_msat_environment() {
      if (msat_p) delete msat_p;
      if (smtprop_msat) delete smtprop_msat;
      if (msat_enc) delete msat_enc;
      if (msat_p)  delete msat_fts;
    }
    apdr_msat_environment& operator=(const apdr_msat_environment &) = delete;
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
  { PROPFILE,
    0,
    "",
    "propfile",
    Arg::NonEmpty,
    "  --propfile \tName of the file that supplies extra properties." },
  // pdr configurations
  { PDR_ITP_MODE,
    0,
    "",
    "itpmode",
    Arg::Numeric,
    "  --itpmode \tInterpolant mode : 0 for normal, 3 for bit-level interpolant" },
  { LEMMA_GEN_MODE,
    0,
    "",
    "lemma-gen-mode",
    Arg::Numeric,
    "  --lemma-gen-mode \tLemma generation : 0(itp) 1(v) 2(syn) 3(all) 4(sygus)" },
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

ProverResult check_prop(Engine engine,
                        unsigned int bound,
                        Property & p,
                        SmtSolver & s,
                        SmtSolver & second_solver,
                        std::vector<UnorderedTermMap> & cex,
                        apdr_msat_environment & apdr_env)
{
  logger.log(1, "Solving property: {}", p.prop());

  logger.log(3, "INIT:\n{}", p.transition_system().init());
  logger.log(3, "TRANS:\n{}", p.transition_system().trans());

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
    if(! apdr_env.msat_p) 
      throw CosaException("APDR on SMV is not implemented.");
    Apdr * ptr = new Apdr(p, s, *apdr_env.msat_p, second_solver,
      std::unordered_set<smt::Term>(), std::unordered_set<smt::Term> ());
    GlobalAPdrConfig.ApdrInterface = ptr;    
    prover = std::shared_ptr<Apdr> ( ptr );
  }
    else {
    throw CosaException("Unimplemented engine.");
  }

  ProverResult r = prover->check_until(bound);
  if (r == FALSE) {
    prover->witness(cex);
  }

  GlobalAPdrConfig.ApdrInterface = NULL;

  return r;
}

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
  std::string property_file_name;
  unsigned int itp_mode = 0;
  unsigned int lemma_gen_mode = GlobalAPdrConfig.LEMMA_GEN_MODE;
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
      case PROPFILE: property_file_name = opt.arg; break;
      case PDR_ITP_MODE: itp_mode = atoi(opt.arg); break;
      case LEMMA_GEN_MODE: lemma_gen_mode = atoi(opt.arg); break;
      case UNKNOWN_OPTION:
        // not possible because Arg::Unknown returns ARG_ILLEGAL
        // which aborts the parse with an error
        break;
    }
  }

  // set logger verbosity -- can only be set once
  logger.set_verbosity(verbosity);

  string filename(parse.nonOption(0));

  int status_code = 3;

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
      GlobalAPdrConfig.USE_SYGUS_REPAIR = sygus_repair_on;
      GlobalAPdrConfig.USE_SYGUS_LEMMA_GEN = sygus_lemma_gen_on;
      GlobalAPdrConfig.BLOCK_CTG = !strengthen_off;
      GlobalAPdrConfig.LEMMA_GEN_MODE = (APdrConfig::LEMMA_GEN_MODE_T)lemma_gen_mode;

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

    // TODO: make this less ugly, just need to keep it in scope if using
    //       it would be better to have a generic encoder
    //       and also only create the transition system once
    ProverResult r;
    string file_ext = filename.substr(filename.find_last_of(".") + 1);
    if (file_ext == "btor2" || file_ext == "btor") {
      logger.log(2, "Parsing BTOR2 file: {}", filename);
      FunctionalTransitionSystem fts(s);
      BTOR2Encoder btor_enc(filename, fts, true);
      Smtlib2PropertyParser prop_parser(s, fts);
      if (!property_file_name.empty()) {
        bool succ = prop_parser.ParsePropertyFromFile(property_file_name);
        if (!succ)
          throw CosaException("Parsing property file : " + filename + " failed, with msg :" + prop_parser.GetParserErrorMessage());
      }
      const TermVec & propvec = property_file_name.empty() ? btor_enc.propvec() : prop_parser.propvec();
      unsigned int num_props = propvec.size();
      if (prop_idx >= num_props) {
        throw CosaException(
            "Property index " + to_string(prop_idx)
            + " is greater than the number of properties in file " + filename
            + " (" + to_string(num_props) + ")");
      }
      Term prop = propvec[prop_idx];

      Property p(fts, prop);
      vector<UnorderedTermMap> cex;

      if (engine == APDR) {
        RegisterApdrSigHandler();
      }
      
      apdr_msat_environment apdr_env = 
        engine == APDR ? apdr_msat_environment(second_solver, filename, property_file_name, prop_idx) : 
                         apdr_msat_environment();

      r = check_prop(engine, bound, p, s, second_solver, cex, apdr_env);

      if (engine == APDR)
        UnregisterApdrSigHandler();

      // print btor output
      if (r == FALSE) {
        cout << "sat" << endl;
        cout << "b" << prop_idx << endl;
        if (cex.size()) {
          print_witness_btor(btor_enc, cex);
          if (!vcd_name.empty()) {
            VCDWitnessPrinter vcdprinter(fts, cex);
            vcdprinter.DumpTraceToFile(vcd_name);
          }
        }
        status_code = 1;
      } else if (r == TRUE) {
        cout << "unsat" << endl;
        cout << "b" << prop_idx << endl;
        status_code = 0;
      } else {
        cout << "unknown" << endl;
        cout << "b" << prop_idx << endl;
        status_code = 2;
      }

    } else if (file_ext == "smv") {
      logger.log(2, "Parsing SMV file: {}", filename);
      RelationalTransitionSystem rts(s);
      SMVEncoder smv_enc(filename, rts);
      const TermVec & propvec = smv_enc.propvec();
      unsigned int num_props = propvec.size();
      if (prop_idx >= num_props) {
        throw CosaException(
            "Property index " + to_string(prop_idx)
            + " is greater than the number of properties in file " + filename
            + " (" + to_string(num_props) + ")");
      }
      Term prop = propvec[prop_idx];
      Property p(rts, prop);
      std::vector<UnorderedTermMap> cex;
      apdr_msat_environment apdr_env;
      r = check_prop(engine, bound, p, s, second_solver, cex, apdr_env);
      logger.log(0, "Property {} is {}", prop_idx, to_string(r));

      if (r == FALSE) {
        for (size_t t = 0; t < cex.size(); t++) {
          cout << "AT TIME " << t << endl;
          for (auto elem : cex[t]) {
            cout << "\t" << elem.first << " : " << elem.second << endl;
          }
        }
        if (!vcd_name.empty()) {
          VCDWitnessPrinter vcdprinter(rts, cex);
          vcdprinter.DumpTraceToFile(vcd_name);
        }
      }
    } else {
      throw CosaException("Unrecognized file extension " + file_ext
                          + " for file " + filename);
    }
  }
  catch (CosaException & ce) {
    cout << ce.what() << endl;
    cout << "unknown" << endl;
    cout << "b" << prop_idx << endl;
  }
  catch (SmtException & se) {
    cout << se.what() << endl;
    cout << "unknown" << endl;
    cout << "b" << prop_idx << endl;
  }
  catch (std::exception & e) {
    cout << "Caught generic exception..." << endl;
    cout << e.what() << endl;
    cout << "unknown" << endl;
    cout << "b" << prop_idx << endl;
  }

  return status_code;
}
