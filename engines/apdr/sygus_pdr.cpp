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
 ** \brief Pdr's sygus interface
 **
 ** 
 **/

#include "apdr.h"

#include "utils/exec.h"
#include "utils/logger.h"
#include "utils/exceptions.h"
#include "utils/multitimer.h"
#include "utils/term_analysis.h"
#include "frontends/smtlib2parser.h"

#include <fstream>
#include <sstream>

#define INFO(...) logger.log(1, __VA_ARGS__)

// #define DEBUG_DUMP_ENUM_STAT 1
#ifdef DEBUG_DUMP_ENUM_STAT
  #define ENUM_STAT_INFO(...) INFO(__VA_ARGS__)
#else
  #define ENUM_STAT_INFO(...) do{}while(0)
#endif

namespace cosa {

#define MAX(a,b) ((a)>(b) ? (a) : (b))
// extracting information from interpolant of certain round
void ApdrSygusHelper::SetItpForCurrentRound(const smt::Term & itp, unsigned fidx_prev) {
  itp_btor = itp; fidx = fidx_prev; max_var_width = 0;
  itp_vars.clear();
  conj_depth_threshold_for_internal_sygus = GlobalAPdrConfig.STARTING_CONJ_DEPTH;

  if (itp_btor) {
    get_free_symbols(itp_btor, itp_vars); // TODO: CHANGE TO constants here
    for (auto && p : itp_vars)
      max_var_width = MAX(max_var_width, p->get_sort()->get_width()); // std::max does not fit here
    conj_depth_threshold_for_internal_sygus = itp_vars.size();
  }
}
#undef MAX



static smt::Term EXEC_OP(const std::string & outfile, const std::string & infile, const std::string & text,
  bool assert_in_prev, bool use_syntax, unsigned time_limit, const std::vector<std::string> & cmd_args,
  bool & succ, bool & timeout, unsigned & time_used,
  sygus::SyGusQueryGen *sygus_query_gen_, 
  Smtlib2Parser & smtlib2parser,

  const smt::Term & prevF_msat, 
  const smt::Term & prop_msat,
  const std::vector<Model *> & cexs,
  const std::vector<Model *> & facts) {
    
    {
      std::ofstream fout(outfile);
      if (!fout.is_open())
        throw CosaException("Cannot open " + outfile + " for write.");
      sygus_query_gen_->GenToFile(prevF_msat, facts, cexs, prop_msat, assert_in_prev, use_syntax, fout , "");      \
      fout.close();
    }
    succ = true;
    timeout = false;
    {
      std::vector<std::string> cmd = (cmd_args);
      cmd.push_back(outfile);
      auto res = timed_execute(cmd, infile, BOTH, time_limit);
      if (res.timeout) {
        INFO(text + " timeout, exceed: {}" , time_limit);
        timeout = true;
        succ = false;
      }
      if (succ) {
        std::ifstream fin(infile);
        std::string line;
        std::getline(fin, line);
        if (line.find("unsat") == line.npos)
          succ = false;
        if (succ) {
          std::stringstream buf;
          buf << fin.rdbuf();
          if (buf.str().find("Error") != std::string::npos) {
            succ = false;
            INFO(text + " output contains error.");
            throw CosaException("Unable to parser sygus result from file: " + infile);
          }
          if(succ) {
            time_used = (unsigned) res.seconds;
            auto ret_term = smtlib2parser.ParseSmtFromString(buf.str());
            if (ret_term != nullptr)
              return ret_term;
            throw CosaException("Unable to parser sygus result from file: " + infile);
            succ = false;
          }
        }
        INFO(text + " headline: " + line);
        if (line.find ("Error") != line.npos || line.find ("error") != line.npos)
          throw CosaException("CVC4 error shown by : " + infile);
      }
    }
    return nullptr;
  }


smt::Term Apdr::do_sygus(const smt::Term & prevF_msat, 
    const smt::Term & prevF_btor,
    const smt::Term & prop_msat,
    const smt::Term & prop_btor,
    const std::vector<Model *> & cexs, const std::vector<Model *> & facts,
    bool assert_inv_in_prevF,
    ApdrSygusHelper & sygus_info /* use itp var size*/) {
  
  if (sygus_info.itp_btor != NULL && sygus_info.max_var_width < GlobalAPdrConfig.NO_SYGUS_IF_ITP_VARWIDTH_LESS_THAN)
    return nullptr; // no need for sygus

  if (GlobalAPdrConfig.SYGUS_MODE & APdrConfig::SYGUS_MODE_T::INTERNAL) {
    // do it here
    ENUM_STAT_INFO(" -- Building term & pred ...");
    GlobalTimer.ClearEventFlag("Enum.PredicateGen");
    GlobalTimer.ClearEventFlag("Enum.EnumPredConj");


    assert (!cexs.empty());

    unsat_enum::Enumerator sygus_enumerator(
      to_next_func_,
      btor(),
      ts_.trans(), ts_.init(),
      prevF_btor /*prevF*/, 
      cexs /*cexs \*/,
      sygus_term_manager_   
    );
  auto ret = sygus_enumerator.GetCandidate();
  if (ret)
    return ret;
  ENUM_STAT_INFO(" --internal sygus fail");
  } // end of sygus mode : INTERNAL

  return nullptr;
} // do_sygus

} // namespace cosa

