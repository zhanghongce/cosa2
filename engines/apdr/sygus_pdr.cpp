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
    get_free_symbols(itp_btor, itp_vars);
    for (auto && p : itp_vars)
      max_var_width = MAX(max_var_width, p->get_sort()->get_width());
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


    assert (prop_btor == nullptr);

    unsat_enum::Enumerator sygus_enumerator(
      to_next_func_,
      btor(),
      ts_.trans(), ts_.init(),
      prevF_btor /*prevF*/, 
      cexs /*cexs \*/,
      sygus_term_manager_   
    );

    // initially, you only have variables and constants for each var
    // for each width, estimate #pred and decide if

    //   0. use itp's vars & syntax's op, =, =/=, <, <=
    //   1. use vars, consts =, =/=
    //   15. vars, consts, unary and binary ops, =, =/= 
    //   2. use vars, consts =, =/=, < , <=
    //   4. all terms & preds containing those vars and level <= 3
    //   don't add that many terms that early
    //   fail as needed don't try too hard.
    //
    //   conj grow to conj_depth_threshold_for_internal_sygus + 1


















#ifdef DEBUG_DUMP_ENUM_STAT
    if (GlobalTimer.EventOccurSinceFlagClear("Enum.PredicateGen")) {
      auto [tdiff, npred, speed] = GlobalTimer.GetStatus("Enum.PredicateGen");
      ENUM_STAT_INFO("{} seconds, {} pred generated, speed: {}", tdiff, npred, speed );
    }
#endif

    auto conjdepth_predwidth = sygus_enumerator.GetEnumStatus().get_conjdepth_predwidth();
    do{
      ENUM_STAT_INFO("ID {} --- Enum status before: ", sygus_enumerator.GetCexRefId());

#ifdef DEBUG_DUMP_ENUM_STAT
      sygus_enumerator.GetEnumStatus().dump();

      float ttotal_old; long long nquery_old; 
      if (GlobalTimer.EventOccurSinceFlagClear("Enum.Z3Query")) {
        auto [ttotal, nquery, speed] = GlobalTimer.GetTotal("Enum.Z3Query");
        ttotal_old = ttotal;
        nquery_old = nquery;
      } else {
        ttotal_old = 0; nquery_old = 0;
      }
#endif
      ENUM_STAT_INFO("--- Enum status end, enumerating... ");
      auto ret = sygus_enumerator.EnumCurrentLevel();
      ENUM_STAT_INFO("--- Enum status after: ");
#ifdef DEBUG_DUMP_ENUM_STAT
      sygus_enumerator.GetEnumStatus().dump();

      if (GlobalTimer.EventOccurSinceFlagClear("Enum.EnumPredConj")) {
        auto [tdiff, npred, speed] = GlobalTimer.GetStatus("Enum.EnumPredConj");
        ENUM_STAT_INFO("Enum.EnumPredConj: {} seconds, {} pred tested, speed: {}", tdiff, npred, speed );
      }
      if (GlobalTimer.EventOccurSinceFlagClear("Enum.Z3Query")) {
        auto [tdiff, nquery, speed] = GlobalTimer.GetTotal("Enum.Z3Query");
        ENUM_STAT_INFO("Enum.Z3Query (Total): {} seconds, #{} query, speed: {}", tdiff, nquery, speed );
        tdiff -= ttotal_old;
        nquery -= nquery_old;
        speed = nquery/tdiff;
        ENUM_STAT_INFO("Enum.Z3Query (Delta): {} seconds, #{} query, speed: {}", tdiff, nquery, speed );
      }
#endif
      ENUM_STAT_INFO("--- Enum status end ");
      
      if (ret.second != nullptr)
        return ret.second;
  
      conjdepth_predwidth = sygus_enumerator.GetEnumStatus().get_conjdepth_predwidth();

      // if use enum::Enumerator, you will not need to move to next level
      #ifndef SYGUS_ENUM_NO_MOVE_TO_NEXT_LEVEL
        // at this point, move to next level, because we run out of candidates
        sygus_enumerator.MoreConjunctions();
        ENUM_STAT_INFO(" --increase conj");
        // TODO: you need to decide what to do here ...
        // whether it worth it to go higher
        // and in what way, and maybe try <  and <= instead?
        // and ... strategy needed here
        if (conjdepth_predwidth.first > conj_depth_threshold_for_internal_sygus + 1) {
          ENUM_STAT_INFO(" --more terms");
          // GlobalTimer.ClearEvent("Enum.PredicateGen"); // no need to clear
          
          if ( ! sygus_enumerator.MoreTermPredicates() )
            break; // no more predicates, sygus failed
          sygus_enumerator.ResetConjunctionOne();

#ifdef DEBUG_DUMP_ENUM_STAT
          auto [tdiff, npred, speed] = GlobalTimer.GetStatus("Enum.PredicateGen");
          ENUM_STAT_INFO("{} seconds, {} pred generated, speed: {}", tdiff, npred, speed );
#endif
        }

        // QUESION: When to use extract? Never?
      #else
        #error "TODO: modify enum.h and enum.cpp to make API the same."
      #endif

      
    } while(conjdepth_predwidth.first <= conj_depth_threshold_for_internal_sygus);
  ENUM_STAT_INFO(" --internal sygus fail");
  } // end of sygus mode : INTERNAL

  // -------------- SYGUS EXTERNAL MODE -------------------------- //

  if (GlobalAPdrConfig.SYGUS_MODE & APdrConfig::SYGUS_MODE_T::EXTERNAL) {
    // then execute 1. first try pbe, if fail try no-pbe
    std::string cvc4_full_path = "cvc4";
    if (!GlobalAPdrConfig.CVC4PATH.empty())
      cvc4_full_path = os_portable_append_dir(GlobalAPdrConfig.CVC4PATH, cvc4_full_path );

    bool succ = true;
    bool time_out = false;
    unsigned time_used;

    smt::Term ret = EXEC_OP(GlobalAPdrConfig.CVC4QUERY_OUT1, GlobalAPdrConfig.CVC4QUERY_BACK1,
      "SYGUS-1", false, true, GlobalAPdrConfig.SYGUS_PBE_TIME_LIMIT,
      {cvc4_full_path,"--lang=sygus2"}, 
      succ, time_out, time_used,
      sygus_query_gen_.get(), smtlib2parser, 
      prevF_msat, prop_msat, {}, facts);
    if (ret != nullptr) {
      // GlobalAPdrConfig.SYGUS_PBE_TIME_LIMIT = time_used*2;
      return ret;
    }
    
    assert (!succ);

    ret = EXEC_OP(GlobalAPdrConfig.CVC4QUERY_OUT_NO_SYNTAX, GlobalAPdrConfig.CVC4QUERY_BACK_NO_SYNTAX,
      "SYGUS-1-nogrammar", false, false, GlobalAPdrConfig.SYGUS_PBE_TIME_LIMIT,
      {cvc4_full_path,"--lang=sygus2"},
      succ, time_out, time_used,
      sygus_query_gen_.get(), smtlib2parser, 
      prevF_msat, prop_msat, {}, facts);

    if (ret != nullptr) {
      // GlobalAPdrConfig.SYGUS_PBE_TIME_LIMIT = time_used*2;
      return ret;
    }

    if (time_out)
      GlobalAPdrConfig.SYGUS_PBE_TIME_LIMIT *= 2;

    assert (!succ);
    
    ret = EXEC_OP(GlobalAPdrConfig.CVC4QUERY_OUT2, GlobalAPdrConfig.CVC4QUERY_BACK2,
      "SYGUS-2", true, true, GlobalAPdrConfig.SYGUS_NO_PBE_TIME_LIMIT,
      {cvc4_full_path,"--lang=sygus2","--no-sygus-pbe"},
      succ, time_out, time_used,
      sygus_query_gen_.get(), smtlib2parser, 
      prevF_msat, prop_msat, cexs, facts);
    if (ret != nullptr) {
      // GlobalAPdrConfig.SYGUS_NO_PBE_TIME_LIMIT = time_used*2;
      return ret;
    }

    if (time_out)
      GlobalAPdrConfig.SYGUS_NO_PBE_TIME_LIMIT *= 2;

    assert (!succ);
    INFO("SyGuS 1&2 both failed.");
    return nullptr;
  } // end of sygus external mode

  return nullptr;
} // do_sygus

} // namespace cosa

