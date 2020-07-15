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
#include "frontends/smtlib2parser.h"

#include <fstream>
#include <sstream>

#define INFO(...) logger.log(1, __VA_ARGS__)

namespace cosa {

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
    bool assert_inv_in_prevF) {
  
  if (GlobalAPdrConfig.SYGUS_MODE & APdrConfig::SYGUS_MODE_T::INTERNAL) {
    // do it here
    
    sat_enum::Enumerator sygus_enumerator(
      btor_var_to_msat_func_,
      to_next_func_,
      btor(),msat(),
      ts_.trans(), ts_.init(),
      prevF_btor /*prevF*/, 
      cexs /*cexs \*/,
      facts /*facts*/,
      prop_btor /*prop_btor*/,
      op_extract_->GetSyntaxConstruct()      
    );

    INFO("ID {} --- Enum status before: ", sygus_enumerator.GetCexRefId());
    sygus_enumerator.GetEnumStatus().dump();
    INFO("\n--- Enum status end ");
    auto ret = sygus_enumerator.EnumCurrentLevel();
    INFO("--- Enum status after: ");
    sygus_enumerator.GetEnumStatus().dump();
    INFO("\n--- Enum status end ");
    if (ret.second != nullptr)
      return ret.second;
  
  // if use enum::Enumerator, you will not need to move to next level
  #ifndef SYGUS_ENUM_NO_MOVE_TO_NEXT_LEVEL
    // at this point, move to next level, because we run out of candidates
    sygus_enumerator.MoveToNextLevel();
  #endif
  }

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
  }

  return nullptr;
} // do_sygus

} // namespace cosa

