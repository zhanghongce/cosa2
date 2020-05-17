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

smt::Term Apdr::do_sygus(const smt::Term & prevF_msat, 
  const smt::Term & prop_msat,
  const std::vector<Model *> & cexs, const std::vector<Model *> & facts,
  bool assert_inv_in_prevF) {
  
  { // write to file
    std::ofstream fout(GlobalAPdrConfig.CVC4QUERY_OUT1);
    if (!fout.is_open())
      throw CosaException("Cannot open " + GlobalAPdrConfig.CVC4QUERY_OUT1 + " for write.");
    sygus_query_gen_->GenToFile(prevF_msat, facts, cexs, prop_msat, false, fout);
    fout.close();
  }

  // then execute 1. first try pbe, if fail try no-pbe
  std::string cvc4_full_path = "cvc4";
  if (!GlobalAPdrConfig.CVC4PATH.empty())
    cvc4_full_path = os_portable_append_dir(GlobalAPdrConfig.CVC4PATH, cvc4_full_path );

  bool succ = true;
  {
    std::vector<std::string> cmd = {cvc4_full_path};
    cmd.push_back("--lang=sygus2");
    cmd.push_back(GlobalAPdrConfig.CVC4QUERY_OUT1);
    auto res = timed_execute(cmd, GlobalAPdrConfig.CVC4QUERY_BACK1, BOTH, GlobalAPdrConfig.SYGUS_PBE_TIME_LIMIT);
    if (res.timeout) {
      INFO("SyGuS-1 timeout.");
      succ = false;
    }

    if (succ) {
      std::ifstream fin(GlobalAPdrConfig.CVC4QUERY_BACK1);
      std::string line;
      std::getline(fin, line);
      if (line.find("unsat") == line.npos) // if we don't have unsat
        succ = false;
      if (succ) {
        std::stringstream buf;
        buf << fin.rdbuf();
        if (buf.str().find("Error") != std::string::npos) {
          succ = false;
          INFO("SyGuS-1 output contains error.");
          throw CosaException("Unable to parser sygus result from file: " + GlobalAPdrConfig.CVC4QUERY_BACK1);
        }
        if(succ) {
          auto ret_term = smtlib2parser.ParseSmtFromString(buf.str());
          if (ret_term != nullptr)
            return ret_term;
          throw CosaException("Unable to parser sygus result from file: " + GlobalAPdrConfig.CVC4QUERY_BACK1);
          // else
          succ = false;
        }
      }

      INFO("SyGuS-1 headline: " + line);
    }
  }
  assert (!succ);
  
  { // try the second method
    std::ofstream fout(GlobalAPdrConfig.CVC4QUERY_OUT2);
    if (!fout.is_open())
      throw CosaException("Cannot open " + GlobalAPdrConfig.CVC4QUERY_OUT2 + " for write.");
    sygus_query_gen_->GenToFile(prevF_msat, facts, cexs, prop_msat, true, fout);
    fout.close();
  }
  succ = true;
  {
    std::vector<std::string> cmd = {cvc4_full_path};
    cmd.push_back("--lang=sygus2");
    cmd.push_back("--no-sygus-pbe");
    cmd.push_back(GlobalAPdrConfig.CVC4QUERY_OUT2);
    auto res = timed_execute(cmd, GlobalAPdrConfig.CVC4QUERY_BACK2, BOTH, GlobalAPdrConfig.SYGUS_PBE_TIME_LIMIT);
    if (res.timeout) {
      INFO("SyGuS-2 timeout.");
      succ = false;
    }

    if (succ) {
      std::ifstream fin(GlobalAPdrConfig.CVC4QUERY_BACK2);
      std::string line;
      std::getline(fin, line);
      if (line.find("unsat") == line.npos) // if we don't have unsat
        succ = false;
      if (succ) {
        std::stringstream buf;
        buf << fin.rdbuf();
        if (buf.str().find("Error") != std::string::npos) {
          succ = false;
          INFO("SyGuS-2 output contains error.");
          throw CosaException("Unable to parser sygus result from file: " + GlobalAPdrConfig.CVC4QUERY_BACK2);
        }
        if(succ) {
          auto ret_term = smtlib2parser.ParseSmtFromString(buf.str());
          if (ret_term != nullptr)
            return ret_term;
          throw CosaException("Unable to parser sygus result from file: " + GlobalAPdrConfig.CVC4QUERY_BACK2);
          // else
          succ = false;
        }
      }

      INFO("SyGuS-2 headline: " + line);
    }
  }

  assert (!succ);
  INFO("SyGuS 1&2 both failed.");
  return nullptr;
}

} // namespace cosa

