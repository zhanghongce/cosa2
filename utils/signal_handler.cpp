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
 ** \brief Signal handler for debug printing purpose
 **
 ** 
 **/

#include <apdr/config.h>

#include <iostream>
#include <string>
#include <string_view>
#include <signal.h>
#include <assert.h>
#include <unistd.h>

namespace cosa{

#if !defined(NDEBUG) || defined(SIGNAL_DUMP)

sighandler_t old_SIGQUIT_handler;
sighandler_t old_SIGINT_handler;
sighandler_t old_SIGALARM_handler;

static std::vector<std::string_view> state_names = {
  "Idle",
  "InitCache", 
  "CheckUntill",
  "GetBadStateForProp", 
  "BlockBadStateForProp", 
  "PushingAll",
  "PushAFrame",
  "PushFirstTryAll",
  "PushTryWhetherCexPushable",
  "PushTrySygus",
  "PushTryBlockCtg",
  "SolveTrans",
  "TryRecBlock",
  "DoRecBlock"
};

std::string_view inline enum2str(APdrConfig::APDR_WORKING_STATE_T s) {
   unsigned idx = (unsigned) (s);
   if (idx >= state_names.size()) {
     std::cerr << "enum2str out of range!" << std::endl;
     exit(1);
   }
   return state_names.at(idx);
}

void dumping_apdr_frames() {
  if (GlobalAPdrConfig.ApdrInterface)
    GlobalAPdrConfig.ApdrInterface->dump_frames(std::cerr);
  std::cerr.flush();
}

void dumping_apdr_states() {
  unsigned idx = 0;
  std::cerr << "\n----------------------" <<std::endl;
  for (auto && s : GlobalAPdrConfig.APDR_WORKING_STATE_STACK) {
    std::cerr << idx ++ << "\t:\t" << enum2str(s.first) << " (" << s.second <<")" << std::endl;
  }
  std::cerr << idx ++ << "\t:\t" 
    << enum2str(GlobalAPdrConfig.APDR_WORKING_STATE.first) 
    << " (" << GlobalAPdrConfig.APDR_WORKING_STATE.second <<")" << std::endl;
  std::cerr << "Good itp (stronger than prop): " 
            << GlobalAPdrConfig.STAT_ITP_STRONG_COUNT 
            << "/" << GlobalAPdrConfig.STAT_ITP_CHECK_COUNT
            << std::endl;
  std::cerr.flush();
}

void SIGQUIT_handler(int sig) {
  signal(sig, SIG_IGN);
  dumping_apdr_states();
  signal(sig, SIGQUIT_handler);
}

void SIGALARM_handler(int sig) {
  signal(sig, SIG_IGN);
  dumping_apdr_states();
  dumping_apdr_frames();
  dumping_apdr_states();
  signal(sig, SIGALARM_handler);
}

void SIGINT_handler(int sig) {

}


void RegisterApdrSigHandler() {
  old_SIGQUIT_handler = signal(SIGQUIT, SIGQUIT_handler);
  old_SIGALARM_handler = signal(SIGALRM, SIGALARM_handler);
  alarm(0);
  alarm(3200);
}

void UnregisterApdrSigHandler() {
  signal(SIGQUIT, old_SIGQUIT_handler);
  //signal(SIGALRM, old_SIGALARM_handler);
}

#else
void SIGQUIT_handler(int sig) {

}

void SIGINT_handler(int sig) {

}

void RegisterApdrSigHandler() {

}

void UnregisterApdrSigHandler() {

}

#endif

} // namespace cosa