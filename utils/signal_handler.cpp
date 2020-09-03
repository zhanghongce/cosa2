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
#include <apdr/support.h>

#include <iostream>
#include <string>
#include <string_view>
#include <signal.h>
#include <assert.h>
#include <unistd.h>


namespace cosa{

#ifdef SIGNAL_DUMP

sighandler_t old_SIGQUIT_handler;
sighandler_t old_SIGINT_handler;
sighandler_t old_SIGALARM_handler;

void dumping_apdr_frames() {
  if (GlobalAPdrConfig.ApdrInterface)
    GlobalAPdrConfig.ApdrInterface->dump_info(std::cerr);
  std::cerr.flush();
}

void dumping_apdr_states() {
  unsigned idx = 0;
  std::cerr << "\n----------------------" <<std::endl;
  for (const auto & s : GlobalAPdrConfig.Apdr_working_state_stack) {
    std::cerr << idx ++ << "\t:\t" << GlobalAPdrConfig.Apdr_function_tracing_func_str(s)
              <<  " (" << GlobalAPdrConfig.Apdr_function_invocation_count.at(s) <<")" << std::endl;
  }

  std::cerr.flush();
}

void SIGQUIT_handler(int sig) {
  signal(sig, SIG_IGN);
  dumping_apdr_frames();
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
  alarm(3200); // get a summary at 3200s 
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