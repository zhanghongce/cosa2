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

namespace cosa{

void SIGQUIT_handler(int sig);
void SIGINT_handler(int sig);

void RegisterApdrSigHandler();
void UnregisterApdrSigHandler();

} // namespace cosa