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
 ** \brief Exec a subprocess
 **
 ** 
 **/


#pragma once

#include <string>
#include <vector>

namespace cosa {

std::string os_portable_append_dir(const std::string& dir1,
                                   const std::string& dir2);

/// the result from executing
struct exec_result_t {
  /// has timeout
  bool timeout;
  /// failed execution
  enum _failure {PREIO = 0, FORK = 1, ALARM, ARG, EXEC, WAIT, NONE } failure;
  /// return value
  unsigned ret;
  /// true if it exits with _exit() call
  bool subexit_normal;
  /// the execution time
  double seconds;
};

/// the type of redirect
enum exec_redirect_t {NONE = 0 , STDOUT = 1 , STDERR = 2, BOTH = 3};
/// execute some executables
/// timeout (if 0 will wait forever)
exec_result_t timed_execute(const std::vector<std::string> & cmdargs, 
    const std::string & redirect_output_file = "", exec_redirect_t rdt = exec_redirect_t::BOTH,
    unsigned timeout = 0,
    const std::string & pid_file_name = "");


} // namespace cosa


