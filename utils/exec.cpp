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

#include "exec.h"
#include "str_util.h"
#include "logger.h"


#include <fstream>
#include <iomanip>

#include <cstdlib>
#include <cctype>
#include <assert.h>

#if defined(_WIN32) || defined(_WIN64)
  // windows
  #include <direct.h>
  #include <windows.h>
  //#include <winbase.h>
  #include <time.h>
#else
  // on *nix
  #include <unistd.h>
  #include <fcntl.h>
  #include <signal.h>
  #include <sys/stat.h>
  #include <sys/types.h>
  #include <sys/wait.h>
  #include <sys/time.h>
#endif

namespace cosa {

using namespace sygus;

/// Append two path (you have to decide whether it is / or \)
std::string os_portable_append_dir(const std::string& dir1,
                                   const std::string& dir2) {
  std::string sep;
#if defined(_WIN32) || defined(_WIN64)
  // on windows
  sep = "\\";
#else
  // on *nix
  sep = "/";
#endif
  auto str1 = dir1;
  auto str2 = dir2;
  if (!StrEndsWith(str1, sep))
    str1 += sep;
  if (StrStartsWith(dir2, sep)) {
    str2 = dir2.substr(1);
  }
  return str1 + str2;
}

#if defined(__unix__) || defined(unix) || defined(__APPLE__) || defined(__MACH__) || defined(__linux__) || defined(__FreeBSD__)

volatile sig_atomic_t child_pid;
volatile sig_atomic_t shared_time_out;

void parent_alarm_handler(int signum) {
  if (child_pid != 0) {
    kill(-child_pid, SIGTERM);
    shared_time_out = 1;
  }
}
#endif

#if defined(_WIN32) || defined(_WIN64)
  #if defined(_MSC_VER) || defined(_MSC_EXTENSIONS)
    #define DELTA_EPOCH_IN_MICROSECS  11644473600000000Ui64
  #else
    #define DELTA_EPOCH_IN_MICROSECS  11644473600000000ULL
  #endif

  struct timezone
  {
    int  tz_minuteswest; /* minutes W of Greenwich */
    int  tz_dsttime;     /* type of dst correction */
  };

  int gettimeofday(struct timeval *tv, struct timezone *tz)
  {
    FILETIME ft;
    unsigned __int64 tmpres = 0;

    if (NULL != tv)
    {
      GetSystemTimeAsFileTime(&ft);

      tmpres |= ft.dwHighDateTime;
      tmpres <<= 32;
      tmpres |= ft.dwLowDateTime;

      /*converting file time to unix epoch*/
      tmpres -= DELTA_EPOCH_IN_MICROSECS;
      tmpres /= 10;  /*convert into microseconds*/
      tv->tv_sec = (long)(tmpres / 1000000UL);
      tv->tv_usec = (long)(tmpres % 1000000UL);
    }

    ILA_ERROR_IF(tz != NULL) << "Not implemented: timezone feature.";
    return 0;
  }

#endif

exec_result_t timed_execute(
  const std::vector<std::string> & cmdargs,
  const std::string & redirect_output_file,
  exec_redirect_t rdt,
  unsigned timeout,
  const std::string & pid_file_name )
{
  int pipefd[2];
  exec_result_t _ret;
  struct timeval Time1,Time2; // count the time

  _ret.seconds = 0;
  _ret.timeout = false;

  auto cmdline = Join(cmdargs, ",");
  
  assert(!cmdargs.empty());

#if defined(_WIN32) || defined(_WIN64)
  #error "Not yet supported on windows."
#else
  // set up the pipe to transfer subprocess's information before exec
  // so close on exec
  gettimeofday(&Time1, NULL);

#if defined(__linux__)
  pipe2(pipefd, O_CLOEXEC); // pipe2 is linux only feature!
#elif defined(__unix__) || defined(unix) || defined(__APPLE__) || defined(__MACH__) ||  defined(__FreeBSD__)
  pipe(pipefd);
#endif

  // on *nix, spawn a child process to do this
  pid_t pid = fork();

  if (pid == -1) {
    _ret.failure = exec_result_t::FORK;
    // not able to create no process
    return _ret;
  }

  // now fork ...
  if (pid == 0) { // child process

    if(timeout != 0) // only if we want to have the time-out feature
      setpgid(0,0); // creates a new proces group

    close(pipefd[0]); // close the read end
    #if !defined(__linux__)
    fcntl(pipefd[1], F_SETFD, FD_CLOEXEC); // close pipe on exec
    #endif

    unsigned char report_to_parent;

    // The child
    // will replace the image and execute the bash
    logger.log(1, "Execute subprocess: [" + cmdline + "]");
    if (! redirect_output_file.empty()) {
      logger.log(1, "Redirect to: " + redirect_output_file );
      
      int fd;
      fd = open(redirect_output_file.c_str(), O_WRONLY | O_CREAT | O_TRUNC , S_IRUSR | S_IWUSR );
      if (fd < 0) {
        logger.log(0, "Failed to open " + redirect_output_file);
        perror(NULL);
        report_to_parent = exec_result_t::PREIO;
        write(pipefd[1], (void *) & report_to_parent, sizeof(report_to_parent));
        exit(1);
      }
      if (rdt & exec_redirect_t::STDOUT)
        dup2(fd, STDOUT_FILENO);
      if (rdt & exec_redirect_t::STDERR)
        dup2(fd, STDERR_FILENO);
      close(fd);
    }

    // this is memory leak, but I have no other way...
    // hope this will be reclaimed by OS
    // + 1 for NULL

    const int MAX_ARG = 64;
    char * argv[MAX_ARG];
    if (cmdargs.size() >= MAX_ARG) {
      report_to_parent = exec_result_t::ARG;
      write(pipefd[1], (void *) & report_to_parent, sizeof(report_to_parent));
      exit(1);
    }

    for(auto it = cmdargs.begin(); it != cmdargs.end(); ++ it) {
      // this is memory leak, but what can I do ?
      size_t len = it->size();
      argv[it-cmdargs.begin()] = new char[len + 1];
      strncpy(argv[it-cmdargs.begin()], it->c_str(), len );
      argv[it-cmdargs.begin()][len] = '\0';
    }
    argv[ cmdargs.size() ] = NULL;

    report_to_parent = exec_result_t::NONE;
    write(pipefd[1], (void *) & report_to_parent, sizeof(report_to_parent));

    int ret = execvp(cmdargs[0].c_str(), argv);
    // if not successful
    if (ret == -1) {
      report_to_parent = exec_result_t::EXEC;
      write(pipefd[1], (void *) & report_to_parent, sizeof(report_to_parent));
    }
    close(pipefd[1]);
    exit(ret);
  } else {
    // The parent will wait for its end
    int infop;
    unsigned char child_report;
    struct sigaction new_act;
    struct sigaction old_act;
    static_assert(sizeof(child_report) == 1, "Expect child_report to be of 1 byte");

    close(pipefd[1]); // close the write end
    auto readlen = read(pipefd[0], (void *) &child_report, sizeof(child_report)); /* Flawfinder: ignore */
    /*
    Justifications:
    - There is no loop.
    - This is not a typical C string, and we don't rely on the ending '\0'
    - It will read at most 1 byte (guarded by the static assert above)
    */

    if(readlen == -1 || readlen != sizeof(child_report)) {
      _ret.failure = exec_result_t::PREIO ;
      close(pipefd[0]);
      return _ret;
    }
    if (child_report != exec_result_t::NONE) {
      // the child has error before exec
      _ret.failure = static_cast<exec_result_t::_failure>( child_report) ;
      close(pipefd[0]);
      return _ret;
    }

    child_pid = pid;

    if (!pid_file_name.empty()) {
      std::ofstream fout(pid_file_name);
      fout << child_pid << std::endl;
    }
    // set alarm
    if(timeout != 0) {
      shared_time_out = 0;
      new_act.sa_handler = parent_alarm_handler;
      sigemptyset (&new_act.sa_mask);
      new_act.sa_flags = 0;

      sigaction(SIGALRM, &new_act, &old_act);
      alarm(timeout);
    }
    // wait for sub-process
    int wait_pid_res = waitpid(pid, &infop, 0);

    gettimeofday(&Time2, NULL);
    _ret.seconds =
      (
        (Time2.tv_usec + Time2.tv_sec*1000000.0) -
        (Time1.tv_usec + Time1.tv_sec*1000000.0) ) / 1000000.0;

    if(timeout != 0) {
      alarm(0); //cancel if previously set
      sigaction(SIGALRM, &old_act, NULL); // restore the old one
    }

    if (timeout == 0 && wait_pid_res == -1) {
      _ret.failure = exec_result_t::WAIT;
      perror(NULL);
      close(pipefd[0]);
      return _ret;
    }

    if (wait_pid_res != -1)
      _ret.subexit_normal = WIFEXITED(infop);

    // read again, if exec suceeded, it should be EOF (read will fail)
    int sec_read = read(pipefd[0], (void *) &child_report, sizeof(child_report)); /* Flawfinder: ignore */
    /*
    Justifications:
    - There is no loop.
    - This is not a typical C string, and we don't rely on the ending '\0'.
    - It will read at most 1 byte (guarded by the static assert above).
    - We are not using the read data at all.
    */
    child_report = 0; // to make static analyzer happy
    if (sec_read != 0 && sec_read != -1) { // not eof
      _ret.failure = exec_result_t::EXEC;
      close(pipefd[0]);
      return _ret;
    }

    _ret.ret = WEXITSTATUS(infop);
    _ret.failure = exec_result_t::NONE;
    _ret.timeout = timeout != 0 && shared_time_out;


    if (!pid_file_name.empty()) {
      std::ofstream fout(pid_file_name);
      fout << 0 << std::endl;
    }

    close(pipefd[0]);
    return _ret;
  } // end of parent
#endif
} // end of os_portable_execute

} // namespace cosa

