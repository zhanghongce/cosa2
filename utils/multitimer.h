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
 ** \brief Multi-channel timer
 **
 ** 
 **/
 
#pragma once

#include <string>
#include <map>
#include <chrono>
#include <iostream>

namespace cosa {

template <class T>
class MultiChannelTimer {
// typedefs
  using nanoseconds = std::chrono::nanoseconds;
  using milliseconds = std::chrono::milliseconds;
  typedef std::chrono::high_resolution_clock clock;
  typedef std::chrono::time_point<clock> time_tp;

  struct EventInfo {
    bool run_at_least_once_flag;
    bool started;
    time_tp tstart;
    time_tp tend;
    T start_quant;
    T end_quant;

    float total_time;
    T total_quant;
    EventInfo() : run_at_least_once_flag(false), started(false), total_time(0), total_quant(0)  {}
  };
protected:
  std::map<std::string, EventInfo> events_;
  void ClearEvent(const std::string & event);
public:
  MultiChannelTimer() {}
  void RegisterEventStart(const std::string & event, const T & quant);
  void RegisterEventEnd(const std::string & event, const T & quant);
  void RegisterEventCount(const std::string & event, const T & quant);
  // tdiff, quantdiff, quantdiff/tdiff
  bool EventExists(const std::string & event);
  bool EventOccurSinceFlagClear(const std::string & event);
  void ClearEventFlag(const std::string & event);
  std::tuple<float, T, float> GetStatus(const std::string & event);
  std::tuple<float, T, float> GetTotal(const std::string & event);
  void DumpAllEvents(std::ostream & os) const;
}; // class MultiChannelTimer

// instantiate this template for long long
// template class MultiChannelTimer<long long>;

extern class MultiChannelTimer<long long> GlobalTimer;

} // namespace cosa

