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
 
#include "multitimer.h"
#include "container_shortcut.h"

#include <cassert>


namespace cosa {

// instantiate this template for long long
template class MultiChannelTimer<long long>;

template <class T> 
void MultiChannelTimer<T>::RegisterEventStart(const std::string & event, const T & quant) {
  auto & st = events_[event];
  assert (!st.started);
  st.started = true;  
  st.run_at_least_once_flag = true;
  st.tstart = clock::now();
  st.start_quant = quant;
}

template <class T> 
void MultiChannelTimer<T>::RegisterEventEnd(const std::string & event, const T & quant) {
  auto pos = events_.find(event);
  assert(pos != events_.end());
  (pos->second.tend) = clock::now();
  pos->second.end_quant = quant;
  assert (pos->second.started);
  pos->second.started = false;

  pos->second.total_quant += pos->second.end_quant - pos->second.start_quant;
  pos->second.total_time += (std::chrono::duration_cast<milliseconds>( pos->second.tend - pos->second.tstart ).count() ) / 1000.0f;
}


template <class T> 
void MultiChannelTimer<T>::RegisterEventCount(const std::string & event, const T & quant) {
  auto & st = events_[event];
  assert (!st.started);
  st.run_at_least_once_flag = st.run_at_least_once_flag  || (quant > 0);
  st.total_quant += quant;
}

template <class T> 
std::tuple<float, T, float> MultiChannelTimer<T>::GetStatus(const std::string & event) {
  auto pos = events_.find(event);
  assert(pos != events_.end());
  assert(!(pos->second.started));
  assert(pos->second.run_at_least_once_flag);
  auto diff (pos->second.tend - pos->second.tstart);
  T quant_diff = pos->second.end_quant-pos->second.start_quant;
  float tdiff = std::chrono::duration_cast<milliseconds>(diff).count() / 1000.0f;
  return std::make_tuple(tdiff, quant_diff, quant_diff/tdiff );
}


template <class T> 
std::tuple<float, T, float> MultiChannelTimer<T>::GetTotal(const std::string & event) {
  auto pos = events_.find(event);
  assert(pos != events_.end());
  T quant_diff = pos->second.total_quant;
  float tdiff = pos->second.total_time;
  return std::make_tuple(tdiff, quant_diff, quant_diff/tdiff );
}

template <class T> 
bool MultiChannelTimer<T>::EventExists(const std::string & event) {
  return (IN(event, events_));
}


template <class T> 
bool MultiChannelTimer<T>::EventOccurSinceFlagClear(const std::string & event) {
  if (!IN(event, events_))
    return false;
  return events_[event].run_at_least_once_flag;
}

template <class T> 
void MultiChannelTimer<T>::ClearEvent(const std::string & event) {
  events_.erase(event);
}

template <class T> 
void MultiChannelTimer<T>::ClearEventFlag(const std::string & event) {
  auto pos = events_.find(event);
  if(pos == events_.end())
    return;
  pos->second.run_at_least_once_flag = false;
}

class MultiChannelTimer<long long> GlobalTimer;

} // namespace cosa
