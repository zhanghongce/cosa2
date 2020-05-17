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
 ** \brief Multi-alarm
 **
 ** 
 **/
 
#pragma once

namespace cosa {

typedef void (*alarm_callback_fn_t)(int);

void RegisterAlarmCallBack(unsigned idx, unsigned time, alarm_callback_fn_t call_back);

} // namespace cosa

