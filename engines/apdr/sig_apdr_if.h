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
 ** \brief Signal handling and APDR's dumping interface
 **
 ** 
 **/
 
#pragma once

#include <iostream>

namespace cosa {
 
class SignalPDRInterface {

public:

  virtual void dump_frames(std::ostream & os) const = 0;

}; // class SignalPDRInterface

} // end of namespace cosa

