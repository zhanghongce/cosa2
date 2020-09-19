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
 ** \brief To BTOR to CHC Base class
 **
 **
 **/
 
 
#pragma once

#include <iostream>

namespace cosa {

class ChcPrinterBase {

public:
  virtual void Export(std::ostream & os) const = 0;
  virtual ~ChcPrinterBase() {}
};

} // namespace cosa


