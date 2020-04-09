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
 ** \brief some shortcut for STL containers
 **
 ** 
 **/

#pragma once

#include <algorithm>
#include <set>
#include <string>

// actually no use, because micros are not bound by namespace
// should only be included in .cpp
namespace cosa {

#define UNION(a, b, r)                                                         \
  (std::set_union((a).begin(), (a).end(), (b).begin(), (b).end(),              \
                  std::inserter((r), (r).end())))
#define INTERSECT(a, b, r)                                                     \
  (std::set_intersection((a).begin(), (a).end(), (b).begin(), (b).end(),       \
                         std::inserter((r), (r).end())))
#define DIFFERENCE(a, b, r)                                                    \
  (std::set_difference((a).begin(), (a).end(), (b).begin(), (b).end(),         \
                       std::inserter((r), (r).end())))
#define SYMDIFF(a, b, r)                                                       \
  (std::set_symmetric_difference((a).begin(), (a).end(), (b).begin(),          \
                                 (b).end(), std::inserter((r), (r).end())))

#define IN(e, s) ((s).find(e) != (s).end())
#define IN_p(e, s) ((s)->find(e) != (s)->end())

#define S_IN(sub, s) ((s).find(sub) != (s).npos)

}  // namespace cosa