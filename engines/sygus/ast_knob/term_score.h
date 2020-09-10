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
 ** \brief The term scores for predicates (will help decide removing order)
 **
 ** 
 **/

#include "walker.h"

namespace cosa {

namespace unsat_enum {

class TermScore : public Walker {
public:
  // ----------- TYPE --------------- //
  struct term_score_t {
    unsigned score;
    term_score_t(unsigned s) : score(s) {}
  };
  
  typedef std::unordered_map<smt::Term, term_score_t> score_map_t;

  static void ClearCache() { scores_.clear(); }
  static unsigned GetScore(const smt::Term & t);
    // find in cache, if not launch a wa
  
  TermScore() {} // do nothing
  
protected:
  static score_map_t scores_;
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;

}; // ParentExtract


} // namespace unsat_enum

} // namespace cosa

