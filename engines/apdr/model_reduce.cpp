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
 ** \brief Model reduce
 **
 ** 
 **/


#include "apdr.h"

#include <queue>

namespace cosa {

class VarWidthLess {
public:
  bool operator()  (const smt::Term &l, const smt::Term &r) const {
    return l->get_sort()->get_width() < r->get_sort()->get_width();
  }
};

Model * Apdr::try_model_reduce(unsigned prevFidx,
  const std::vector<Model *> & models_to_block, const std::vector<Model *> & models_fact,
  bool remove_prop_in_prev_frame, bool use_init, FrameCache * fc) {
    
  if (models_to_block.size() != 1) {
    return NULL;
  }
  const cube_t & c = models_to_block.at(0)->cube;

  if (c.size() == 1) // will not try if size == 1
    return NULL;

  std::priority_queue<smt::Term, std::vector<smt::Term>, VarWidthLess> vars;
  for (auto && var_val_pair : c) {
    if (var_val_pair.first->get_sort()->get_width() > GlobalAPdrConfig.MSAT_INTERPOLANT_ENHANCE_VAR_WIDTH_THRESHOLD)
      vars.push(var_val_pair.first);
  }

  bool succ = false;
  Model * prev_model = new Model(*(models_to_block.at(0)));
  while(!vars.empty()) {
    // drop headv in new_model, clear model's cache
    // see solveTrans, if okay?
    // if okay, delete prev_model, prev = new_model
    // else delete new_model
    smt::Term headv = vars.top();
    vars.pop();

    Model * new_model = new Model(*(prev_model));
    bool erased = new_model->erase_var(headv);
    if ( ! erased ) {
      delete new_model;
      continue; // try next var
    }

    auto res = solveTrans(prevFidx, NULL /*prop_btor*/, NULL /*prop_msat*/,
      {new_model}, models_fact, remove_prop_in_prev_frame, use_init,
      false /*use_itp*/ , false /*pre state*/, false /*post state*/, fc);
    if (res.not_hold) { // failed
      delete new_model;
    } else {
      delete prev_model;
      prev_model = new_model;
      succ = true;
    }
  } // end of while

  if (succ) {
    register_new_model(prev_model);
    return prev_model;
  } // else

  delete prev_model;
  return NULL;
  
  // sort the sizes, stop at size N=5
  // try reduce one by one, if any one is reducible, remove and continue

} // end of try_model_reduce

} // namespace cosa

