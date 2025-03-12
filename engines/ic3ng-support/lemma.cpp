#include "lemma.h"

#include <cassert>

namespace pono
{
  

ModelLemmaManager::ModelLemmaManager() { }

ModelLemmaManager::~ModelLemmaManager() {
  for (auto lp : lemma_allocation_pool)
    delete lp;
  for (auto mp : cube_allocation_pool)
    delete mp;
  for (auto vp : cube_slicedvar_info_allocation_pool)
    delete vp.second;
  for (auto vp : cube_unslicevar_info_allocation_pool)
    delete vp.second;
}

// Model * ModelLemmaManager::new_model() {
//   cube_allocation_pool.push_back(new Model);
//   return cube_allocation_pool.back();
// }


Model * ModelLemmaManager::new_model(
  smt::UnorderedTermSet && slicedvarset, 
  smt::UnorderedTermSet && unslicedvarset,
  smt::TermVec && eqs) {
  std::string sliced_hashstring = Model::compute_vars_canonical_string(slicedvarset);
  auto pos = cube_slicedvar_info_allocation_pool.find(sliced_hashstring);
  if (pos == cube_slicedvar_info_allocation_pool.end()) {
    // try to find unsliced var
    std::string unsliced_hashstring = Model::compute_vars_canonical_string(unslicedvarset);
    auto pos_unsliced = cube_unslicevar_info_allocation_pool.find(unsliced_hashstring);
    if (pos_unsliced == cube_unslicevar_info_allocation_pool.end()) {
      // build unsliced var first;
      auto res = cube_unslicevar_info_allocation_pool.emplace(unsliced_hashstring,
        new PerUnslicedVarInfo(std::move(unslicedvarset), unsliced_hashstring));
      assert(res.second);
      pos_unsliced = res.first;
    }

    auto res = cube_slicedvar_info_allocation_pool.emplace(
      sliced_hashstring,
      new PerSlicedVarInfo(std::move(slicedvarset),sliced_hashstring, pos_unsliced->second));
    assert(res.second); // insertion must be successful
    pos = res.first;
  }

  cube_allocation_pool.push_back(new Model(std::move(eqs), pos->second));
  return cube_allocation_pool.back();
}

// void ModelLemmaManager::register_new_model(Model * m) {
//   assert (m);
//   cube_allocation_pool.push_back(m);
// }


Lemma * ModelLemmaManager::new_lemma(
  const smt::Term & expr, Model * cex, LCexOrigin origin, smt::TermVec && cube) {
  if (origin.is_must_block() || origin.is_may_block())
    assert(!cube.empty()); // this cannot be the default empty
  lemma_allocation_pool.push_back(new Lemma(expr, std::move(cube), cex, origin));
  return lemma_allocation_pool.back();
}


} // namespace pono
