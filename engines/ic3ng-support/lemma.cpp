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
}

Model * ModelLemmaManager::new_model() {
  cube_allocation_pool.push_back(new Model);
  return cube_allocation_pool.back();
}

void ModelLemmaManager::register_new_model(Model * m) {
  assert (m);
  cube_allocation_pool.push_back(m);
}


} // namespace pono
