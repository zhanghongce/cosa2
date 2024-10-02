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


Model * ModelLemmaManager::new_model(const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset) {
  cube_allocation_pool.push_back(new Model(solver(),varset));
  return cube_allocation_pool.back();
}

void ModelLemmaManager::register_new_model(Model * m) {
  assert (m);
  cube_allocation_pool.push_back(m);
}


Lemma * ModelLemmaManager::new_lemma(
  const smt::Term & expr, Model * cex, LCexOrigin origin) {
  lemma_allocation_pool.push_back(new Lemma(expr, cex, origin));
  return lemma_allocation_pool.back();
}


} // namespace pono
