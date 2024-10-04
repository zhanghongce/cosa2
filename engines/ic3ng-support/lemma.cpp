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
  for (auto vp : cube_var_info_allocation_pool)
    delete vp.second;
}

// Model * ModelLemmaManager::new_model() {
//   cube_allocation_pool.push_back(new Model);
//   return cube_allocation_pool.back();
// }


Model * ModelLemmaManager::new_model(const std::unordered_map <smt::Term,std::vector<std::pair<int,int>>> & varset) {
  std::unordered_set<smt::Term> varset_noslice;
  Model::compute_varset_noslice(varset, varset_noslice);
  std::string hashstring = Model::compute_vars_noslice_canonical_string(varset_noslice);
  auto pos = cube_var_info_allocation_pool.find(hashstring);
  if (pos == cube_var_info_allocation_pool.end()) {
    auto res = cube_var_info_allocation_pool.emplace(
      hashstring,
      new PerVarInfo(std::move(varset_noslice),std::move(hashstring)));
    assert(res.second); // insertion must be successful
    pos = res.first;
  }

  cube_allocation_pool.push_back(new Model(solver(),varset, pos->second));
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
