/*********************                                                        */
/*! \file 
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce Zhang
 ** This file is part of the cosa2 project.
 ** Copyright (c) 2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term extractor
 **
 ** 
 **/
  
#pragma once

#include "walker.h"

#include <map>

namespace cosa {
  
namespace unsat_enum {

class TermExtractor : public Walker {
public:
  // ----------- TYPE --------------- //
  struct node_info_t {
    bool in;
    unsigned level;
    node_info_t() : in(false), level(0) {}
  };
  
  
  // ----------- CONSTRUCTOR --------------- //
  // if level > 0, then we will count level, otherwise, we don't care about the levels
  TermExtractor(const std::unordered_set<smt::Term> & varset, bool collect_constants, unsigned level,
      std::map<unsigned, std::vector<smt::Term>> & width_to_term_table,
      std::unordered_set<smt::Term> & all_terms_set) :
    related_vars_(varset), collect_constants_(collect_constants), level_(level),
    width_to_terms_(width_to_term_table), all_terms_(all_terms_set) { }
    
  //const std::map<unsigned, std::vector<smt::Term>> & GetTermsByWidth() const { return width_to_terms_; }
  //const std::unordered_set<smt::Term> & GetAllTerms() const { return all_terms_; }
  const std::map<unsigned, std::vector<smt::Term>> & GetConstants() const { return width_to_constants_; }
  
  // public method inherited: WalkDFS (*) /BFS
  
protected:
  std::unordered_map<smt::Term, node_info_t> walked_nodes_;
  const std::unordered_set<smt::Term> & related_vars_; // we will also bring in unrelated vars
  bool collect_constants_;
  unsigned level_;
  
  std::map<unsigned, std::vector<smt::Term>> & width_to_terms_;
  std::map<unsigned, std::vector<smt::Term>> width_to_constants_; // const is not needed, as you may not always need it
  std::unordered_set<smt::Term> & all_terms_;
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;

}; // class TermExtractor



class ParentExtract : public Walker {
public:
  // ----------- TYPE --------------- //
  typedef std::unordered_map<smt::Term, smt::UnorderedTermSet> parent_map_t;

  ParentExtract() {} // do nothing
  static void ClearCache() { parent_.clear(); }
  static const parent_map_t & GetParentRelation() {return parent_;}
  static bool RegisterNewParentRelation(const smt::Term &child, const smt::Term &parent) {
    auto ret = parent_[child].insert(parent);
    return ret.second;
  }
  
protected:

  std::unordered_set<smt::Term> walked_nodes_;
  static parent_map_t parent_;
  
  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;

}; // ParentExtract

class ConstantExtractor: public Walker {
public:
  // ----------- TYPE --------------- //
  typedef std::map<unsigned, std::vector<smt::Term>> width_constant_map_t;

  ConstantExtractor(width_constant_map_t & out,
    std::unordered_set<std::string> & cnstr_strs
    ) : width_constant_map(out), constants_strs_(cnstr_strs)  {}

protected:
  width_constant_map_t & width_constant_map;
  std::unordered_set<std::string> & constants_strs_;
  std::unordered_set<smt::Term> walked_nodes_;

  virtual bool Skip(const smt::Term & ast) override;
  virtual void PreChild(const smt::Term & ast) override;
  virtual void PostChild(const smt::Term & ast) override;

}; // ConstantExtractor

} // namespace unsat_enum

}  // namespace cosa

