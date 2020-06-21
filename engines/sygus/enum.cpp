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
 ** \brief The Enumerator
 **
 ** 
 **/

#include "enum.h"
#include "utils/term_analysis.h"

#include "utils/container_shortcut.h"

#include "engines/apdr/config.h"
#include <cassert>
#include <cmath>

// some helper functions
#define TERM_TRUE    (solver_->make_term(true))
#define NOT(x)       (solver_->make_term(smt::Not, (x)))
#define NOT_msat(x)  (msat_solver_->make_term(smt::Not, (x)))
#define EQ(x, y)     (solver_->make_term(smt::Equal, (x), (y)))
#define AND(x, y)    (solver_->make_term(smt::And, (x), (y)))
#define OR(x, y)     (solver_->make_term(smt::Or, (x), (y)))
#define IMPLY(x, y)  (solver_->make_term(smt::Implies, (x), (y)))
#define IFF(x, y)    (solver_->make_term(smt::Iff, (x), (y)))

namespace cosa {

namespace sygus_enum {

// --------------------  enum_status ----------------
bool enum_status::is_uninit() const {
  return (
  prev_predicate_num == 0 && prev_conjunction_depth == 0 &&
    curr_predicate_num == 0 && curr_conjunction_depth == 0 && 
    looping_indices.size() == 1 && looping_indices[0] == 0  );
}

void enum_status::init(uint64_t init_conj_depth) {
  assert( is_uninit() );
  curr_conjunction_depth = init_conj_depth;
  curr_predicate_num = predicate_list_btor.size();
} // init

void enum_status::step() {
  assert(!is_curr_round_finished());
  // carry style
  bool inc = false;
  for(auto & idx : looping_indices) {
    if (idx < curr_predicate_num-1) {
      ++ idx;
      inc = true;
      break;
    }
    idx = 0;
  }
  if (!inc)
    looping_indices.push_back(0);
  looping_sanity_check();
}

void enum_status::increase_both_conjunction_depth_and_predicate_num() {
  assert(is_curr_round_finished());
  assert(predicate_list_btor.size() == predicate_list_msat.size());
  assert(predicate_list_btor.size() > curr_predicate_num);

  prev_predicate_num = curr_predicate_num;
  prev_conjunction_depth = curr_conjunction_depth;
  
  ++ curr_conjunction_depth;
  curr_predicate_num = predicate_list_btor.size();
  
  looping_indices.clear();
  looping_indices.push_back(prev_predicate_num);
}

void enum_status::increase_conjunction_depth() {
  assert(is_curr_round_finished());
  prev_predicate_num = curr_predicate_num;
  prev_conjunction_depth = curr_conjunction_depth;

  ++ curr_conjunction_depth;
  looping_indices.clear();
  for (uint64_t idx = 0; idx < curr_conjunction_depth; ++ idx)
    looping_indices.push_back(0); // start from more elements
  // 0 is also okay, and it will be skipped anyway
}

void enum_status::increase_predicate_num() {
  assert(is_curr_round_finished());
  assert(predicate_list_btor.size() == predicate_list_msat.size());
  assert(predicate_list_btor.size() > curr_predicate_num);

  prev_predicate_num = curr_predicate_num;
  prev_conjunction_depth = curr_conjunction_depth;

  curr_predicate_num = predicate_list_btor.size();

  looping_indices.clear();
  looping_indices.push_back(prev_predicate_num);
  // 0 is also okay, and it will be skipped anyway
}

bool enum_status::is_curr_round_finished() const {
  looping_sanity_check();
  if (curr_predicate_num == 0)
    return true;
  if (looping_indices.size() != curr_conjunction_depth)
    return false;
  for(auto idx : looping_indices) {
    if(idx != curr_predicate_num-1)
      return false;
  }
  return true;
}

void enum_status::looping_sanity_check() const {
#ifndef NDEBUG
  assert(
    (prev_conjunction_depth < curr_conjunction_depth) ||
    (prev_predicate_num < curr_predicate_num)
  );
  assert(
    (prev_conjunction_depth <= curr_conjunction_depth) &&
    (prev_predicate_num <= curr_predicate_num)
  );
  assert(looping_indices.size() <= curr_conjunction_depth);
  for(auto idx : looping_indices) {
    if (curr_predicate_num == 0)
      assert (idx == 0);
    else
      assert(idx < curr_predicate_num);
  }
#endif
}

bool enum_status::skip_current_idx() const {
  if (looping_indices.size() > prev_conjunction_depth)
    return false;
  for (auto idx : looping_indices) {
    if (idx >= prev_predicate_num)
      return false;
  }
  return true;
}

void enum_status::dump() const {
  std::cout << prev_predicate_num;
  for (uint64_t p = 1; p < prev_conjunction_depth; ++ p)
    std::cout << "*" << prev_predicate_num;

  std::cout << " --- ";
  for(auto idx : looping_indices)
    std::cout << idx << ",";
  std::cout << " --->> ";
  
  std::cout << curr_predicate_num;
  for (uint64_t p = 1; p < curr_conjunction_depth; ++ p)
    std::cout << "*" << curr_predicate_num;
}

smt::Term enum_status::GetCandidateBtor(smt::SmtSolver & solver_) const {
  smt::Term ret = nullptr;
  for (auto idx : looping_indices ) {
    assert(idx < predicate_list_btor.size());
    if (ret == nullptr)
      ret = predicate_list_btor.at(idx);
    else
      ret = AND(ret, predicate_list_btor.at(idx));
  }
  return ret;
}

smt::Term enum_status::GetCandidateMsat(smt::SmtSolver & solver_) const {
  smt::Term ret = nullptr;
  for (auto idx : looping_indices ) {
    assert(idx < predicate_list_msat.size());
    if (ret == nullptr)
      ret = predicate_list_msat.at(idx);
    else
      ret = AND(ret, predicate_list_msat.at(idx));
  }
  return ret;
}

// --------------------  Enumerator ----------------

Enumerator::prop_pos_buf_t Enumerator::prop_enum_buf_;
Enumerator::cex_pos_buf_t  Enumerator::cex_enum_buf_;

Enumerator::prop_term_map_t Enumerator::prop_term_map_;
Enumerator::cex_term_map_t  Enumerator::cex_term_map_;

void Enumerator::ClearCache() {
  prop_enum_buf_.clear();
  cex_enum_buf_.clear();
  prop_term_map_.clear();
  cex_term_map_.clear();
}

uint64_t Enumerator::GetCurrentLevelMaxEffort() const {
  std::cout << "(" << enum_status_.curr_predicate_num << " ^ " << enum_status_.curr_conjunction_depth << ")" << std::endl;
  return (
    std::pow(enum_status_.curr_predicate_num, enum_status_.curr_conjunction_depth)
    - 
    std::pow(enum_status_.prev_predicate_num, enum_status_.prev_conjunction_depth)
  );
}

bool Enumerator::is_valid(const smt::Term & e) {
  solver_->push();
  solver_->assert_formula(NOT(e));
  auto result = solver_->check_sat();
  solver_->pop();
  return !(result.is_sat());
}
  
bool Enumerator::a_implies_b(const smt::Term & a, const smt::Term & b) {
  return is_valid(IMPLY(a,b));
}
  
Enumerator::Enumerator(
    btor_var_to_msat_t btor_var_to_msat_func,
    to_next_t to_next_func,
    smt::SmtSolver & btor_solver,
    smt::SmtSolver & msat_solver,
    const smt::Term & T_btor, const smt::Term & Init_btor, const smt::Term & Fprev_btor,
    const std::vector<Model *> & cexs, const std::vector<Model *> & facts,
    const smt::Term & prop_btor,
    const sygus::SyntaxStructure & syntax ):
    btor_var_to_msat_(btor_var_to_msat_func),
    to_next_(to_next_func),
    solver_(btor_solver), msat_solver_(msat_solver),
    trans_(T_btor), init_(Init_btor), prev_(Fprev_btor),
    cexs_(cexs), facts_(facts), prop_(prop_btor),
    syntax_(syntax), syntax_struct_(syntax.GetSyntaxConstruct()),
    use_cex_(!cexs.empty()),
    width_term_table_(SetupInitTermList()),
    enum_status_(SetUpEnumStatus()),
    predicate_list_btor_(enum_status_.predicate_list_btor),
    predicate_list_msat_(enum_status_.predicate_list_msat)
{
  // SetupInitialPredicateListAndEnumStatus
  // term table dump
  PrintWidthTermTable(width_term_table_);

  if (enum_status_.is_uninit()) {
    PopulatePredicateListsWithTermsIncr();
    enum_status_.init(GlobalAPdrConfig.STARTING_CONJ_DEPTH);
  } else if (enum_status_.is_curr_round_finished()) {
    MoveToNextLevel();
  } // else will continue to enum on this
}


enum_status & Enumerator::SetUpEnumStatus() {
  if(use_cex_) {
    assert(cexs_.size() == 1);
    Model * cex = cexs_.at(0);
    return cex_enum_buf_[cex];
    // will create, but need to take care of the size of curr_s anyway
  }
  else {
    return prop_enum_buf_[prop_];
  }
  assert (false); // should not be reachable
} // Enumerator::SetUpEnumStatus()

Enumerator::width_term_table_t & Enumerator::SetupInitTermList() {
  if(use_cex_) {
    assert(cexs_.size() == 1);
    Model * cex = cexs_.at(0);
    auto pos = cex_term_map_.find(cex);
    if (pos != cex_term_map_.end())
      return pos->second;
    // now create the index
    auto & w2symbols = cex_term_map_[cex];
    // now collect symbols
    for (auto && v_val : cex->cube ) {
      const auto & v = v_val.first;
      assert ( v->is_symbolic_const() );
      uint64_t width = sygus::get_width_of_var(v);
      w2symbols[width].terms.push_back(std::make_pair(v, btor_var_to_msat_(v)));
    }
    for (auto & w_term_pair : w2symbols)
      w_term_pair.second.n_vars = w_term_pair.second.terms.size();

    PopulateTermTableWithConstants(w2symbols);
    PopulateTermTableWithUnaryOp(w2symbols);
    PopulateTermTableWithBinaryOp(w2symbols);
    PopulateTermTableWithExtractOpSyntaxDependentVars(w2symbols); // no use now
    return w2symbols;
  } else {
    auto pos = prop_term_map_.find(prop_);
    if (pos != prop_term_map_.end())
      return pos->second;

    smt::UnorderedTermSet all_symbols;
    get_free_symbols(prop_, all_symbols);

    width_term_table_t & w2symbols = prop_term_map_[prop_]; // will create
    for (auto && v : all_symbols) {
      uint64_t width = sygus::get_width_of_var(v);
      w2symbols[width].terms.push_back(std::make_pair(v, btor_var_to_msat_(v))); // will create
    }
    for (auto & w_term_pair : w2symbols)
      w_term_pair.second.n_vars = w_term_pair.second.terms.size();

    PopulateTermTableWithConstants(w2symbols);
    PopulateTermTableWithUnaryOp(w2symbols);
    PopulateTermTableWithBinaryOp(w2symbols);
    PopulateTermTableWithExtractOpSyntaxDependentVars(w2symbols); // no use now
    return w2symbols;
  }
  assert (false); // should not be reachable
} // SetupInitTermList

 //  initial population of tables 
void Enumerator::PopulateTermTableWithConstants(width_term_table_t & table) {
  // width -> vars and constants and then apply comps on them
  // output: predicate_list_btor_, predicate_list_msat_

  // SetupInitTermList already set up vars
  // add constants from grammar
  std::unordered_set<std::string> bool_consts = {"true", "false"};
  std::unordered_set<std::string> bv1_consts = {"#b0", "#b1"};
  // you can add more enumeration if wanted

  for (const auto & w_syntax : syntax_struct_ ) {
    uint64_t width = w_syntax.first;
    const auto & syntax = w_syntax.second;
    const std::unordered_set<std::string> & cnsts_set
      = (width == 0) ? bool_consts : (
        (width == 1) ? bv1_consts  : (
        syntax.constants));
      
    for (const auto & c: cnsts_set) {
      table[width].terms.push_back(std::make_pair(
        sygus::smt_string_to_const_term(c, solver_),
        sygus::smt_string_to_const_term(c, msat_solver_)
        ));
      table[width].consts_string.insert(
        table[width].terms.back().first->to_string());
    }
  }

  for (auto & w_term_pair : table)
    w_term_pair.second.n_consts_vars = w_term_pair.second.terms.size();

} // Enumerator::SetupInitialTermTable

void Enumerator::PopulateTermTableWithUnaryOp(width_term_table_t & terms_table) {
  for (auto && w_syntax : syntax_struct_ ) {
    uint64_t width = w_syntax.first;
    auto & syntax = w_syntax.second;
    if (!IN(width, terms_table))
      continue; // no such width, skip
    auto & terms = terms_table.at(width);
    auto start = terms.prev_unary_pointer;
    auto end = terms.terms.size();

    if(terms.n_vars == 0 && end == terms.n_consts_vars) {
      terms.prev_unary_pointer = end;
      continue; // no vars captured for this, and no other terms to work on
    }

    for (auto && op: syntax.op_unary) {
      auto smt_op = smt::Op(op);
      for(auto idx = start; idx < end; ++ idx) {
        auto btor_new_term = solver_->make_term(smt_op, terms.terms.at(idx).first);
        if (btor_new_term->is_value()) {
            auto v = btor_new_term->to_string();
            if (terms.consts_string.find(v) != terms.consts_string.end())
              continue; // skip this
            terms.consts_string.insert(v);
          }
        else if (btor_new_term->is_symbolic_const())
          continue; // will not add vars

        terms.terms.push_back(
          std::make_pair(
            btor_new_term, // btor_term
            msat_solver_->make_term(smt_op, terms.terms.at(idx).second) // msat_term
        ));
      }
    }
    terms.prev_unary_pointer = terms.terms.size(); // no need to neg neg (double cancellation)
  }  
} // PopulateTermTableWithUnaryOp


void Enumerator::PopulateTermTableWithBinaryOp(width_term_table_t & terms_table) {
  for (auto && w_syntax : syntax_struct_ ) {
    uint64_t width = w_syntax.first;
    auto & syntax = w_syntax.second;
    if (!IN(width, terms_table))
      continue; // no such width, skip
    auto & terms = terms_table.at(width);

    uint64_t start = 0;
    auto prev_pos = terms.prev_binary_pointer;
    auto end = terms.terms.size();

    if(terms.n_vars == 0 && end == terms.n_consts_vars) {
      terms.prev_binary_pointer = end;
      continue; // no vars capture for this
    }

    for (auto && op: syntax.op_binary) {
      auto smt_op = smt::Op(op);
      bool symmetry = sygus::is_primop_symmetry(op);
      for(auto idx1 = start; idx1 < end; ++ idx1) { // a-b and b-a
        for(auto idx2 = ( idx1 < prev_pos ? prev_pos : 
            (symmetry ? idx1 : start)) ; 
          idx2 < end; ++ idx2) {
          assert(!( idx1 < prev_pos && idx2 < prev_pos )); // no repetition
          auto btor_new_term = solver_->make_term(smt_op, terms.terms.at(idx1).first, terms.terms.at(idx2).first);
          if (btor_new_term->is_value()) {
            auto v = btor_new_term->to_string();
            if (terms.consts_string.find(v) != terms.consts_string.end())
              continue; // skip this
            terms.consts_string.insert(v);
          }
          else if (btor_new_term->is_symbolic_const())
            continue; // will not add vars
            
          terms.terms.push_back(  
          std::make_pair(
            btor_new_term,
            msat_solver_->make_term(smt_op, terms.terms.at(idx1).second, terms.terms.at(idx2).second)));
        } // for idx2
      } // for idx1
    } // for each op

    terms.prev_binary_pointer = end;
  } // for (auto && w_syntax : syntax_struct_ )
} // PopulateTermTableWithBinaryOp

// only one shot
void Enumerator::PopulateTermTableWithExtractOpAllWidthVars(width_term_table_t & terms_table) {
  for(auto && width_terms_pair : terms_table) {
    auto width = width_terms_pair.first;
    if(width == 0 || width == 1)
      continue;
    auto terms = width_terms_pair.second;
    for (decltype(width) widx = 0; widx < width; ++widx) { // extract
      auto op = smt::Op(smt::PrimOp::Extract,widx,widx);
      for (size_t idx = 0; idx < terms.n_vars; ++idx) {
        terms_table[1].terms.push_back(
        std::make_pair(
          solver_->make_term(op, terms.terms.at(idx).first),
          msat_solver_->make_term(op, terms.terms.at(idx).second)));
      } // for each var
    } // for diff extract
  } // for each width
} // PopulateTermTableWithExtractOpAllWidthVars


// only one shot
void Enumerator::PopulateTermTableWithExtractOpSyntaxDependentVars(width_term_table_t & terms_table) {
  /* TODO:
  for(auto && width_terms_pair : terms_table) {
    auto width = width_terms_pair.first;
    if(width == 0 || width == 1)
      continue;
    auto syntax_pos = syntax_struct_.find(width);
    if (syntax_pos == syntax_struct_.end())
      continue; // no need to 
  } // for each width*/
} // PopulateTermTableWithExtractOpSyntaxDependentVars




bool Enumerator::is_predicate_const(const smt::Term & t) {
  {
  solver_->push();
    solver_->assert_formula(t);
    auto r = solver_->check_sat();
  solver_->pop();
  if (r.is_unsat()) // is always false
    return true;
  }
  {
  solver_->push();
    solver_->assert_formula(NOT(t));
    auto r = solver_->check_sat();
  solver_->pop();
  if (r.is_unsat()) // is always true
    return true;
  }
  return false;
} // is_predicate_const

bool Enumerator::is_predicate_implicable(const smt::Term & t) {
  if(use_cex_) {
    // cex should imply this
    auto cex_p = cexs_[0]->to_expr_btor(solver_);
    solver_->push();
      solver_->assert_formula(cex_p); // cex_p , but not t
      solver_->assert_formula(NOT(t)); //
      auto r = solver_->check_sat();
    solver_->pop();
    if (r.is_sat())
      return false;
    return true;
  } // else not using use_cex_
    solver_->push();
      solver_->assert_formula(NOT(prop_)); // cex_p , but not t
      solver_->assert_formula(NOT(t)); //
      auto r = solver_->check_sat();
    solver_->pop();
    if (r.is_sat())
      return false;
    return true;
} // is_predicate_implicable

bool Enumerator::init_imply(const smt::Term & c) {
  solver_->push();
    solver_->assert_formula(init_);
    solver_->assert_formula(NOT(c));
    auto r = solver_->check_sat();
  solver_->pop();
  return !(r.is_sat());
}

bool Enumerator::compatible_w_facts(const smt::Term & c) {
  if(facts_.empty()) // shortcut
    return true;
  
  bool compatible = true;
  solver_->push();
    solver_->assert_formula(c);
    for (auto f_ptr : facts_) {
      solver_->push();
      solver_->assert_formula(f_ptr->to_expr_btor(solver_));
      compatible = solver_->check_sat().is_sat();
      solver_->pop();
      
      if(!compatible)
        break;
    }
  solver_->pop();
  return compatible;
}

bool Enumerator::F_T_and_P_imply_Pprime(const smt::Term & c) {
  solver_->push();
    solver_->assert_formula(prev_);
    solver_->assert_formula(c);
    solver_->assert_formula(trans_);
    solver_->assert_formula(NOT(to_next_(c)));
    auto r = solver_->check_sat();
  solver_->pop();
  return !(r.is_sat());
} // F_T_and_P_imply_Pprime


// is_const
// predicate_implicable

const std::unordered_set<smt::PrimOp> &  Enumerator::GetCompForWidth(uint64_t w) {
 // TODO: decide what comp to include

 static const std::unordered_set<smt::PrimOp>  default_eq 
  = {smt::PrimOp::Equal,  smt::PrimOp::Distinct}; //,
 static const std::unordered_set<smt::PrimOp>  default_eqlte 
  = {smt::PrimOp::Equal,  smt::PrimOp::Distinct,
     smt::PrimOp::BVUlt, smt::PrimOp::BVUle};
 static std::unordered_set<smt::PrimOp> custom_comp;

  const std::unordered_set<smt::PrimOp> & default_comp = 
    GlobalAPdrConfig.COMP_DEFAULT_BVULTULE ? default_eqlte : default_eq;
  
  if(GlobalAPdrConfig.COMP_DEFAULT_OVERRIDE)
    return default_comp;
  
  // extract from syntax
  auto pos = syntax_struct_.find(w);
  if (pos == syntax_struct_.end())
    return default_comp;
  custom_comp.clear();
  custom_comp.insert(smt::PrimOp::Equal);
  custom_comp.insert(smt::PrimOp::Distinct);

  if (pos->second.op_comp.find(smt::PrimOp::BVUlt) != pos->second.op_comp.end())
    custom_comp.insert(smt::PrimOp::BVUlt);

  if (pos->second.op_comp.find(smt::PrimOp::BVUle) != pos->second.op_comp.end())
    custom_comp.insert(smt::PrimOp::BVUle);

  return (custom_comp);
}

// terms to predicates
void Enumerator::PopulatePredicateListsWithTermsIncr() {
  assert (predicate_list_btor_.size() == predicate_list_msat_.size());
  // Level n decision
  for (auto & width_term_pair : width_term_table_) {
    auto width = width_term_pair.first;
    const auto & terms = width_term_pair.second;
    auto nterms = terms.terms.size();
    if(terms.n_vars == 0 && (nterms - terms.n_consts_vars == 0) ) {
      width_term_pair.second.prev_comp_pointer = nterms;
      continue; // skip those without vars;
    }
    auto skip_pos = terms.prev_comp_pointer;
    // use width to index into grammer to find ops
    const auto & comp_op = GetCompForWidth(width);
    for (auto op : comp_op) {
      auto smt_op = smt::Op(op);
      bool symmetry = sygus::is_primop_symmetry(op);
      for (size_t idx1 = 0; idx1 < nterms; ++idx1 ) {
        for (size_t idx2 = (idx1 < skip_pos) ? skip_pos : 
              (symmetry ? idx1+1 : 0); // + 1 , no need for a == a, a < a or a <= a
             idx2 < nterms; ++ idx2) {
          if (idx1 < skip_pos && idx2 < skip_pos)
            continue;
          auto pred_btor = solver_->make_term(smt_op, 
            terms.terms.at(idx1).first,
            terms.terms.at(idx2).first);
          if (is_predicate_const(pred_btor))
            continue;
          if (!is_predicate_implicable(pred_btor))
            continue;
          auto pred_msat = msat_solver_->make_term(smt_op, 
            terms.terms.at(idx1).second,
            terms.terms.at(idx2).second);
          // std::cout << "Get pred: " << pred_msat->to_string() << std::endl;
          predicate_list_btor_.push_back(pred_btor);
          predicate_list_msat_.push_back(pred_msat);
        } // for idx2
      } // for idx1
    } // for each op

    width_term_pair.second.prev_comp_pointer = terms.terms.size();
  } // for each width

  assert (predicate_list_btor_.size() == predicate_list_msat_.size());
} // PopulatePredicateListsWithTermsIncr


void Enumerator::MoveToNextLevel() { // more predicates more in conjunction
  assert(enum_status_.is_curr_round_finished());
  if( enum_status_.curr_conjunction_depth == GlobalAPdrConfig.EXTRACT_DEGENERATE_THRESHOLD) {
    PopulateTermTableWithExtractOpAllWidthVars(width_term_table_);
    enum_status_.increase_both_conjunction_depth_and_predicate_num();
  } else {
    PopulateTermTableWithUnaryOp(width_term_table_);
    PopulateTermTableWithBinaryOp(width_term_table_);
    PopulatePredicateListsWithTermsIncr();
    enum_status_.increase_both_conjunction_depth_and_predicate_num();
  }
}


std::pair<smt::Term, smt::Term> Enumerator::EnumCurrentLevel(uint64_t bnd) {
  // here is the most interesting part
  assert(!enum_status_.is_curr_round_finished());
  uint64_t idx = 0;
  while(true) {
    while (enum_status_.skip_current_idx()) {
      enum_status_.step();
    } // ! enum_status_.skip_current_idx()
    if (enum_status_.is_curr_round_finished())
      return std::make_pair(nullptr,nullptr);
    if (bnd != 0 && idx > bnd)
      return std::make_pair(nullptr,nullptr);

    ++ idx;
    smt::Term raw_cand = enum_status_.GetCandidateBtor(solver_);
    smt::Term cand = NOT(raw_cand);
    if (!init_imply(cand)) {
      enum_status_.step();
      continue;
    }
    if (!compatible_w_facts(cand)) {
      enum_status_.step();
      continue;
    }
    if (!F_T_and_P_imply_Pprime(cand)) {
      enum_status_.step();
      continue;
    }
    // now we found
    smt::Term cand_msat = NOT_msat(enum_status_.GetCandidateMsat(msat_solver_));
    enum_status_.step();
    return std::make_pair(cand, cand_msat);
  } // while true
  assert (false);
  return std::make_pair(nullptr,nullptr);
} // EnumCurrentLevel






void Enumerator::PrintWidthTermTable(const width_term_table_t & tb) {
  for(const auto & width_terms_pair : tb) {
    auto width = width_terms_pair.first;
    const auto & terms_info = width_terms_pair.second;
    std::cout << "[Width = " << width << "]" << std::endl;
    std::cout << "[PU @ " << terms_info.prev_unary_pointer 
              << ", PB @ " << terms_info.prev_binary_pointer
              << ", PC @ " << terms_info.prev_comp_pointer<< "]" << std::endl;
    std::cout << "V : ";
    unsigned idx = 0;
    for (; idx < terms_info.n_vars; ++idx )
      std::cout << ((terms_info.terms.at(idx).first)->to_string()) << ",";
    std::cout << std::endl;

    std::cout << "C : ";
    for (; idx < terms_info.n_consts_vars; ++idx )
      std::cout << ((terms_info.terms.at(idx).first)->to_string()) << ",";
    std::cout << std::endl;

    std::cout << "T : ";
    for (; idx < terms_info.terms.size(); ++idx )
      std::cout << ((terms_info.terms.at(idx).first)->to_string()) << ",";
    std::cout << std::endl;
    std::cout << std::endl;
  }
}

void Enumerator::PrintEnumStatus(const enum_status & e) {
  e.dump();
}



} // namespace sygus_enum

} // namespace cosa

