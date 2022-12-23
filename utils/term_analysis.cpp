/*********************                                                        */
/*! \file term_analysis.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Useful functions for term analysis.
**
**
**/

#include "assert.h"
#include "smt-switch/smt.h"
#include "smt-switch/utils.h"
#include "utils/exceptions.h"

using namespace smt;
using namespace std;

namespace pono {

// set of operators which cannot be predicates
// mostly boolean operators plus some special cases
// and the bit-vector versions for boolector
// boolean terms with these operators are not predicates
unordered_set<PrimOp> nonpred_ops({
    And,
    Or,
    Xor,
    Not,
    Implies,
    Ite,
    // Note: also including bit-vector operators for solvers that
    //       alias bool and bv of size 1
    //       should not make a difference for solvers that don't
    //       alias, because it will check if it's a boolean first.
    //       so this is just to make this method work for all solvers
    BVAnd,
    BVOr,
    BVXor,
    BVNand,
    BVNot,
    Extract  // otherwise boolector will count single-bit extracts
});

// helper functions

/** Helper function for get_combinations. Builds the output vector recursively
 *  @param options a sequence of non-empty vectors containing each option for
 * this position
 *  @param output vector (should start empty) - gets incrementally populated
 * with a flattened sequence of vectors with each option
 *  @param i the index this recursive function is currently working on
 *  NOTE: this is not the most performant implementation, but in practice we
 * don't expect too many options so this is not expected to be a bottleneck
 */
void get_combinations_helper(const vector<TermVec> & options,
                             vector<TermVec> & out,
                             size_t i)
{
  if (i == options.size()) {
    return;
  }

  if (i == 0) {
    if (!out.empty()) {
      throw PonoException("Expecting empty vector");
    }
    // need to initialize the vector
    for (auto c : options[i]) {
      out.push_back({ c });
    }
  } else {
    size_t orig_out_size = out.size();
    for (size_t j = 0; j < orig_out_size; ++j) {
      if (options[i].empty()) {
        throw PonoException("Each element of options must be non-empty");
      }

      for (int k = options[i].size() - 1; k >= 0; --k) {
        // each element of out should be the same length
        // exactly i because that's how far into the options we've gotten
        assert(out[j].size() == i);
        if (k != 0) {
          // copy the vector and add it to out with this option appended
          TermVec outj = out[j];
          outj.push_back(options[i][k]);
          out.push_back(outj);
        } else {
          // for element 0, just add it to the existing vector instead of
          // creating a new one NOTE: this is the last option we're appending so
          // we don't need to keep the old
          //       version of this vector
          out[j].push_back(options[i][k]);
        }
      }
    }
  }

  // recursive call
  get_combinations_helper(options, out, i + 1);
}

/** Generate all combinations of the terms in the vector
 *  e.g. if the input is
 *  [[v, w],
 *    [x],
 *    [y, z]
 *  ]
 *  then the output should be [[v, x, y], [v, x, z], [w, x, y], [w, x, z]]
 *  @param options a sequence of non-empty vectors containing each option for
 * this position
 *  @param a flattened sequence of vectors with each option
 */
vector<TermVec> get_combinations(const vector<TermVec> & options)
{
  vector<TermVec> out;
  get_combinations_helper(options, out, 0);
  return out;
}

// end helper functions

bool is_predicate(const Term & t, const Sort & boolsort, bool include_symbols)
{
  if (t->get_sort() != boolsort) {
    return false;
  }

  const Op & op = t->get_op();

  if (include_symbols && t->is_symbolic_const()) {
    return true;
  } else if (op.is_null()) {
    // cannot be a predicate with a null op unless including symbols
    return false;
  }

  assert(!op.is_null());
  if (nonpred_ops.find(op.prim_op) != nonpred_ops.end()) {
    // boolean operators cannot make predicates
    // also included extract because otherwise boolector
    // would include single-bit extracts
    return false;
  }

  TermVec children(t->begin(), t->end());

  // boolean terms that do not use a boolean combination operator are
  // predicates
  // one special case is equality between two booleans is not a predicate
  // this is an iff essentially
  if (op.prim_op == Equal && (*t->begin())->get_sort() == boolsort) {
    return false;
  }

  // if it made it through all the checks, then it's a predicate
  return true;
}

UnorderedTermSet get_free_symbols(const Term & term)
{
  UnorderedTermSet free_symbols;
  get_free_symbols(term, free_symbols);
  return free_symbols;
}


void get_leaves(const Term & term, UnorderedTermSet & leaves)
{
  TermVec to_visit({ term });
  UnorderedTermSet visited;

  Term t;
  while (!to_visit.empty()) {
    t = to_visit.back();
    to_visit.pop_back();

    if (visited.find(t) != visited.end()) {
      // cache hit
      continue;
    }
    visited.insert(t);

    for (const auto & tt : t) {
      to_visit.push_back(tt);
    }

    if (t->get_op().is_null()) {
      assert(t->is_symbol() || t->is_value());
      leaves.insert(t);
    }
  }
}


smt::Term name_changed(const smt::Term & input, const smt::UnorderedTermSet & varset, const SmtSolver & slv) {
  smt::UnorderedTermMap substitute_map;
  for(const auto & var: varset) {
    assert(var->is_symbol());
    auto sort = var->get_sort();
    auto var_middle =  var->to_string();
    auto pos1 = var_middle.find("|");
    if (pos1!=std::string::npos){
      var_middle = var_middle.erase(pos1,1);
    }
    auto pos2 = var_middle.find("|");
    if (pos2!=std::string::npos){
      var_middle = var_middle.erase(pos2,1);
    }
    // auto pos_reg = var_middle.find("register");
    // auto ps_left_paren = var_middle.find("[");
    // if (ps_left_paren!=std::string::npos){
    //   var_middle = var_middle.replace(ps_left_paren,1,"_");
    // }
    // auto ps_right_paren = var_middle.find("]");
    // if (ps_right_paren!=std::string::npos){
    //   var_middle = var_middle.replace(ps_right_paren,1,"_");
    // }
    std::string new_name;
    // if (pos_reg!=std::string::npos){
    //   new_name = "RTL.RTL__DOT__" + var_middle;
    // }
    // else{
    new_name = "RTL." + var_middle;
    // }
    auto new_var = slv->make_symbol(new_name, sort);
    substitute_map.emplace(var, new_var);
  }
  return slv->substitute(input, substitute_map);
}


void name_changed(const Term & term, Term & new_Term, smt::SmtSolver &solver)
{
  TermVec to_visit({ term });
  // SortKind sort;
  Term t;
  Term val;
  Term eq;
  Term term_wrapper;
  Term var_record;
  int count_var=0;
  int count_val=0;
  int not_count = 0;
  std::string var_wrapper;
  int var_width;
  int val_width;
  while (!to_visit.empty()) {
    t = to_visit.back();
    to_visit.pop_back();

    for (const auto & tt : t) {
      to_visit.push_back(tt);
    }

    if (t->get_op() == BVNot){
      not_count = 1;
    }
    if (t->get_op().is_null()) {
      assert(t->is_symbol() || t->is_value());
      auto sort = t->get_sort()->get_sort_kind();
      auto bit_width = t->get_sort()->get_width();

      if (t->is_symbol()){
        var_wrapper = "RTL." + t->to_string();
// auto sort = t->get_sort()->get_sort_kind();
        auto sort_new = solver->make_sort(sort,bit_width);
        term_wrapper = solver->make_symbol(var_wrapper,sort_new);
        if (bit_width == 1){
          var_record = term_wrapper;
        }  
        count_var = count_var + 1;
        var_width = bit_width;
      }
      else if (t->is_value()){
        auto sort_new = solver->make_sort(sort,bit_width);
        auto val_string = t->to_string(); 
        val_string = val_string.substr(2, val_string.size()-1);
        val = solver->make_term(val_string,sort_new,2);
        count_val = count_val + 1;
        val_width = bit_width;
      }
      
      if ((count_val == 1 )&&(count_var == 1)&&(var_width == val_width)){
                eq = solver->make_term(Equal, term_wrapper, val );
                if(new_Term == nullptr)
                {
                new_Term = eq;
                }
                else{
                  new_Term = solver->make_term(BVAnd, new_Term,eq);
                }
                count_val = 0;
                count_var = 0;
                not_count = 0;
      }
      /// The val may occur two times, which means that originally, they are 1 bit vector./////
      else{
                if((var_width != 1)) continue; 
                if (not_count ==1){
                  not_count = 0;
                  eq = solver->make_term(BVNot, var_record);
                }
                else{
                  eq = var_record;
                }
                if(new_Term == nullptr)
                {
                  new_Term = eq;
                }
                else{
                  new_Term = solver->make_term(BVAnd, new_Term,eq);
                }
                count_var = count_var -1;
                assert(count_var = 1);
      }
    }
  }
  new_Term = solver -> make_term(BVNot, new_Term);
  cout<<new_Term<<endl;
}

void smt_lib2_front(const UnorderedTermSet &out,std::string & sort_list){
      std::unordered_map<smt::Term,smt::Sort> symbols_mapping;
      for (const auto &var: out){
          std::cout<<var<<std::endl;
          auto var_sort = var->get_sort();
          symbols_mapping.insert(pair<Term,Sort> (var,var_sort));
      }
      const auto length = symbols_mapping.size();
      int count = 0; 
      for (const auto &symbols: symbols_mapping){
        if (count != length -1)
        {
        sort_list = sort_list + "("  + symbols.first->to_string()  + " " + symbols.second->to_string() + ")" +" ";
        cout<<sort_list<<endl;
        count = count + 1;
        }
        else{
          sort_list = sort_list + "(" + symbols.first->to_string() + " " + symbols.second->to_string() + ")";
          cout<<sort_list<<endl;
        }
      }
}
void get_predicates(const SmtSolver & solver,
                    const Term & term,
                    UnorderedTermSet & out,
                    bool include_symbols,
                    bool search_subterms,
                    bool split_ites)
{
  // NOTE: this is better than checking the SortKind of a sort
  //       some solvers alias sorts and might return a SortKind
  //       of BV (with width 1) for a boolean
  //       But, even those solvers will be consistent and a term
  //       t with boolean sort will satisfy
  //       t->get_sort() == boolsort
  //       even if
  //       t->get_sort()->get_sort_kind() != BOOL
  Sort boolsort = solver->make_sort(BOOL);

  TermVec to_visit({ term });
  UnorderedTermSet visited;

  Term t;
  while (to_visit.size()) {
    t = to_visit.back();
    assert(t);  // non-null term
    to_visit.pop_back();

    if (visited.find(t) == visited.end()) {
      visited.insert(t);

      TermVec children(t->begin(), t->end());
      // later we will want to know which children are ITEs (if any)
      unordered_set<size_t> ite_indices;
      // add children to stack
      Term c;
      for (size_t i = 0; i < children.size(); ++i) {
        c = children[i];
        if (c->get_op() == Ite) {
          ite_indices.insert(i);
        }
      }

      if (!search_subterms && t->get_sort() != boolsort) {
        // not a candidate for predicates
        continue;
      }

      if (t->is_value()) {
        // values are not predicates
        continue;
      }

      bool is_pred = false;
      // special case for ITE children
      // Note: we're trying to never include an ITE in a predicate
      //       so if we get y = ite(x < 10, x+1, 0), we want to add
      //       y = x+1 and y = 0 as the predicates instead of the
      //       whole formula
      if (split_ites && ite_indices.size()) {
        vector<TermVec> options;
        for (size_t i = 0; i < children.size(); ++i) {
          if (ite_indices.find(i) != ite_indices.end()) {
            TermVec ite_children(children[i]->begin(), children[i]->end());
            assert(ite_children.size() == 3);
            options.push_back({ ite_children[1], ite_children[2] });
            // look for predicates in the ite condition
            to_visit.push_back(ite_children[0]);
          } else {
            options.push_back({ children[i] });
          }
        }
        assert(options.size() == children.size());
        // generate all combinations of options
        vector<TermVec> all_combinations = get_combinations(options);

        // then rebuild for each TermVec of children
        const Op & op = t->get_op();
        Term res;
        for (auto comb : all_combinations) {
          // construct a new term with the given combination of children
          assert(comb.size() == children.size());
          res = solver->make_term(op, comb);
          // add this term to the stack of terms to check for predicates
          to_visit.push_back(res);
        }
      } else if (is_predicate(t, boolsort, include_symbols)) {
        out.insert(t);
        is_pred = true;
      }

      if (!is_pred || search_subterms) {
        to_visit.insert(to_visit.end(), children.begin(), children.end());
      }
    }
  }
}

TermVec remove_ites_under_model(const SmtSolver & solver, const TermVec & terms)
{
  UnorderedTermSet visited;
  UnorderedTermMap cache;

  TermVec to_visit = terms;
  Term solver_true = solver->make_term(true);
  Term t;
  while (to_visit.size()) {
    t = to_visit.back();
    to_visit.pop_back();

    if (visited.find(t) == visited.end()) {
      to_visit.push_back(t);
      visited.insert(t);
      for (const auto & tt : t) {
        to_visit.push_back(tt);
      }
    } else {
      // post-order case

      TermVec cached_children;
      for (const auto & tt : t) {
        cached_children.push_back(tt);
      }
      Op op = t->get_op();

      if (op == Ite) {
        if (solver->get_value(cached_children[0]) == solver_true) {
          // if case
          cache[t] = cached_children[1];
        } else {
          // else case
          cache[t] = cached_children[2];
        }
      } else if (cached_children.size()) {
        // rebuild to take into account any changes
        if (!op.is_null()) {
          cache[t] = solver->make_term(op, cached_children);
        } else {
          assert(cached_children.size() == 1);  // must be a constant array
          assert(t->get_sort()->get_sort_kind() == ARRAY);
          cache[t] = solver->make_term(cached_children[0], t->get_sort());
        }
      } else {
        // just map to itself in the cache
        // when there's no children
        cache[t] = t;
      }

      assert(cache.find(t) != cache.end());
    }
  }

  TermVec res;
  res.reserve(terms.size());
  for (const auto & tt : terms) {
    res.push_back(cache.at(tt));
  }
  return res;
}

}  // namespace pono
