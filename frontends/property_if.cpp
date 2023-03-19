/*********************                                                        */
/*! \file property_if.cpp
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Frontend for the Verification Modulo Theories (VMT) format.
**        See https://vmt-lib.fbk.eu/ for more information.
**
**
**/

#include "frontends/property_if.h"
#include "cexreader/cex_extract.h"
#include <numeric>
#include <cmath>
using namespace smt;
using namespace std;

namespace pono {
PropertyInterface::PropertyInterface(std::string filename, TransitionSystem & ts)
    : super(ts.get_solver()), filename_(filename), ts_(ts)
{
  set_logic_all();
  int res = parse(filename_);
  assert(!res);  // 0 means success

  for(const auto & n_prop : defs_){
      if(n_prop.first.find("assertion.") == 0)
        assertions_.push_back(n_prop.second);
      if(n_prop.first.find("assumption.") == 0)
        assumptions_.push_back(n_prop.second);
       
  }
}

PropertyInterface::PropertyInterface(std::string filename, TransitionSystem & ts, int step)
    : super(ts.get_solver()), filename_(filename), ts_(ts), step_(step)
{
  set_logic_all();
  int res = parse(filename_);
  assert(!res);  // 0 means success

  for(const auto & n_prop : defs_){
      if(n_prop.first.find("assertion.") == 0)
        assertions_.push_back(n_prop.second);
      if(n_prop.first.find("assumption.") == 0)
        assumptions_.push_back(n_prop.second);
        // for(int i=1;i<=num_consider_;i++){
        //   if(con_assumption.size()==num_consider_)
        //     break;
          auto position = n_prop.first.find(to_string(step_-1));
          if (position!=std::string::npos){
            // con_assumption.push_back(n_prop.second);
            assumption = n_prop.second;
            // break;
          }
        // }
  }
}


smt::Term PropertyInterface::register_arg(const std::string & name, const smt::Sort & sort) {
  auto tmpvar = ts_.lookup(name);
  arg_param_map_.add_mapping(name, tmpvar);
  return tmpvar; // we expect to get the term in the transition system.
}

smt::Term PropertyInterface::AddAssertions(const smt::Term &in) const{
  smt::Term ret = in;
  for(const auto & t : assertions_) {
    if (ret == nullptr)
      ret = t;
    else
      ret = ts_.make_term(smt::And, ret, t);
  }
  return ret;
}

void PropertyInterface::AddAssumptionsToTS() {
  for(const auto & t : assumptions_)
    ts_.add_constraint(t);
}

// --------------------------------------------------------------------------

std::string static remove_vertical_bar(const std::string & in) {
  if (in.length() > 2 && in.front() == '|' && in.back() == '|')
    return in.substr(1,in.length()-2);
  return in;
}

AssumptionRelationReader::AssumptionRelationReader(std::string filename, TransitionSystem & ts)
    : super(ts.get_solver()), filename_(filename), ts_(ts)
{
  set_logic_all();
  int res = parse(filename_);
  assert(!res);  // 0 means success

  for(const auto & n_prop : defs_) {
    auto fun_name = remove_vertical_bar(n_prop.first);
    if ( fun_name.find("cond.") == 0 ) {
      //                01234
      auto sv_name = fun_name.substr(5);
      sv_cond_.emplace(sv_name, n_prop.second);
    } else if (fun_name.find("value.") == 0) {
      //                      012345
      auto sv_name = fun_name.substr(6);
      sv_value_.emplace(sv_name, n_prop.second);
    }     
  }
} // end of AssumptionRelationReader::AssumptionRelationReader


smt::Term AssumptionRelationReader::register_arg(const std::string & name, const smt::Sort & sort) {
  auto tmpvar = ts_.lookup(name);
  arg_param_map_.add_mapping(name, tmpvar);
  return tmpvar; // we expect to get the term in the transition system.
}

smt::Term AssumptionRelationReader::GetConditionInAssumption(const std::string & t) const {
  if(sv_cond_.find(t) == sv_cond_.end())
    return ts_.get_solver()->make_term(true); // return true;
  return sv_cond_.at(t);
}

// --------------------------------------------------------------------------

PropertyInterfacecex::PropertyInterfacecex(const std::string& vcd_file_name,
                           const std::string& scope,
                           bool reg_only, TransitionSystem & ts):
ts_(ts), is_reg([this](const std::string & check_name) -> bool{ 
  auto pos = ts_.named_terms().find(check_name);
  // std::cout<< check_name<<std::endl;
  if(pos == ts_.named_terms().end())
    return false;
  return ts_.is_curr_var(pos->second);
 } )
  {
    parse_from(vcd_file_name, scope, is_reg, reg_only);
  }

int PropertyInterfacecex::get_reg_width(){
    for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    get_width.push_back(sort->get_width());
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
    auto eq = ts_.make_term(Equal, var, val);
  }
  // std::cout<<prop->to_string()<<std::endl;
  double sumValue = accumulate(begin(get_width), end(get_width), 0.0); 
  int meanvalue = round(sumValue/get_width.size());
  return meanvalue;
  

}
smt::Term PropertyInterfacecex::cex_parse_to_pono_property(filter_t filter,filter_r filter_re){
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    if (!filter(var_name)){
      continue;
    }
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
    auto eq = ts_.make_term(Equal, var, val);
    if (!filter_re(eq)){
      continue;
      }
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  if (prop==nullptr)
    {
      return cex_parse_to_pono_property(filter);
    }
  return ts_.make_term(Not, prop);

}


smt::Term PropertyInterfacecex::cex_parse_to_pono_property(filter_r filter_re){
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
    auto eq = ts_.make_term(Equal, var, val);
    if (!filter_re(eq)){
      continue;
      }
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  if (prop==nullptr)
    {
      return prop;
    }
  return ts_.make_term(Not, prop);

}

smt::Term PropertyInterfacecex::cex_parse_to_pono_property(filter_t filter)
{
  // NOT (var1 == val1 && var2 == val2 && ...)
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    if (!filter(var_name)){
      continue;
    }
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
    auto eq = ts_.make_term(Equal, var, val);
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  // std::cout<<prop->to_string()<<std::endl;
  return ts_.make_term(Not, prop);
}
smt::Term PropertyInterfacecex::cex_parse_to_pono_property()
{
  // NOT (var1 == val1 && var2 == val2 && ...)
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
    auto eq = ts_.make_term(Equal, var, val);
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  // std::cout<<prop->to_string()<<std::endl;
  return ts_.make_term(Not, prop);
}


// --------------------------------------------------------------------------

QedCexParser::QedCexParser(const std::string& vcd_file_name,
                           const std::string& filter,
                            const std::string& name_removal,
                           TransitionSystem & ts):
SelectiveExtractor(name_removal), // do not parse automatically
ts_(ts), is_reg([this](const std::string & check_name) -> bool{ 
  auto pos = ts_.named_terms().find(check_name);
  if(pos == ts_.named_terms().end())
    return false;
  return ts_.is_curr_var(pos->second);
 } )
  {
    parse_from(vcd_file_name, filter, is_reg, true);
  }

void QedCexParser::get_remaining_var(filter_t & filter,std::vector<std::string> & out) const {
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    if(!filter(var_name))
      continue;
    out.push_back(var_name);
  }
}

smt::Term QedCexParser::cex2property(
  filter_t & filter) const
{
  // NOT (var1 == val1 && var2 == val2 && ...)
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    if(!filter(var_name))
      continue;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;

    auto sort = var->get_sort();
    auto val = ts_.make_term(var_val_pair.second, sort, 2);

    auto range = filter.range(var_name);
    Term eq;
    if (range.empty()) 
      eq = ts_.make_term(Equal, var, val);
    else {
      for (const auto & slice : range) {
        auto extract_op = smt::Op(smt::PrimOp::Extract, slice.first, slice.second);
        auto slice_eq = 
          ts_.make_term(Equal, ts_.make_term(extract_op, var), ts_.make_term(extract_op, val));

        if (eq == nullptr)
          eq = slice_eq;
        else
          eq = ts_.make_term(And, eq, slice_eq);
      }
    }
    
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  assert(prop != nullptr);
  return ts_.make_term(Not, prop);
}

}  // namespace pono
