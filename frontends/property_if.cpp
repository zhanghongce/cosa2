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
#include <fstream>
#include <numeric>
#include <cmath>
#include "json/json.hpp"
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
          auto position = n_prop.first.find(std::to_string(step_-1));
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

PropertyInterfacecex::PropertyInterfacecex(const PonoOptions pono_options,
                            
                           const std::string& scope,
                           bool reg_only, TransitionSystem & ts):
pono_options_(pono_options),ts_(ts), is_reg([this](const std::string & check_name) -> bool{ 
  auto pos = ts_.named_terms().find(check_name);
  // std::cout<< check_name<<std::endl;
  if(pos == ts_.named_terms().end())
    return false;
  return ts_.is_curr_var(pos->second);
 } )
  {
    const std::string& vcd_file_name = pono_options.cex_reader_;
    parse_from(vcd_file_name, scope, is_reg, reg_only);
    // pono_options_ = pono_options;
    get_COI_variable(pono_options_);
  }

void PropertyInterfacecex::get_COI_variable(PonoOptions pono_options_){
    const std::string json_name = pono_options_.smt_path_ + "/" + "COI_variable.json";
    std::ifstream f(json_name);
    if(!f.is_open() )
        return ;
    nlohmann::json data = nlohmann::json::parse(f);
    data.at("name").get_to(name_terms); 
      for(const auto var: name_terms) {
      std::cout<<"The COI variable is: "<<var<<endl;
      auto var_copy = var;
      if (var_copy.length() > 2 && var_copy.front() == var_copy.back() &&
        var_copy.front() == '|') // remove extra | pair
        var_copy = var_copy.substr(1,var_copy.length()-2);
      auto pos_1 = var_copy.rfind("RTL.");
      if(pos_1!=std::string::npos){
        var_copy = var_copy.substr(pos_1+4);
      }
      // auto pos = var_copy.rfind('[');
      // if (pos != std::string::npos) {
      //   auto rpos = var_copy.find(']',pos);//If we cannot find, the find function will return the std::string::npos
      //   // ILA_ERROR_IF(rpos == std::string::npos) 
      //   //   << "Cex variable name:" << check_name << " has unmatched [] pair";
      //   if (rpos == std::string::npos)
      //     throw PonoException("has unmatched [] pair");
      //   auto colon_pos = var_copy.find(':', pos);
      //   if (colon_pos != std::string::npos && colon_pos < rpos){
      //     auto new_name = var_copy.substr(0, pos); 
      //     new_name_terms.push_back(new_name);
      //   }

      // }
      // else{
      new_name_terms.push_back(var_copy);
      // }
  }
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
  }
  // std::cout<<prop->to_string()<<std::endl;
  double sumValue = accumulate(begin(get_width), end(get_width), 0.0); 
  int meanvalue = round(sumValue/get_width.size());
  return meanvalue;
}

int PropertyInterfacecex::get_reg_min_width(){
    for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    get_width.push_back(sort->get_width());
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
  }
  // std::cout<<prop->to_string()<<std::endl;
  std::vector<int>::iterator min_iterator = std::min_element(get_width.begin(), get_width.end());
  return *min_iterator;
}
smt::Term PropertyInterfacecex::cex_parse_to_pono_property(filter_t filter,filter_r filter_re,bool add_coi){
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    // vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    // if(result==new_name_terms.end()){
    //   continue;
    // }
    if(add_coi){
    vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
      if ((!filter(var_name))||(result==new_name_terms.end())){
        continue;
        }
    }
    else{
      if ((!filter(var_name))){
        continue;
        }      
    }
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
    auto eq = ts_.make_term(Equal, var, val);
    if(add_coi){
    vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    if ((!filter_re(eq))||(result==new_name_terms.end())){
        continue;
        }
    }
    else{
      if ((!filter_re(eq))){
        continue;
        }      
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


smt::Term PropertyInterfacecex::cex_parse_to_pono_property(filter_r filter_re,bool add_coi){
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    // vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    // if(result==new_name_terms.end()){
    //   continue;
    // }
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(var_val_pair.second, sort, 2);
    auto eq = ts_.make_term(Equal, var, val);
    if(add_coi){
    vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    if ((!filter_re(eq))||(result==new_name_terms.end())){
        continue;
        }
    }
    else{
      if ((!filter_re(eq))){
        continue;
        }      
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

smt::Term PropertyInterfacecex::cex_parse_to_pono_property(filter_t filter,bool add_coi)
{
  // NOT (var1 == val1 && var2 == val2 && ...)
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    // vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    // if(result==new_name_terms.end()){
    //   continue;
    // }
    if(add_coi){
    vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
      if ((!filter(var_name))||(result==new_name_terms.end())){
        continue;
        }
    }
    else{
      if ((!filter(var_name))){
        continue;
        }      
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
    // vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    // if(result==new_name_terms.end()){
    //   continue;
    // }
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

smt::Term PropertyInterfacecex::cex_parse_to_pono_property_coi(filter_r filter_re)
{
  // NOT (var1 == val1 && var2 == val2 && ...)
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    if(result==new_name_terms.end()){
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
  // std::cout<<prop->to_string()<<std::endl;
    if (prop==nullptr)
    {
      return prop;
    }
  return ts_.make_term(Not, prop);
}

smt::Term PropertyInterfacecex::cex_parse_to_pono_property_coi(filter_t filter)
{
  // NOT (var1 == val1 && var2 == val2 && ...)
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    if(result==new_name_terms.end()){
      continue;
    }
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
    if (prop==nullptr)
    {
      return prop;
    }
  return ts_.make_term(Not, prop);
}

smt::Term PropertyInterfacecex::cex_parse_to_pono_property_coi()
{
  // NOT (var1 == val1 && var2 == val2 && ...)
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
    if(result==new_name_terms.end()){
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
    if (prop==nullptr)
    {
      return prop;
    }
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

void QedCexParser::get_remaining_var(filter_t filter,std::vector<std::string> & out) const {
  for (const auto & var_val_pair : GetCex() ) {
    const auto & var_name = var_val_pair.first;
    if(!filter(var_name))
      continue;
    out.push_back(var_name);
  }
}

smt::Term QedCexParser::cex2property(
  filter_t filter) const
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
    auto eq = ts_.make_term(Equal, var, val);
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  assert(prop != nullptr);
  return ts_.make_term(Not, prop);
}

}  // namespace pono
