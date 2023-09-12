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
#include "json/json.hpp"
#include <fstream>
#include <numeric>
#include <cmath>
#include <stddef.h>
#include "json/json.hpp"
#include <boost/regex.hpp>
using namespace smt;
using namespace std;

namespace pono {
int findElement(vector<std::string> v, std::string key){
	int len = v.size();
	for(int i=0; i<len; i++){
		if(v.at(i) == key){
			return i;
		}
	}
	return -1;
}

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

// PropertyInterface::PropertyInterface(std::string filename, TransitionSystem & ts, int step)
//     : super(ts.get_solver()), filename_(filename), ts_(ts), step_(step)
// {
//   set_logic_all();
//   int res = parse(filename_);
//   assert(!res);  // 0 means success

//   for(const auto & n_prop : defs_){
//       if(n_prop.first.find("assertion.") == 0)
//         assertions_.push_back(n_prop.second);
//       if(n_prop.first.find("assumption.") == 0)
//         assumptions_.push_back(n_prop.second);
//         // for(int i=1;i<=num_consider_;i++){
//         //   if(con_assumption.size()==num_consider_)
//         //     break;
//           auto position = n_prop.first.find(to_string(step_-1));
//           if (position!=std::string::npos){
//             // con_assumption.push_back(n_prop.second);
//             assumption = n_prop.second;
//             // break;
//           }
//         // }
//   }
// }


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

smt::Term PropertyInterface::Transfer_assump_to_assert(const smt::Term &in) const{
  smt::Term ret = in;
  for(const auto & t : assumptions_) {
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

PropertyInterfacecex::PropertyInterfacecex(const PonoOptions pono_options,
                            const std::string filter,
                           bool reg_only, TransitionSystem & ts):
pono_options_(pono_options),ts_(ts), is_reg([this](const std::string & check_name) -> bool{ 
  auto pos = ts_.named_terms().find(check_name);
  if(pos == ts_.named_terms().end())
    return false;
  auto a = ts_.is_curr_var(pos->second);
  auto b = (ts_.state_updates().find(pos->second)!=ts_.state_updates().end());
  return a&&b;
 } )
  {
    const std::string& vcd_file_name = pono_options.cex_reader_;
    parse_from(vcd_file_name, filter, is_reg, true);
    get_COI_variable(pono_options_);
  }
}


void PropertyInterfacecex::get_COI_variable(PonoOptions pono_options_){
      const std::string& vcd_file_name = pono_options_.cex_reader_;
      // parse_from(vcd_file_name, scope, is_reg, true);
      const std::string json_name = pono_options_.smt_path_ + "/" + "COI_variable.json";
      const std::string qed_name = pono_options_.smt_path_ + "/" + "qed_signal.json";
      std::ifstream f(json_name);
      std::ifstream f1(qed_name);
      if(!f.is_open() )
          return ;
      nlohmann::json data = nlohmann::json::parse(f);
      if(f.is_open()){
        nlohmann::json data_qed = nlohmann::json::parse(f1);
        data_qed.at("name").get_to(qed_name_terms);
      }
       
      data.at("name").get_to(name_terms); 
      data.at("value").get_to(value_terms); 

      having_extract = data.find("name_to_extract")!=data.end();
      if(having_extract){
        data.at("name_to_extract").get_to(name_extract);
        data.at("extract_width").get_to(extract_val);
      }

      auto count = 0;
      for(const auto var: name_terms) {
      std::cout<<"The COI variable is: "<<var<<endl;
      auto pos_qed = var.rfind("qed");
      if(pos_qed!=std::string::npos){
        std::cout<<"The COI variable is in the QED module. "<<var<<endl;
        count = count + 1;
        continue;
      }
      if(!qed_name_terms.empty()&&(std::find(qed_name_terms.begin(), qed_name_terms.end(), var) != qed_name_terms.end())){
        std::cout<<"The COI variable is for the SQED test. "<<var<<endl;
        count = count + 1;
        continue;
      }
      auto var_copy = var;
      if (var_copy.length() > 2 && var_copy.front() == var_copy.back() &&
        var_copy.front() == '|') // remove extra | pair
        var_copy = var_copy.substr(1,var_copy.length()-2);
      auto pos_1 = var_copy.rfind("RTL.");
      if(pos_1!=std::string::npos){
        var_copy = var_copy.substr(pos_1+4);
      }
      else{
        count = count + 1;
        continue;
      }
      auto origin_val  = value_terms.at(count);
      origin_val = origin_val.substr(2);
      new_name_terms.push_back(var_copy);
      new_value_terms.push_back(origin_val);
      count = count +1;
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
    // auto val = ts_.make_term(var_val_pair.second, sort, 2);
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
    // auto val = ts_.make_term(var_val_pair.second, sort, 2);
  }
  // std::cout<<prop->to_string()<<std::endl;
  std::vector<int>::iterator min_iterator = std::min_element(get_width.begin(), get_width.end());
  return *min_iterator;
}

smt::Term PropertyInterfacecex::cex_parse_to_pono_property(filter_t filter,bool filter_en,filter_r filter_re,bool filter_re_en){
  smt::Term prop;
  for (const auto & var_val_pair : GetCex() ) {
    smt::Term eq;
    const auto & var_name = var_val_pair.first;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    if((!filter(var_name))&&filter_en)
        continue;
    auto var = pos->second;
    auto sort = var->get_sort();
    auto idx = findElement(new_name_terms,var_name);
    if(idx!=-1)
      eq = get_extract_from_coi(var_val_pair.second,var,var_name,filter_re,filter_re_en);
    else
      continue;
    if(eq==nullptr)
      continue;
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  if (prop==nullptr){
      return prop;
  }
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

smt::Term PropertyInterfacecex::get_extract_from_coi(const std::string val_string, const smt::Term var, std::string var_name,filter_r filter,bool filter_re_en){
    smt::Term eq;
    std::vector<std::pair<int,int>> extracted_out;
    auto val = ts_.make_term(val_string,var->get_sort(),2);
    if(having_extract&& is_extracted(var_name,extracted_out)){
      for(const auto out:extracted_out){
        int idx0;
        int idx1;
        get_info(out,idx0,idx1);
        if((!filter(var_name,val_string,idx0,idx1))&&(filter_re_en))
          continue;
        auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
        auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
        auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
        if(eq==nullptr){
          eq = eq_extract;
        }
        else{
          eq=ts_.make_term(And,eq,eq_extract);
        }
      }
    }
    else{
      eq = ts_.make_term(Equal, var, val);  
    }
    return eq;
}

bool PropertyInterfacecex::is_extracted(const std::string & var_name, std::vector<std::pair<int,int>> & extract_info){
  auto count = 1;
  auto count_pos = 0;
  for(auto name_ext: name_extract){
    
    auto pos_1 = name_ext.rfind("RTL.");
    if(pos_1!=std::string::npos){
      name_ext = name_ext.substr(pos_1+4);
    }
    else{
      count_pos = count_pos + 1;
      continue;
    }

    if(name_ext == var_name){
      std::cout<<"The COI variable: "<< var_name<<" can be extracted "<< count << " times"<<std::endl; 
      count = count + 1;
      extract_info.push_back(extract_val.at(count_pos));
    }
    count_pos = count_pos + 1;
  }
  if(extract_info.empty()==true){
    return false;
  }
  return true;
}

void PropertyInterfacecex::get_info(const std::pair<int,int> & out, int & idx0, int & idx1){
  idx0 = out.first;
  idx1 = out.second;
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
  auto a = ts_.is_curr_var(pos->second);
  auto b = (ts_.state_updates().find(pos->second)!=ts_.state_updates().end());
  return a&&b;
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



JsonCexParser::JsonCexParser(PonoOptions & pono_options,const std::string& scope,TransitionSystem & ts):
  pono_options_(pono_options),ts_(ts),is_reg([this](const std::string & check_name) -> bool{ 
  auto pos = ts_.named_terms().find(check_name);
  if(pos == ts_.named_terms().end())
    return false;
  auto a = ts_.is_curr_var(pos->second);
  auto b = (ts_.state_updates().find(pos->second)!=ts_.state_updates().end());
  return a&&b;
 })
 {
      const std::string& vcd_file_name = pono_options.cex_reader_;
      // parse_from(vcd_file_name, scope, is_reg, true);
      const std::string json_name = pono_options_.smt_path_ + "/" + "COI_variable.json";
      const std::string qed_name = pono_options_.smt_path_ + "/" + "qed_signal.json";
      std::ifstream f(json_name);
      std::ifstream f1(qed_name);
      if(!f.is_open() )
          return ;
      nlohmann::json data = nlohmann::json::parse(f);
      if(f.is_open()){
        nlohmann::json data_qed = nlohmann::json::parse(f1);
        data_qed.at("name").get_to(qed_name_terms);
      }
       
      data.at("name").get_to(name_terms); 
      data.at("value").get_to(value_terms); 
      auto using_coi = true;
      if(using_coi){
        having_extract = data.find("name_to_extract")!=data.end();
        // std::vector<std::vector<std::pair<int,int>>> extract_val_middle;
        if(having_extract){
          data.at("name_to_extract").get_to(name_extract);
          data.at("extract_width").get_to(extract_val);
        }
      }
      auto count = 0;
      for(const auto var: name_terms) {
      std::cout<<"The COI variable is: "<<var<<endl;
      auto pos_qed = var.rfind("qed");
      if(pos_qed!=std::string::npos){
        std::cout<<"The COI variable is in the QED module. "<<var<<endl;
        count = count + 1;
        continue;
      }
      if(!qed_name_terms.empty()&&(std::find(qed_name_terms.begin(), qed_name_terms.end(), var) != qed_name_terms.end())){
        std::cout<<"The COI variable is for the SQED test. "<<var<<endl;
        count = count + 1;
        continue;
      }
      auto var_copy = var;
      if (var_copy.length() > 2 && var_copy.front() == var_copy.back() &&
        var_copy.front() == '|') // remove extra | pair
        var_copy = var_copy.substr(1,var_copy.length()-2);
      auto pos_1 = var_copy.rfind("RTL.");
      if(pos_1!=std::string::npos){
        var_copy = var_copy.substr(pos_1+4);
      }
      else{
        count = count + 1;
        continue;
      }
      auto origin_val  = value_terms.at(count);
      origin_val = origin_val.substr(2);
      new_name_terms.push_back(var_copy);
      new_value_terms.push_back(origin_val);
      count = count +1;
  }
}

bool JsonCexParser::is_extracted(const std::string & var_name, std::vector<std::pair<int,int>> & extract_info,std::vector<std::pair<int,int>> & extract_val_info){
  auto count = 1;
  auto count_pos = 0;
  auto flag = 0;

  std::pair<int,int> origin_extract = std::make_pair(0,0);
  std::pair<int,int> origin_extract_val = std::make_pair(0,0);
  // boost::regex pattern(R"(\[(\d+)_(\d+)\])");
  // boost::smatch matches;
  if(extract_info.empty()!=true){
        assert(extract_info.size()==1);
        origin_extract = extract_info.back();
        origin_extract_val = extract_val_info.back();
        extract_info.clear();
        extract_val_info.clear();
        flag = 1;
  }
  for(auto name_ext: name_extract){
    // if (boost::regex_search(name_ext, matches, pattern)){
    //   auto pos = name_ext.find("[");
    //   name_ext = name_ext.substr(0,pos);
    // }
    auto pos_1 = name_ext.rfind("RTL.");
    if(pos_1!=std::string::npos){
      name_ext = name_ext.substr(pos_1+4);
    }
    // else
    //   continue;
    if(name_ext == var_name){

      std::cout<<"The COI variable: "<< var_name<<" can be extracted "<< count << " times"<<std::endl; 
      count = count + 1;
      if(flag==0){
        extract_info.push_back(extract_val.at(count_pos));
        extract_val_info.push_back(extract_val.at(count_pos));
      }
      else{
        auto extract_bit = extract_val.at(count_pos);
        assert((origin_extract.first>=origin_extract.second + extract_bit.first));
        extract_info.push_back(std::make_pair(origin_extract.second + extract_bit.first, origin_extract.second + extract_bit.second));  
        extract_val_info.push_back(extract_val.at(count_pos)); 
      }
    }
    count_pos = count_pos + 1;
  }
  if(extract_info.empty()==true){
    if(flag==1){
      std::cout<<"The COI variable: "<< var_name<<" can be extracted "<< 1 << " times"<<std::endl; 
      extract_info.push_back(origin_extract);
      extract_val_info.push_back(origin_extract_val);
      return true;
    }
    else
      return false;
  }
  return true;
}

void JsonCexParser::get_info(const std::pair<int,int> & out, int & idx0, int & idx1){
  idx0 = out.first;
  idx1 = out.second;
}

/// @brief ///We need to fix some var_name that inserted by us on btor
/// @param var_name 
/// @param extracted_out 
bool JsonCexParser::fix_varname(std::string & var_name,std::vector<std::pair<int,int>> & extracted_out,std::vector<std::pair<int,int>> & extract_val_info){
      auto pos_left = var_name.rfind("[");
      if(pos_left!=std::string::npos){
        auto extract_val = var_name.substr(pos_left);
        auto pos_unknow = extract_val.rfind("_");
        if(pos_unknow!=std::string::npos){
          auto left = extract_val.substr(1 ,pos_unknow-1);
          auto right_bound =  extract_val.size() - 1;
          auto right = extract_val.substr(pos_unknow+1,right_bound - pos_unknow-1);
          auto left_val =  stoi(left);
          auto right_val = stoi(right);
          extracted_out.push_back(std::make_pair(left_val,right_val));
          extract_val_info.push_back(std::make_pair(left_val-right_val,0));
          var_name = var_name.substr(0,pos_left);
          return true;
        }
      }
      return false;
}

smt::Term JsonCexParser::json_cex_parse_to_pono_property(filter_r filter_re,filter_t filter){
  auto count = 0;
  smt::Term prop;
  bool is_extract = false;
  for (const auto var_name: new_name_terms){
    smt::Term eq;
    std::vector<std::pair<int,int>> extracted_out;
    std::vector<std::pair<int,int>> extract_val_info;
    auto var_name_copy = var_name;
    if ((!filter(var_name_copy))){
        count = count + 1;
        continue;
    } 
    is_extract = fix_varname(var_name_copy,extracted_out,extract_val_info);
    auto pos = ts_.named_terms().find(var_name_copy);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(new_value_terms.at(count), sort, 2);
    count = count + 1;
    if(having_extract)
      is_extract = is_extracted(var_name,extracted_out,extract_val_info);
    assert(extracted_out.size()==extract_val_info.size());
    if(is_extract==true){
      for(auto i = 0;i < extracted_out.size();i++){
        int idx0;
        int idx1;
        get_info(extract_val_info.at(i),idx0,idx1);
        if(!(filter_re(var_name,new_value_terms.at(count),idx0,idx1)))
          continue;
        auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
        get_info(extracted_out.at(i),idx0,idx1);
        auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
        auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
        if(eq==nullptr){
          eq = eq_extract;
        }
        else{
          eq=ts_.make_term(And,eq,eq_extract);
        }
      }
    }
    else{
      if(!(filter_re(var_name,new_value_terms.at(count),sort->get_width(),0)))
        continue;
      eq = ts_.make_term(Equal, var, val);    
    }
    if(prop!=nullptr){
      prop = ts_.make_term(And, prop, eq);
    }
    else{
      prop = eq;
    }
  } 
  if (prop==nullptr)
    {
      return prop;
    }
  return ts_.make_term(Not, prop);
}


smt::Term JsonCexParser::json_cex_parse_to_pono_property(filter_r filter_re){
  auto count = 0;
  smt::Term prop;
  bool is_extract = false;
  for (const auto var_name: new_name_terms){
    smt::Term eq;
    std::vector<std::pair<int,int>> extracted_out;
    std::vector<std::pair<int,int>> extract_val_info;
    auto var_name_copy = var_name;
    is_extract = fix_varname(var_name_copy,extracted_out,extract_val_info);
    auto pos = ts_.named_terms().find(var_name_copy);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(new_value_terms.at(count), sort, 2);
    count = count + 1;
    if(having_extract)
      is_extract = is_extracted(var_name,extracted_out,extract_val_info);
    assert(extracted_out.size()==extract_val_info.size());
    if(is_extract==true){
      for(auto i = 0;i < extracted_out.size();i++){
        int idx0;
        int idx1;
        if(!(filter_re(var_name,new_value_terms.at(count),idx0,idx1)))
          continue;
        get_info(extract_val_info.at(i),idx0,idx1);
        auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
        get_info(extracted_out.at(i),idx0,idx1);
        auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
        auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
        if(eq==nullptr){
          eq = eq_extract;
        }
        else{
          eq=ts_.make_term(And,eq,eq_extract);
        }
      }
    }
    else{
      if(!(filter_re(var_name,new_value_terms.at(count),sort->get_width(),0)))
        continue;
      eq = ts_.make_term(Equal, var, val);    
    }

    if(prop!=nullptr){
      prop = ts_.make_term(And, prop, eq);
    }
    else{
      prop = eq;
    }
  } 
  if (prop==nullptr)
    {
      return prop;
    }
  return ts_.make_term(Not, prop);
}

smt::Term JsonCexParser::json_cex_parse_to_pono_property(filter_t filter){
  auto count = 0;
  smt::Term prop;
  bool is_extract;
  for (auto var_name: new_name_terms){
    smt::Term eq;
    std::vector<std::pair<int,int>> extracted_out;
    std::vector<std::pair<int,int>> extract_val_info;
    auto var_name_copy = var_name;
    is_extract = fix_varname(var_name_copy,extracted_out,extract_val_info);
    if ((!filter(var_name_copy))){
        count = count + 1;
        continue;
    }  
    auto pos = ts_.named_terms().find(var_name_copy);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    // auto sort_kind = sort->get_sort_kind();
    // auto sort_width = sort ->get_width();
    // auto sort_val = ts_.make_sort(sort_kind,sort_width);
    auto val = ts_.make_term(new_value_terms.at(count), sort, 2);
    count = count + 1;
    if(having_extract)
      is_extract = is_extracted(var_name,extracted_out,extract_val_info);
    assert(extracted_out.size()==extract_val_info.size());
    if(is_extract==true){
      for(auto i = 0;i < extracted_out.size();i++){
        int idx0;
        int idx1;
        get_info(extract_val_info.at(i),idx0,idx1);
        auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
        get_info(extracted_out.at(i),idx0,idx1);
        auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
        auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
        if(eq==nullptr){
          eq = eq_extract;
        }
        else{
          eq=ts_.make_term(And,eq,eq_extract);
        }
      }
    }
    else{
      eq = ts_.make_term(Equal, var, val);  
    }
    if(prop!=nullptr){
      prop = ts_.make_term(And, prop, eq);
    }
    else{
      prop = eq;
    }
  } 
  if (prop==nullptr)
    {
      return prop;
    }
  return ts_.make_term(Not, prop);
}
smt::Term JsonCexParser::json_cex_parse_to_pono_property(){
  auto count = 0;
  smt::Term prop;
  bool is_extract;
  for (auto var_name: new_name_terms){   
    smt::Term eq;
    std::vector<std::pair<int,int>> extracted_out;
    std::vector<std::pair<int,int>> extract_val_info;
    auto var_name_copy = var_name;
    is_extract = fix_varname(var_name_copy,extracted_out,extract_val_info);
    auto pos = ts_.named_terms().find(var_name_copy);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    auto val = ts_.make_term(new_value_terms.at(count), sort, 2);
    count = count + 1;
    if(having_extract)
      is_extract = is_extracted(var_name,extracted_out,extract_val_info);
    assert(extracted_out.size()==extract_val_info.size());
    if(is_extract==true){
      for(auto i = 0;i < extracted_out.size();i++){
        int idx0;
        int idx1;
        get_info(extract_val_info.at(i),idx0,idx1);
        auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
        get_info(extracted_out.at(i),idx0,idx1);
        auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
        auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
        if(eq==nullptr){
          eq = eq_extract;
        }
        else{
          eq=ts_.make_term(And,eq,eq_extract);
        }
      }
    }
    else{
    eq = ts_.make_term(Equal, var, val);    
    } 
    if(prop!=nullptr){
      prop = ts_.make_term(And, prop, eq);
    }
    else{
      prop = eq;
    }
  } 
  if (prop==nullptr)
    {
      return prop;
    }
  return ts_.make_term(Not, prop);
}

// smt::Term JsonCexParser::json_cex_vcd_parse_to_pono_property(filter_r filter_re){
//   auto count = 0;
//   smt::Term prop;
//   smt::Term eq;
//   bool is_extract;
//   for(const auto & var_val_pair : GetCex() ){
//     const auto & var_name = var_val_pair.first;
//     vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
//     if(result==new_name_terms.end()){
//       continue;
//     }
//     std::vector<pair<int,int>> extracted_out;
//     auto pos = ts_.named_terms().find(var_name);
//     assert(pos != ts_.named_terms().end());    
//     auto var = pos->second;
//     auto sort = var->get_sort();
//     auto val = ts_.make_term(new_value_terms.at(count), sort, 2);
//     count = count + 1;
//     if(having_extract)
//       is_extract = is_extracted(var_name,extracted_out);
//     if(is_extract==true){
//       for(const auto out:extracted_out){
//         int idx0;
//         int idx1;
//         get_info(out,idx0,idx1);
//         auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
//         auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
//         auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
//         if(eq==nullptr){
//           eq = eq_extract;
//         }
//         else{
//           eq=ts_.make_term(And,eq,eq_extract);
//         }
//       }
//     }
//     else{
//     eq = ts_.make_term(Equal, var, val);    
//     }
//     if ((!filter_re(eq))){
//       continue;
//       }
//     if(prop!=nullptr){
//       prop = ts_.make_term(And, prop, eq);
//     }
//     else{
//       prop = eq;
//     }
//   } 
//   if (prop==nullptr)
//     {
//       return prop;
//     }
//   return ts_.make_term(Not, prop);
// }

// smt::Term JsonCexParser::json_cex_vcd_parse_to_pono_property(filter_t filter){
//   auto count = 0;
//   smt::Term prop;
//   smt::Term eq;
//   bool is_extract;
//   for(const auto & var_val_pair : GetCex() ){
//     const auto & var_name = var_val_pair.first;
//     vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
//     if(result==new_name_terms.end()){
//       continue;
//     }
//     if(!filter(var_name)){
//       count = count + 1;
//       continue;      
//     }
//     std::vector<pair<int,int>> extracted_out;
//     auto pos = ts_.named_terms().find(var_name);
//     assert(pos != ts_.named_terms().end());    
//     auto var = pos->second;
//     auto sort = var->get_sort();
//     auto val = ts_.make_term(new_value_terms.at(count), sort, 2);
//     count = count + 1;
//     if(having_extract)
//       is_extract = is_extracted(var_name,extracted_out);
//     if(is_extract==true){
//       for(const auto out:extracted_out){
//         int idx0;
//         int idx1;
//         get_info(out,idx0,idx1);
//         auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
//         auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
//         auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
//         if(eq==nullptr){
//           eq = eq_extract;
//         }
//         else{
//           eq=ts_.make_term(And,eq,eq_extract);
//         }
//       }
//     }
//     else{
//     eq = ts_.make_term(Equal, var, val);    
//     }
//     if(prop!=nullptr){
//       prop = ts_.make_term(And, prop, eq);
//     }
//     else{
//       prop = eq;
//     }
//   } 
//   if (prop==nullptr)
//     {
//       return prop;
//     }
//   return ts_.make_term(Not, prop);
// }

// smt::Term JsonCexParser::json_cex_vcd_parse_to_pono_property(){
//   auto count = 0;
//   smt::Term prop;
//   smt::Term eq;
//   bool is_extract;
//   for(const auto & var_val_pair : GetCex() ){
//     const auto & var_name = var_val_pair.first;
//     vector<string>::iterator result = find( new_name_terms.begin( ), new_name_terms.end( ), var_name );
//     if(result==new_name_terms.end()){
//       continue;
//     }
//     std::vector<pair<int,int>> extracted_out;
//     auto pos = ts_.named_terms().find(var_name);
//     assert(pos != ts_.named_terms().end());    
//     auto var = pos->second;
//     auto sort = var->get_sort();
//     auto val = ts_.make_term(new_value_terms.at(count), sort, 2);
//     count = count + 1;
//     if(having_extract)
//       is_extract = is_extracted(var_name,extracted_out);
//     if(is_extract==true){
//       for(const auto out:extracted_out){
//         int idx0;
//         int idx1;
//         get_info(out,idx0,idx1);
//         auto val_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), val);
//         auto var_extract = ts_.make_term(smt::Op(smt::PrimOp::Extract, idx0, idx1), var);
//         auto eq_extract = ts_.make_term(Equal,var_extract,val_extract);
//         if(eq==nullptr){
//           eq = eq_extract;
//         }
//         else{
//           eq=ts_.make_term(And,eq,eq_extract);
//         }
//       }
//     }
//     else{
//     eq = ts_.make_term(Equal, var, val);    
//     }
//     if(prop!=nullptr){
//       prop = ts_.make_term(And, prop, eq);
//     }
//     else{
//       prop = eq;
//     }
//   } 
//   if (prop==nullptr)
//     {
//       return prop;
//     }
//   return ts_.make_term(Not, prop);
// }

int JsonCexParser::get_reg_width(){
    std::vector<std::pair<int,int>> extracted_out;
    std::vector<std::pair<int,int>> extract_val_info;
    for (auto var_name: new_name_terms){
    auto is_extract = fix_varname(var_name,extracted_out,extract_val_info);
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    auto sort = var->get_sort();
    get_width.push_back(sort->get_width());
    // auto val = ts_.make_term(var_val_pair.second, sort, 2);
  }
  // std::cout<<prop->to_string()<<std::endl;
  double sumValue = accumulate(begin(get_width), end(get_width), 0.0); 
  int meanvalue = round(sumValue/get_width.size());
  return meanvalue;
}

int JsonCexParser::get_reg_min_width(){
    std::vector<std::pair<int,int>> extracted_out;
    std::vector<std::pair<int,int>> extract_val_info;
    for (auto var_name: new_name_terms){
      auto is_extract = fix_varname(var_name,extracted_out,extract_val_info);
      auto pos = ts_.named_terms().find(var_name);
      assert(pos != ts_.named_terms().end());
      auto var = pos->second;
      auto sort = var->get_sort();
      get_width.push_back(sort->get_width());
  }
  // std::cout<<prop->to_string()<<std::endl;
  std::vector<int>::iterator min_iterator = std::min_element(get_width.begin(), get_width.end());
  return *min_iterator;
}



smt::Term QedCexParser::cex2property_ant(
  filter_t & filter,filter_r & filter_ant) const
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
        if((!filter_ant(var_name,var_val_pair.second,slice.first,slice.second)))
          continue;
        auto extract_op = smt::Op(smt::PrimOp::Extract, slice.first, slice.second);
        auto slice_eq = 
          ts_.make_term(Equal, ts_.make_term(extract_op, var), ts_.make_term(extract_op, val));

        if (eq == nullptr)
          eq = slice_eq;
        else
          eq = ts_.make_term(And, eq, slice_eq);
      }
    }
    if(eq==nullptr)
      continue;
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  // assert(prop != nullptr);
  if(prop!=nullptr)
    return ts_.make_term(Not, prop);
  else
    return prop;
}

smt::Term coireader::coi_cex2property_ant(filter_t & filter,filter_r & filter_ant) const
{
  smt::Term prop;
  for(const auto & coi: COI_to_consider_){
    const auto & var_name = coi.first;
    if(!filter(var_name))
      continue;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;

    auto sort = var->get_sort();
    auto pos_1 = COI_value_.find(var_name);
    assert(pos_1 != COI_value_.end());
    auto value = pos_1->second;
    assert(value.substr(0,2)=="#b");
    value = value.substr(2);
    auto val = ts_.make_term(value, sort, 2);
    auto range = filter.range(var_name);
    Term eq;
    if (range.empty()) 
      eq = ts_.make_term(Equal, var, val);
    else {
      for (const auto & slice : range) {
        if((!filter_ant(var_name,value,slice.first,slice.second)))
          continue;
        auto extract_op = smt::Op(smt::PrimOp::Extract, slice.first, slice.second);
        auto slice_eq = 
          ts_.make_term(Equal, ts_.make_term(extract_op, var), ts_.make_term(extract_op, val));

        if (eq == nullptr)
          eq = slice_eq;
        else
          eq = ts_.make_term(And, eq, slice_eq);
      }
    }
    if(eq==nullptr)
      continue;
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  if(prop!=nullptr)
    return ts_.make_term(Not, prop);
  else
    return prop;
}


smt::Term coireader::coi_cex2property(filter_t & filter) const{
  smt::Term prop;
  for(const auto & coi: COI_to_consider_){
    const auto & var_name = coi.first;
    if(!filter(var_name))
      continue;
    auto pos = ts_.named_terms().find(var_name);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;

    auto sort = var->get_sort();
    auto pos_1 = COI_value_.find(var_name);
    assert(pos_1 != COI_value_.end());
    auto value = pos_1->second;
    assert(value.substr(0,2)=="#b");
    value = value.substr(2);
    auto val = ts_.make_term(value, sort, 2);
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
    if(eq==nullptr)
      continue;
    if (prop == nullptr)
      prop = eq;
    else
      prop = ts_.make_term(And, prop, eq);
  }
  if(prop!=nullptr)
    return ts_.make_term(Not, prop);
  else
    return prop;
}
}  // namespace pono
