
#pragma once
// #ifndef FILTER_H
// #define FILTER_H

// #include "frontends/property_if.cpp"

// #endif /* B_H */
#include <string>
#include <list>
#include <vector>
#include <assert.h>
#include "core/ts.h"
// #include "frontends/property_if.h"

// #include "utils/term_analysis.h"
namespace pono {

// class PropertyInterface;

class AntFilter{
  public:  
    smt::UnorderedTermSet out;
    std::vector<smt::UnorderedTermSet> out_vec;
    AntFilter(const std::string filename, TransitionSystem &ts, int step); 
    // : filename_(filename),ts_(ts), step_(step){
    //     // PropertyInterface pp = new PropertyInterface(filename_,ts_,step);
    //     PropertyInterface prop_inv(filename_,ts_,step);
    //     auto assumption = prop_inv.assumption;
        
    //     // auto assumption = assumptions_.at(i);
    //     get_predicates(ts.get_solver(),assumption,out,false,true,true);
          
    // }
    ~AntFilter() {}
    bool operator()(const smt::Term &n) const;
    // {
    //     for (const auto & it: out){
    //       if (it->to_string() == n ->to_string()){
    //         return true;
    //       }
    // }
    // return false;
    // }
  protected:
    std::string filename_;
    TransitionSystem & ts_;
    smt::Term assumption;
    int step_ ;
    int num_consider_;
};

class Filter {
public:
  virtual bool operator()(const std::string & n) const = 0;
  virtual std::vector<std::pair<int,int>> range(const std::string & n) const = 0;
  virtual std::string to_string() const = 0;
  virtual ~Filter() {}
};

class MaxWidthFilter : public Filter {
protected:
  unsigned width_;
  const TransitionSystem & ts_;
public:
  MaxWidthFilter(unsigned w, const TransitionSystem & ts) : width_(w), ts_(ts) { }
  bool operator()(const std::string & n) const override {
    auto pos = ts_.named_terms().find(n);
    assert(pos != ts_.named_terms().end());
    auto var = pos->second;
    if ( var->get_sort()->get_sort_kind() != smt::SortKind::BV )
      return true;
    if (var->get_sort()->get_width() <= width_ )
      return true;
    return false;
  }
  std::string to_string() const override {
    return "[W<" + std::to_string(width_) +"]";
  }
  
  virtual std::vector<std::pair<int,int>> range(const std::string & n) const override {
    return {};
  }
};

class NameFilter : public Filter{
protected:
  std::unordered_set<std::string> varset;
  const TransitionSystem & ts_;
  bool must_in_;
public:
  NameFilter(const std::vector<std::string> & v, const TransitionSystem & ts, bool must_in) : ts_(ts), must_in_(must_in)
     { varset.insert(v.begin(), v.end()); }
  bool operator()(const std::string & n) const {
    auto pos1 = varset.find(n);
    auto pos2 = ts_.named_terms().find(n);
    assert(pos2 != ts_.named_terms().end());
    auto var = pos2->second;

    std::string varname_from_smt2 = var->to_raw_string();
    if(varname_from_smt2.length() > 2 && varname_from_smt2.front() == '|' 
      && varname_from_smt2.back() == '|' )
      varname_from_smt2 = varname_from_smt2.substr(1, varname_from_smt2.length() -2 );
    auto pos3 = varset.find(varname_from_smt2);

    bool in_vars  = pos1 != varset.end() || pos3 != varset.end();
    if(must_in_ && !in_vars)
      return false;
    if (!must_in_ && in_vars)
      return false;
    return true;
  }
  std::string to_string() const override {
    if(must_in_)
      return "[Keep " + std::to_string(varset.size()) +" V]";
    return "[rm " + std::to_string(varset.size()) +"V]";
  }
  virtual std::vector<std::pair<int,int>> range(const std::string & n) const override {
    return {};
  }
};



class SliceFilter : public Filter{
protected:
  std::unordered_map<std::string, std::vector<std::pair<int,int>>> var_slices_;
  const TransitionSystem & ts_;
public:
  SliceFilter(const std::unordered_map<std::string, std::vector<std::pair<int,int>>> & v, const TransitionSystem & ts) : 
    var_slices_(v) , ts_(ts) { }

  bool operator()(const std::string & n) const {
    auto pos1 = var_slices_.find(n);
    auto pos2 = ts_.named_terms().find(n);
    assert(pos2 != ts_.named_terms().end());
    auto var = pos2->second;

    std::string varname_from_smt2 = var->to_raw_string();
    if(varname_from_smt2.length() > 2 && varname_from_smt2.front() == '|' 
      && varname_from_smt2.back() == '|' )
      varname_from_smt2 = varname_from_smt2.substr(1, varname_from_smt2.length() -2 );
    auto pos3 = var_slices_.find(varname_from_smt2);

    bool in_vars  = pos1 != var_slices_.end() || pos3 != var_slices_.end();
    if(!in_vars)
      return false;
    return true;
  }
  std::string to_string() const override {
    return "[Keep " + std::to_string(var_slices_.size()) +" V]";
  }
  virtual std::vector<std::pair<int,int>> range(const std::string & n) const override {
    auto pos1 = var_slices_.find(n);
    auto pos2 = ts_.named_terms().find(n);
    assert(pos2 != ts_.named_terms().end());
    auto var = pos2->second;

    std::string varname_from_smt2 = var->to_raw_string();
    if(varname_from_smt2.length() > 2 && varname_from_smt2.front() == '|' 
      && varname_from_smt2.back() == '|' )
      varname_from_smt2 = varname_from_smt2.substr(1, varname_from_smt2.length() -2 );
    auto pos3 = var_slices_.find(varname_from_smt2);

    if( pos1 != var_slices_.end() )
      return pos1->second;
    if ( pos3 != var_slices_.end() )
      return pos3->second;
    assert (false);
  }
};

struct FilterConcat : public Filter{
  std::list<std::shared_ptr<Filter>> filters;
  bool operator()(const std::string & n) const override {
    for (const auto & f : filters) {
      if (!(*f)(n))
        return false;
    }
    return true;
  }
  std::string to_string() const override {
    std::string ret;
    for (const auto & f : filters) 
      ret += f->to_string();
    return ret;
  }
  virtual std::vector<std::pair<int,int>> range(const std::string & n) const override {
    for (const auto & f : filters) {
      auto r = f->range(n);
      if ( r.size() > 0 )
        return r;
    }
    return {};
  }
};
}

