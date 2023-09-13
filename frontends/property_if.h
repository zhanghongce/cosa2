/*********************                                                        */
/*! \file property_if.h
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Frontend for properties in 
**       (define-fun assertion.0 ...) or (define-fun assumption.0 ...)
**
**
**/

#pragma once
// #ifndef PROPERTY_IF_H
// #define PROPERTY_IF_H



// #endif 

#include <iostream>
#include "options/options.h"
#include "assert.h"
#include "core/rts.h"
#include "smt-switch/smt.h"
#include "smt-switch/smtlib_reader.h"
#include "utils/exceptions.h"
#include "cexreader/cex_extract.h"


#include "utils/filter.h"

namespace pono {
class PropertyInterface : public smt::SmtLibReader
{
 public:
  // PropertyInterface(std::string filename, TransitionSystem & ts, int step);
  PropertyInterface(std::string filename, TransitionSystem & ts);
  typedef SmtLibReader super;

  smt::Term AddAssertions(const smt::Term &in) const;
  smt::Term Transfer_assump_to_assert(const smt::Term &in) const;
  void AddAssumptionsToTS();
  smt::TermVec con_assumption;
  smt::Term assumption;
 protected:
  // overloaded function, used when arg list of function is parsed
  // NOTE: | |  pipe quotes are removed.
  virtual smt::Term register_arg(const std::string & name, const smt::Sort & sort) override;

  std::string filename_;

  TransitionSystem & ts_;
  int step_;
  int num_consider_;
  smt::TermVec assertions_;
  smt::TermVec assumptions_;

};

class AssumptionRelationReader : public smt::SmtLibReader {
  
public:
  AssumptionRelationReader(std::string filename, TransitionSystem & ts);
  typedef SmtLibReader super;

  // the input value t should be the term for state variable
  bool IsConstrainedInAssumption(const std::string& t) const { return sv_value_.find(t) != sv_value_.end();}
  smt::Term GetConditionInAssumption(const std::string & t) const;
  smt::Term GetValueTermInAssumption(const std::string & t) const { return sv_value_.at(t); }

  std::string ReportStatus() const { return "SV:"+std::to_string(sv_value_.size()); }
protected:
  // overloaded function, used when arg list of function is parsed
  // NOTE: | |  pipe quotes are removed.
  virtual smt::Term register_arg(const std::string & name, const smt::Sort & sort) override;

  std::string filename_;
  TransitionSystem & ts_;

  std::unordered_map<std::string, smt::Term> sv_cond_;
  std::unordered_map<std::string, smt::Term> sv_value_;

}; // end of class AssumptionRelationReader

class PropertyInterfacecex : public CexExtractor 
{
  public:
  ////Build the Constructor//////
  std::vector<int> get_width;
  typedef std::function<bool(const std::string &n)> filter_t;
  typedef AntFilter filter_r;
    PropertyInterfacecex(const PonoOptions pono_options,
                           const std::string filter,
                           bool reg_only, TransitionSystem & ts);                 
    void get_COI_variable(PonoOptions pono_options_);
    smt::Term cex_parse_to_pono_property(filter_t filter,bool filter_en,filter_r filter_re,bool filter_re_en);
    smt::Term cex_parse_to_pono_property();
    int get_reg_width();
    int get_reg_min_width();
    smt::Term get_extract_from_coi(const std::string val_string, const smt::Term var, std::string var_name,filter_r filter,bool filter_re_en);
    bool is_extracted(const std::string & var_name, std::vector<std::pair<int,int>> & extract_info);
    void get_info(const std::pair<int,int> & out, int & idx0, int & idx1);
  protected:
    TransitionSystem & ts_;
    std::vector<std::string> name_terms;
    std::vector<std::string> qed_name_terms;
    std::vector<std::string> value_terms;
    std::vector<std::string> new_name_terms;
    std::vector<std::string> new_value_terms;
    std::vector<std::string> name_extract;
    std::vector<std::pair<int,int>> extract_val;
    PonoOptions pono_options_;
    bool having_extract;
    is_reg_t is_reg;
    bool is_parse_concat_;
    int startsfrom;
};



class QedCexParser : public SelectiveExtractor  
{
  public:
    typedef Filter filter_t;
    typedef AntFilter filter_r;
  ////Build the Constructor//////
    QedCexParser(const std::string& vcd_file_name,
                 const std::string& filter,
                 const std::string& name_removal,
                 TransitionSystem & ts);
    smt::Term cex2property(filter_t & filter) const;
    smt::Term cex2property_ant(filter_t & filter,filter_r & filter_re) const;
    void get_remaining_var(filter_t & filter, std::vector<std::string> & out) const;
  protected:
    TransitionSystem & ts_;

    is_reg_t is_reg;
};

class coireader 
{
  public:
    typedef Filter filter_t;
    typedef AntFilter filter_r;
  ////Build the Constructor//////
    coireader(std::unordered_map<std::string, std::vector<std::pair<int,int>>>  COI_to_consider,
              std::unordered_map<std::string, std::string> COI_value,
                 const std::string& filter,
                 TransitionSystem & ts):COI_to_consider_(COI_to_consider),COI_value_(COI_value),filter_(filter),ts_(ts){};
    smt::Term coi_cex2property(filter_t & filter) const;
    smt::Term coi_cex2property_ant(filter_t & filter,filter_r & filter_re) const;
  protected:
    TransitionSystem & ts_;
    std::unordered_map<std::string, std::vector<std::pair<int,int>>>  COI_to_consider_;
    std::unordered_map<std::string, std::string>  COI_value_;
    std::string filter_;
};




}  // namespace pono
