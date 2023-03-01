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

#include <iostream>

#include "assert.h"
#include "core/rts.h"
#include "smt-switch/smt.h"
#include "smt-switch/smtlib_reader.h"
#include "utils/exceptions.h"
#include "options/options.h"
#include "cexreader/cex_extract.h"
namespace pono {
class PropertyInterface : public smt::SmtLibReader
{
 public:
  PropertyInterface(std::string filename, TransitionSystem & ts, int step);
  PropertyInterface(std::string filename, TransitionSystem & ts);
  typedef SmtLibReader super;

  smt::Term AddAssertions(const smt::Term &in) const;

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

class PropertyInterfacecex : public CexExtractor 
{
  public:
  ////Build the Constructor//////
  std::vector<int> get_width;
  typedef std::function<bool(const std::string &n)> filter_t;
  typedef std::function<bool(const smt::Term &n)> filter_r;
    PropertyInterfacecex(const PonoOptions pono_options,
                           const std::string& scope,
                           bool reg_only, TransitionSystem & ts);
    void get_COI_variable(PonoOptions pono_options_);
    smt::Term cex_parse_to_pono_property(filter_t filter,bool add_coi);
    smt::Term cex_parse_to_pono_property(filter_r filter_re,bool add_coi);
    smt::Term cex_parse_to_pono_property(filter_t filter,filter_r filter_re,bool add_coi);
    smt::Term cex_parse_to_pono_property();
    smt::Term cex_parse_to_pono_property_coi(filter_r filter_re);
    smt::Term cex_parse_to_pono_property_coi(filter_t filter);
    smt::Term cex_parse_to_pono_property_coi();
    int get_reg_width();
    int get_reg_min_width();
  protected:
    TransitionSystem & ts_;
    std::vector<std::string> name_terms;
    std::vector<std::string> new_name_terms;
    PonoOptions pono_options_;
    is_reg_t is_reg;
};


class QedCexParser : public SelectiveExtractor 
{
  public:
    typedef std::function<bool(const std::string &n)> filter_t;
  ////Build the Constructor//////
    QedCexParser(const std::string& vcd_file_name,
                 const std::string& filter,
                 const std::string& name_removal,
                 TransitionSystem & ts);
    smt::Term cex2property(filter_t filter) const;

    void get_remaining_var(filter_t filter, std::vector<std::string> & out) const;
  protected:
    TransitionSystem & ts_;

    is_reg_t is_reg;
};

}  // namespace pono
