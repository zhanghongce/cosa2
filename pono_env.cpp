/*********************                                                        */
/*! \file
** \verbatim
** Top contributors (to current version):
**   Makai Mann, Ahmed Irfan
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief
**
**
**/

#include <csignal>
#include <iostream>
#include "assert.h"

#ifdef WITH_PROFILING
#include <gperftools/profiler.h>
#endif

#include "smt-switch/boolector_factory.h"
#ifdef WITH_MSAT
#include "smt-switch/msat_factory.h"
#endif
#include "core/fts.h"
#include "frontends/btor2_encoder.h"
#include "frontends/smv_encoder.h"
#include "frontends/vmt_encoder.h"
#include "frontends/property_if.h"
#include "modifiers/control_signals.h"
#include "modifiers/mod_ts_prop.h"
#include "modifiers/prop_monitor.h"
#include "modifiers/static_coi.h"
#include "options/options.h"
#include "printers/btor2_witness_printer.h"
#include "printers/vcd_witness_printer.h"
#include "smt-switch/logging_solver.h"
#include "smt/available_solvers.h"
#include "utils/logger.h"
#include "utils/timestamp.h"
#include "utils/make_provers.h"
#include "utils/ts_analysis.h"
#include "utils/term_analysis.h"
#include "utils/filter.h"
#include <fstream>
#include <filesystem>
#include <queue>

using namespace pono;
using namespace smt;
using namespace std;
namespace fs = std::filesystem;
typedef std::function<bool(const std::string &n)> filter_t;
typedef std::function<bool(const smt::Term &n)> filter_r;
// Note: signal handlers are registered only when profiling is enabled.
void profiling_sig_handler(int sig)
{
  std::string signame;
  switch (sig) {
    case SIGINT: signame = "SIGINT"; break;
    case SIGTERM: signame = "SIGTERM"; break;
    case SIGALRM: signame = "SIGALRM"; break;
    default:
      throw PonoException(
          "Caught unexpected signal"
          "in profiling signal handler.");
  }
  logger.log(0, "\n Signal {} received\n", signame);
#ifdef WITH_PROFILING
  ProfilerFlush();
  ProfilerStop();
#endif
  // Switch back to default handling for signal 'sig' and raise it.
  signal(sig, SIG_DFL);
  raise(sig);
}
// class Filter {
// public:
//   virtual bool operator()(const std::string & n) const = 0;
//   virtual std::string to_string() const = 0;
//   virtual ~Filter() {}
// };

// class MaxWidthFilter : public Filter {
// protected:
//   unsigned width_;
//   const TransitionSystem & ts_;
// public:
//   MaxWidthFilter(unsigned w, const TransitionSystem & ts) : width_(w), ts_(ts) { }
//   bool operator()(const std::string & n) const override {
//     auto pos = ts_.named_terms().find(n);
//     assert(pos != ts_.named_terms().end());
//     auto var = pos->second;
//     if ( var->get_sort()->get_sort_kind() != SortKind::BV )
//       return true;
//     if (var->get_sort()->get_width() <= width_ )
//       return true;
//     return false;
//   }
//   std::string to_string() const override {
//     return "[W<" + std::to_string(width_) +"]";
//   }
// };

// class NameFilter : public Filter{
// protected:
//   unordered_set<string> varset;
//   const TransitionSystem & ts_;
//   bool must_in_;
// public:
//   NameFilter(const vector<string> & v, const TransitionSystem & ts, bool must_in) : ts_(ts), must_in_(must_in)
//      { varset.insert(v.begin(), v.end()); }
//   bool operator()(const std::string & n) const {
//     auto pos1 = varset.find(n);
//     auto pos2 = ts_.named_terms().find(n);
//     assert(pos2 != ts_.named_terms().end());
//     auto var = pos2->second;

//     std::string varname_from_smt2 = var->to_raw_string();
//     if(varname_from_smt2.length() > 2 && varname_from_smt2.front() == '|' 
//       && varname_from_smt2.back() == '|' )
//       varname_from_smt2 = varname_from_smt2.substr(1, varname_from_smt2.length() -2 );
//     auto pos3 = varset.find(varname_from_smt2);

//     bool in_vars  = pos1 != varset.end() || pos3 != varset.end();
//     if(must_in_ && !in_vars)
//       return false;
//     if (!must_in_ && in_vars)
//       return false;
//     return true;
//   }
//   std::string to_string() const override {
//     if(must_in_)
//       return "[Keep " + std::to_string(varset.size()) +" V]";
//     return "[rm " + std::to_string(varset.size()) +"V]";
//   }
// };

// class RepeatFilter{
//   public:  
//     UnorderedTermSet out;
//     std::vector<UnorderedTermSet> out_vec;
//     // RepeatFilter(const std::string filename, TransitionSystem &ts, int step, int num_consider) : filename_(filename),ts_(ts), step_(step),num_consider_(num_consider){
//     //     PropertyInterface prop_inv(filename_,ts_,step,num_consider);
//     //     auto assumption = prop_inv.con_assumption;
        
//     //     for(auto &it:assumption)
//     //      { 
//     //       get_predicates(ts.get_solver(),it,out,false,false,true);
//     //       out_vec.push_back(out);
//     //      }
          
//     // };
//     RepeatFilter(const std::string filename, TransitionSystem &ts, int step) : filename_(filename),ts_(ts), step_(step){
//         PropertyInterface prop_inv(filename_,ts_,step);
//         auto assumption = prop_inv.assumption;
        
//         // auto assumption = assumptions_.at(i);
//         get_predicates(ts.get_solver(),assumption,out,false,false,true);
          
//     };
//     ~RepeatFilter() {}
//   bool operator()(const Term &n) const{
//       // UnorderedTermSet::const_iterator got = out.find(n);
   
//         for (Term it: out){
//           if (it->to_string() == n ->to_string()){
//             return true;
//           }
//     }
//     return false;
//   }
//   // bool operator()(const Term &n) const{
//   //     // UnorderedTermSet::const_iterator got = out.find(n);
//   //   int count = 0;
//   //   int count1 = 0;
//   //   for(auto output:out_vec){
//   //     for (Term it: output){
//   //         count1 = count1 +1;
//   //         if (it->to_string() == n ->to_string()){
//   //           count =count +1;
//   //           break;
//   //         }
//   //     }
//   //     if(count == num_consider_)
//   //       return true;
//   //     }
//   //   return false;
//   // }

//   protected:
//     std::string filename_;
//     TransitionSystem & ts_;
//     smt::Term assumption;
//     int step_ ;
//     int num_consider_;
// };

// struct FilterConcat : public Filter{
//   list<shared_ptr<Filter>> filters;
//   bool operator()(const std::string & n) const override {
//     for (const auto & f : filters) {
//       if (!(*f)(n))
//         return false;
//     }
//     return true;
//   }
//   std::string to_string() const override {
//     std::string ret;
//     for (const auto & f : filters) 
//       ret += f->to_string();
//     return ret;
//   }
// };

bool check_for_inductiveness(const Term & prop, const TransitionSystem & ts) {
  Term init = ts.init();
  Term trans = ts.trans();
  const auto & s = ts.solver();
  s->push();
  s->assert_formula(init);
  s->assert_formula(s->make_term(Not, prop));
  auto r = s->check_sat();
  s->pop();
  if (r.is_sat())
    return false;
  
  // s->push();
  //   s->assert_formula(prop);
  //   s->assert_formula(trans);
  //   s->assert_formula(s->make_term(Not, ts.next(prop)));
  //   r = s->check_sat();
  // s->pop();
  // if (r.is_sat())
  //   return false;

  return true;
}


// Term get_term_with_dual_fil(FilterConcat filter, int num_consider, PropertyInterfacecex prop_cex, TransitionSystem &fts, int step, std::string filename_origin){
//     std::cout<<"The current reduction property cannot be used."<<std::endl;
//     RepeatFilter filter_re(filename_origin,fts,step);
//     Term prop_filter;
//     prop_filter = prop_cex.cex_parse_to_pono_property(filter,filter_re);
//     std::cout <<"The new reduction property for the width filter and repeat filter is : "<< prop_filter->to_raw_string() << std::endl;
//     return prop_filter;

// }


// Term get_term_with_width_fil(FilterConcat filter, PropertyInterfacecex prop_cex){
//       std::cout<<"The current reduction property cannot be used."<<std::endl;
//       Term prop_filter_single;
//       prop_filter_single = prop_cex.cex_parse_to_pono_property(filter);
//       std::cout <<"The new reduction property for the width filter is : "<< prop_filter_single->to_raw_string() << std::endl;
//       return prop_filter_single;
// }



// Term get_term_with_repeat_fil(int num_consider, PropertyInterfacecex prop_cex, TransitionSystem &fts, int step, std::string filename_origin){
//         std::cout<<"The current reduction property cannot be used."<<std::endl;
//         RepeatFilter filter_re(filename_origin,fts,step);
//         Term prop_filter_single_re;
//         prop_filter_single_re = prop_cex.cex_parse_to_pono_property(filter_re,filter);
//         std::cout <<"The new reduction property for the repeat filter is : "<< prop_filter_single_re->to_raw_string() << std::endl;
//         return prop_filter_single_re;
// }

Term get_term_without_fil( PropertyInterfacecex prop_cex){
      std::cout <<"We cannot get any reduction."<<std::endl;
      Term prop;
      prop = prop_cex.cex_parse_to_pono_property();
      std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
      return prop;
}
ProverResult check_prop_inv(PonoOptions pono_options,
                        Term & prop,
                        TransitionSystem & ts,
                        const SmtSolver & s,
                        std::vector<UnorderedTermMap> & cex,
                        int step)
{
  // get property name before it is rewritten
  const string prop_name = ts.get_name(prop);
  logger.log(1, "Solving property: {}", prop_name);
  logger.log(3, "INIT:\n{}", ts.init());
  logger.log(3, "TRANS:\n{}", ts.trans());

  // modify the transition system and property based on options
  if (!pono_options.clock_name_.empty()) {
    Term clock_symbol = ts.lookup(pono_options.clock_name_);
    toggle_clock(ts, clock_symbol);
  }
  if (!pono_options.reset_name_.empty()) {
    std::string reset_name = pono_options.reset_name_;
    bool negative_reset = false;
    if (reset_name.at(0) == '~') {
      reset_name = reset_name.substr(1, reset_name.length() - 1);
      negative_reset = true;
    }
    Term reset_symbol = ts.lookup(reset_name);
    if (negative_reset) {
      SortKind sk = reset_symbol->get_sort()->get_sort_kind();
      reset_symbol = (sk == BV) ? s->make_term(BVNot, reset_symbol)
                                : s->make_term(Not, reset_symbol);
    }
    Term reset_done = add_reset_seq(ts, reset_symbol, pono_options.reset_bnd_);
    // guard the property with reset_done
    prop = ts.solver()->make_term(Implies, reset_done, prop);
  }


  if (pono_options.static_coi_) {
    /* Compute the set of state/input variables related to the
       bad-state property. Based on that information, rebuild the
       transition relation of the transition system. */
    StaticConeOfInfluence coi(ts, { prop }, pono_options.verbosity_);
  }

  if (pono_options.pseudo_init_prop_) {
    ts = pseudo_init_and_prop(ts, prop);
  }

  if (pono_options.promote_inputvars_) {
    ts = promote_inputvars(ts);
    assert(!ts.inputvars().size());
  }

  if (!ts.only_curr(prop)) {
    logger.log(1,
               "Got next state or input variables in property. "
               "Generating a monitor state.");
    prop = add_prop_monitor(ts, prop);
  }

  if (pono_options.assume_prop_) {
    // NOTE: crucial that pseudo_init_prop and add_prop_monitor passes are
    // before this pass. Can't assume the non-delayed prop and also
    // delay it
    prop_in_trans(ts, prop);
  }

  Property p(s, prop, prop_name);

  // end modification of the transition system and property
  // if (step >0)
  //   s->set_opt("incremental","true");
  Engine eng = pono_options.engine_;

  std::shared_ptr<Prover> prover;
  if (pono_options.cegp_abs_vals_) {
    prover = make_cegar_values_prover(eng, p, ts, s, pono_options);
  } else if (pono_options.ceg_bv_arith_) {
    prover = make_cegar_bv_arith_prover(eng, p, ts, s, pono_options);
  } else if (pono_options.ceg_prophecy_arrays_) {
    prover = make_ceg_proph_prover(eng, p, ts, s, pono_options);
  } else {
    prover = make_prover(eng, p, ts, s, pono_options);
  }
  assert(prover);

  // TODO: handle this in a more elegant way in the future
  //       consider calling prover for CegProphecyArrays (so that underlying
  //       model checker runs prove unbounded) or possibly, have a command line
  //       flag to pick between the two
  ProverResult r;
  if (pono_options.engine_ == MSAT_IC3IA)
  {
    // HACK MSAT_IC3IA does not support check_until
    r = prover->prove();
  }
  else
  {
    r = prover->check_until(pono_options.bound_);
  }

  if (r == FALSE && pono_options.witness_) {
    bool success = prover->witness(cex);
    if (!success) {
      logger.log(
          0,
          "Only got a partial witness from engine. Not suitable for printing.");
    }
  }

  Term invar;
  if (r == TRUE){ 
  if (r == TRUE && (pono_options.show_invar_ || pono_options.check_invar_)) {
    try {
      invar = prover->invar();
    }
    catch (PonoException & e) {
      std::cout << "Engine " << pono_options.engine_
                << " does not support getting the invariant." << std::endl;
    }
  }

    auto cvc5solver = smt::Cvc5SolverFactory::create(false);
    auto transferer = smt::TermTranslator(cvc5solver);
    auto invar_in_cvc5 = transferer.transfer_term(invar);
    // auto invar_in_cvc5_origin = transferer.transfer_term(invar);
    smt::UnorderedTermSet varset;
   

      varset = get_free_symbols(invar_in_cvc5);
      auto invar_varname_rewritten = name_changed(invar_in_cvc5, varset, cvc5solver, "RTL.");
      auto varset_new = get_free_symbols(invar_varname_rewritten);
      std::string sort_list,sort_list_origin;
      smt_lib2_front(varset_new, sort_list);
      smt_lib2_front(varset, sort_list_origin);
      std::string folderPath = pono_options.smt_path_;
      std::string origin_smt = folderPath + "/inv_origin.smt2"; 

        if(step == 0){
          std::string step_char = to_string(step);
          std::string filename = folderPath + "/" + "inv.smt2"; 
          ofstream res1(origin_smt.c_str());        
          ofstream res(filename.c_str());
          res<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list<<")"<<" "<<"Bool"<<" "<<invar_varname_rewritten->to_string()<<")"<<endl;
          res1<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list_origin<<")"<<" "<<"Bool"<<" "<<invar_in_cvc5->to_string()<<")"<<endl;
        }
        else{
          std::string step_char = to_string(step);
          ofstream res;
          ofstream res1;
          std::string filename = folderPath + "/" + "inv"  +".smt2";
          res.open(filename, ios::app);
          res1.open(origin_smt, ios::app);
          res<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list<<")"<<" "<<"Bool"<<" "<<invar_varname_rewritten->to_string()<<")"<<endl;
          res1<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list_origin<<")"<<" "<<"Bool"<<" "<<invar_in_cvc5->to_string()<<")"<<endl;
        }
  

  if (r == TRUE && pono_options.show_invar_ && invar) {
    logger.log(0, "INVAR: {}", invar_in_cvc5);
  }

  if (r == TRUE && pono_options.check_invar_ && invar) {
    bool invar_passes = check_invar(ts, p.prop(), invar);
    std::cout << "Invariant Check " << (invar_passes ? "PASSED" : "FAILED")
              << std::endl;
    if (!invar_passes) {
      // shouldn't return true if invariant is incorrect
      throw PonoException("Invariant Check FAILED");
    }
  }
  }
  // s->reset();
  return r;
}
void write_inv_to_file(const smt::Term & invar, ostream & outf, ostream & outf_origin, unsigned step, const std::string & varname_prefix) {
    auto cvc5solver = smt::Cvc5SolverFactory::create(false);
    auto transferer = smt::TermTranslator(cvc5solver);
    auto invar_in_cvc5 = transferer.transfer_term(invar);

    smt::UnorderedTermSet varset;
   
    varset = get_free_symbols(invar_in_cvc5);
    auto invar_varname_rewritten = varname_prefix.empty() ?
      invar_in_cvc5 : name_changed(invar_in_cvc5, varset, cvc5solver, varname_prefix);
    auto varset_new = get_free_symbols(invar_varname_rewritten);

    std::string sort_list,sort_list_origin;
    smt_lib2_front(varset_new, sort_list);
    smt_lib2_front(varset, sort_list_origin);
    std::string step_char = to_string(step);
    outf<<"(define-fun assumption." << step_char << " ("<<sort_list<<") Bool "<<invar_varname_rewritten->to_string()<<")"<<endl;
    outf_origin<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list_origin<<")"<<" "<<"Bool"<<" "<<invar_in_cvc5->to_string()<<")"<<endl;
}

ProverResult check_prop(PonoOptions pono_options,
                        const Term & prop_old,
                        const TransitionSystem & original_ts,
                        const SmtSolver & solver_old,
                        std::vector<UnorderedTermMap> & cex,
                        SolverEnum se,
                        Engine e,
                        unsigned step)
{
  // create a solver for this
  auto new_solver = create_solver_for(se, e, true,false);
  TermTranslator to_new_solver(new_solver);
  TermTranslator to_old_solver(solver_old);
  FunctionalTransitionSystem new_fts(original_ts,to_new_solver);
  std::vector<UnorderedTermMap> local_cex;
  std::string filename_origin = pono_options.smt_path_ + "/" + "inv_origin.smt2";
  if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
      {       
        PropertyInterface add_to_frame(filename_origin, new_fts);
        add_to_frame.AddAssumptionsToTS();
      }
  Term prop = to_new_solver.transfer_term(prop_old);

  // get property name before it is rewritten
  const string prop_name = new_fts.get_name(prop);
  logger.log(1, "Solving property: {}", prop_name);
  logger.log(3, "INIT:\n{}", new_fts.init());
  logger.log(3, "TRANS:\n{}", new_fts.trans());

  // modify the transition system and property based on options
  if (!pono_options.clock_name_.empty()) {
    Term clock_symbol = new_fts.lookup(pono_options.clock_name_);
    toggle_clock(new_fts, clock_symbol);
  }
  if (!pono_options.reset_name_.empty()) {
    std::string reset_name = pono_options.reset_name_;
    bool negative_reset = false;
    if (reset_name.at(0) == '~') {
      reset_name = reset_name.substr(1, reset_name.length() - 1);
      negative_reset = true;
    }
    Term reset_symbol = new_fts.lookup(reset_name);
    if (negative_reset) {
      SortKind sk = reset_symbol->get_sort()->get_sort_kind();
      reset_symbol = (sk == BV) ? new_solver->make_term(BVNot, reset_symbol)
                                : new_solver->make_term(Not, reset_symbol);
    }
    Term reset_done = add_reset_seq(new_fts, reset_symbol, pono_options.reset_bnd_);
    // guard the property with reset_done
    prop = new_fts.solver()->make_term(Implies, reset_done, prop);
  }


  if (pono_options.static_coi_) {
    /* Compute the set of state/input variables related to the
       bad-state property. Based on that information, rebuild the
       transition relation of the transition system. */
    StaticConeOfInfluence coi(new_fts, { prop }, pono_options.verbosity_);
  }

  if (pono_options.pseudo_init_prop_) {
    new_fts = pseudo_init_and_prop(new_fts, prop);
  }

  if (pono_options.promote_inputvars_) {
    new_fts = promote_inputvars(new_fts);
    assert(!new_fts.inputvars().size());
  }

  if (!new_fts.only_curr(prop)) {
    logger.log(1,
               "Got next state or input variables in property. "
               "Generating a monitor state.");
    prop = add_prop_monitor(new_fts, prop);
  }

  if (pono_options.assume_prop_) {
    // NOTE: crucial that pseudo_init_prop and add_prop_monitor passes are
    // before this pass. Can't assume the non-delayed prop and also
    // delay it
    prop_in_trans(new_fts, prop);
  }

  Property p(new_solver, prop, prop_name);

  // end modification of the transition system and property

  Engine eng = pono_options.engine_;

  std::shared_ptr<Prover> prover;
  if (pono_options.cegp_abs_vals_) {
    prover = make_cegar_values_prover(eng, p, new_fts, new_solver, pono_options);
  } else if (pono_options.ceg_bv_arith_) {
    prover = make_cegar_bv_arith_prover(eng, p, new_fts, new_solver, pono_options);
  } else if (pono_options.ceg_prophecy_arrays_) {
    prover = make_ceg_proph_prover(eng, p, new_fts, new_solver, pono_options);
  } else {
    prover = make_prover(eng, p, new_fts, new_solver, pono_options);
  }
  assert(prover);

  // TODO: handle this in a more elegant way in the future
  //       consider calling prover for CegProphecyArrays (so that underlying
  //       model checker runs prove unbounded) or possibly, have a command line
  //       flag to pick between the two
  ProverResult r;
  if (pono_options.engine_ == MSAT_IC3IA)
  {
    // HACK MSAT_IC3IA does not support check_until
    r = prover->prove();
  }
  else
  {
    r = prover->check_until(pono_options.bound_);
  }

  // if (r == FALSE && pono_options.witness_) {
  //   bool success = prover->witness(local_cex);
  //   if (!success) {
  //     logger.log(
  //         0,
  //         "Only got a partial witness from engine. Not suitable for printing.");
  //   }
  // }

  Term invar;
  if (r == TRUE && (pono_options.show_invar_ || pono_options.check_invar_)) {
    try {
      invar = prover->invar();

      // write_inv_to_file(invar, outf,outf_origin, step, "RTL.");
    }
    catch (PonoException & e) {
      std::cout << "Engine " << pono_options.engine_
                << " does not support getting the invariant." << std::endl;
      // outf << "(noinvar)" << endl;      
    }

    std::string folderPath = pono_options.smt_path_;
    std::string filename = folderPath + "/" + "inv.smt2"; 
    auto cvc5solver = smt::Cvc5SolverFactory::create(false);
    auto transferer = smt::TermTranslator(cvc5solver);
    auto invar_in_cvc5 = transferer.transfer_term(invar);
    // auto invar_in_cvc5_origin = transferer.transfer_term(invar);
    smt::UnorderedTermSet varset;
   

      varset = get_free_symbols(invar_in_cvc5);
      auto invar_varname_rewritten = name_changed(invar_in_cvc5, varset, cvc5solver, "RTL.");
      auto varset_new = get_free_symbols(invar_varname_rewritten);
      std::string sort_list,sort_list_origin;
      smt_lib2_front(varset_new, sort_list);
      smt_lib2_front(varset, sort_list_origin);
      // std::string folderPath = pono_options.smt_path_;
      std::string origin_smt = folderPath + "/inv_origin.smt2"; 
    // std::ofstream outf(filename, std::ofstream::out | std::ofstream::app);
    // std::ofstream outf_origin(origin_smt, std::ofstream::out | std::ofstream::app);
    if(step == 0){
      std::string step_char = to_string(step);
      std::string filename = folderPath + "/" + "inv.smt2"; 
      ofstream res1(origin_smt.c_str());        
      ofstream res(filename.c_str());
      res<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list<<")"<<" "<<"Bool"<<" "<<invar_varname_rewritten->to_string()<<")"<<endl;
      res1<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list_origin<<")"<<" "<<"Bool"<<" "<<invar_in_cvc5->to_string()<<")"<<endl;
    }
    else{
      std::string step_char = to_string(step);
      ofstream res;
      ofstream res1;
      std::string filename = folderPath + "/" + "inv"  +".smt2";
      res.open(filename, ios::app);
      res1.open(origin_smt, ios::app);
      res<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list<<")"<<" "<<"Bool"<<" "<<invar_varname_rewritten->to_string()<<")"<<endl;
      res1<<"("<<"define-fun"<<" "<<"assumption." << step_char << " "<<"("<<sort_list_origin<<")"<<" "<<"Bool"<<" "<<invar_in_cvc5->to_string()<<")"<<endl;
        }


  }
    

  if (r == TRUE && pono_options.show_invar_ && invar) {
    logger.log(0, "INVAR: {}", invar);
  }

  if (r == TRUE && pono_options.check_invar_ && invar) {
    bool invar_passes = check_invar(new_fts, p.prop(), invar);
    std::cout << "Invariant Check " << (invar_passes ? "PASSED" : "FAILED")
              << std::endl;
    if (!invar_passes) {
      // shouldn't return true if invariant is incorrect
      throw PonoException("Invariant Check FAILED");
    }
  }

  // now translate cex back to original 
  for (const auto & frame: local_cex) {
    cex.push_back(UnorderedTermMap());
    for(const auto & var_val : frame) {
      cex.back().emplace(to_old_solver.transfer_term(var_val.first, false), 
                         to_old_solver.transfer_term(var_val.second, false));
    }
  }

  return r;
}

// int check_repeat(Term prop_filter,UnorderedTermSet prop_check){
//     int idx = 0;
//     for (Term it: prop_check){
//       if (it->to_string()==prop_filter->to_string()){
//         idx = 1;
//         break;
//       } 
//     }
//     return idx;
// }

bool check_previous(Term prop_filter, UnorderedTermSet prop_check)
{
  for (auto prop:prop_check){
    if(prop->to_string()== prop_filter->to_string())
      return true;
  }
  return false;
}
ProverResult get_prop_inv(PonoOptions pono_options, 
                  TransitionSystem fts, 
                  int step, 
                  SmtSolver s,
                  vector<UnorderedTermMap> &cex)
{
      ProverResult res;
      PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);
      UnorderedTermSet prop_check;
      pono_options.sygus_initial_term_width_= prop_cex.get_reg_width();
      FilterConcat filter;
      Term prop_filter;
      std::queue<pair<Term,std::string>> prop_queue;
      // UnorderedTermSet prop_check;
      std::string filename_origin = pono_options.smt_path_ + "/" + "inv_origin.smt2";
      filter.filters.push_back(std::make_shared<MaxWidthFilter>(pono_options.sygus_initial_term_width_,fts));
      bool inductiveness;
      if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
      {       
        PropertyInterface add_to_frame(filename_origin, fts);
        add_to_frame.AddAssumptionsToTS();
      }      
      bool repeat_first = true;
      bool re;
      if(step>0){
          Antfilter filter_re(filename_origin,fts,step);
          if(repeat_first){
            prop_filter = prop_cex.cex_parse_to_pono_property(filter,filter_re);
            if(((inductiveness = check_for_inductiveness(prop_filter, fts)) == true))
            {
                prop_queue.push(make_pair(prop_filter,"dual filter"));
                prop_check.insert(prop_filter);
            }
            prop_filter = prop_cex.cex_parse_to_pono_property(filter_re);
            if((prop_filter!=nullptr)&&((inductiveness = check_for_inductiveness(prop_filter, fts)) == true))
            {
                re = check_previous(prop_filter,prop_check);
                if(re==false){               
                  prop_queue.push(make_pair(prop_filter,"repeat filter"));
                  prop_check.insert(prop_filter);
                }
            }
            prop_filter = prop_cex.cex_parse_to_pono_property(filter);
            if(((inductiveness = check_for_inductiveness(prop_filter, fts)) == true)){
                re = check_previous(prop_filter,prop_check);
                if(re==false){
                prop_queue.push(make_pair(prop_filter,"width filter"));
                prop_check.insert(prop_filter);
                }
            }
            prop_filter = prop_cex.cex_parse_to_pono_property();
            prop_queue.push(make_pair(prop_filter,"without filter"));
          }
          else{
            prop_filter = prop_cex.cex_parse_to_pono_property(filter,filter_re);
            if(((inductiveness = check_for_inductiveness(prop_filter, fts)) == true)){
              prop_queue.push(make_pair(prop_filter,"dual filter"));
              prop_check.insert(prop_filter);
            }
            prop_filter = prop_cex.cex_parse_to_pono_property(filter);
            if(((inductiveness = check_for_inductiveness(prop_filter, fts)) == true)){
                re = check_previous(prop_filter,prop_check);
                if(re==false){
                prop_queue.push(make_pair(prop_filter,"width filter"));
                prop_check.insert(prop_filter);
                }
              }
            prop_filter = prop_cex.cex_parse_to_pono_property(filter_re);
            if((prop_filter!=nullptr)&&((inductiveness = check_for_inductiveness(prop_filter, fts)) == true)){
                re = check_previous(prop_filter,prop_check);
                if(re==false){               
                  prop_queue.push(make_pair(prop_filter,"repeat filter"));
                  prop_check.insert(prop_filter);
                }
            }
            prop_filter = prop_cex.cex_parse_to_pono_property();
            // auto idx = check_repeat(prop_filter, prop_check);
            // if(idx == 0){
              prop_queue.push(make_pair(prop_filter,"without filter"));
            // }
          }
        }
        else{
          prop_filter = prop_cex.cex_parse_to_pono_property(filter);
          if(((inductiveness = check_for_inductiveness(prop_filter, fts)) == true)){
            prop_queue.push(make_pair(prop_filter,"width filter"));
            // prop_check.insert(prop_filter);
          } 
          prop_filter = prop_cex.cex_parse_to_pono_property();
          // auto idx = check_repeat(prop_filter, prop_check);
          // if(idx = 0){
          prop_queue.push(make_pair(prop_filter,"without filter"));
            // }
        }
      // std::cout <<"The initial reduction property for the filter is: "<< prop_filter->to_raw_string() << std::endl;
      Term prop;
      std::string fil_name;
      prop = prop_queue.front().first;
      fil_name = prop_queue.front().second;
      prop_queue.pop();
      std::cout <<"The initial reduction property for the filter is: "<< prop->to_raw_string() <<std::endl;
      std::cout << "The filter we use is: "<< fil_name <<std::endl; 
      while ((res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step))!=TRUE)
      {
        if(prop_queue.empty()==true){
          return res;
        }
        prop = prop_queue.front().first;
        fil_name = prop_queue.front().second;
        if (prop_queue.size()==1){
          pono_options.bound_ = 150;
        }
        prop_queue.pop();
        std::cout << "The original filter cannot be used." <<std::endl;
        std::cout <<"The new reduction property for the filter is: "<< prop->to_raw_string() <<std::endl;
        std::cout << "The filter we use is: "<< fil_name <<std::endl;
      }
      return res;
}




int main(int argc, char ** argv)
{
  auto begin_time_stamp = timestamp();

  PonoOptions pono_options;
  ProverResult res = pono_options.parse_and_set_options(argc, argv);
  if (res == ERROR) return res;
  // expected result returned by option parsing and setting is
  // 'pono::UNKNOWN', indicating that options were correctly set and
  // 'ERROR' otherwise, e.g. wrong command line options or
  // incompatible options were passed
  assert(res == pono::UNKNOWN);

  // set logger verbosity -- can only be set once
  logger.set_verbosity(pono_options.verbosity_);

  // For profiling: set signal handlers for common signals to abort
  // program.  This is necessary to gracefully stop profiling when,
  // e.g., an external time limit is enforced to stop the program.
  if (!pono_options.profiling_log_filename_.empty()) {
    signal(SIGINT, profiling_sig_handler);
    signal(SIGTERM, profiling_sig_handler);
    signal(SIGALRM, profiling_sig_handler);
#ifdef WITH_PROFILING
    logger.log(
        0, "Profiling log filename: {}", pono_options.profiling_log_filename_);
    ProfilerStart(pono_options.profiling_log_filename_.c_str());
#endif
  }


    // no logging by default
    // could create an option for logging solvers in the future

    // HACK bool_model_generation for IC3IA breaks CegProphecyArrays
    // longer term fix will use a different solver in CegProphecyArrays,
    // but for now just force full model generation in that case

    SmtSolver s = create_solver_for(pono_options.smt_solver_,
                                    pono_options.engine_,
                                    true,
                                    pono_options.ceg_prophecy_arrays_);
    

    // new AbsSmtSolver s = BoolectorSolverFactory::create();
    s->set_opt("incremental","true");
    if (pono_options.logging_smt_solver_) {
      s = make_shared<LoggingSolver>(s);
      // TODO consider setting base-context-1 for BTOR here
      //      to allow resetting assertions
    }

    // limitations with COI
    if (pono_options.static_coi_) {
      if (pono_options.pseudo_init_prop_) {
        // Issue explained here:
        // https://github.com/upscale-project/pono/pull/160 will be resolved
        // once state variables removed by COI are removed from init then should
        // do static-coi BEFORE mod-init-prop
        logger.log(0,
                   "Warning: --mod-init-prop and --static-coi don't work "
                   "well together currently.");
      }
    }
    // default options for IC3SA
    if (pono_options.engine_ == IC3SA_ENGINE) {
      // IC3SA expects all state variables
      pono_options.promote_inputvars_ = true;
    }

    // TODO: make this less ugly, just need to keep it in scope if using
    //       it would be better to have a generic encoder
    //       and also only create the transition system once
    string file_ext = pono_options.filename_.substr(
        pono_options.filename_.find_last_of(".") + 1);
    if (file_ext == "btor2" || file_ext == "btor") {
      logger.log(2, "Parsing BTOR2 file: {}", pono_options.filename_);
      FunctionalTransitionSystem fts(s);
      BTOR2Encoder btor_enc(pono_options.filename_, fts);
    // Term prop;
    Term prop_filter;
    // Term prop_filter_single;
    // Term prop_filter_single_re;
    if (pono_options.find_environment_invariant_){
      assert(!pono_options.cex_reader_.empty());
      int step = pono_options.step_;
      // FilterConcat filter;
      // PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);
      // pono_options.sygus_initial_term_width_= prop_cex.get_reg_width();
      // filter.filters.push_back(std::make_shared<MaxWidthFilter>(pono_options.sygus_initial_term_width_,fts));
      // std::string filename_origin = pono_options.smt_path_ + "/" + "inv_origin.smt2";
      // int num_consider = 1;
      std::cout <<"Now the step is: "<<to_string(step)<<std::endl;
  //     if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //     {       
  //       PropertyInterface add_to_frame(filename_origin, fts);
  //       add_to_frame.AddAssumptionsToTS();
  //     }
  //     if(step>0){
  //         RepeatFilter filter_re(filename_origin,fts,step);
  //         prop_filter = prop_cex.cex_parse_to_pono_property(filter,filter_re);
  //       }
  //       else{
  //         prop_filter = prop_cex.cex_parse_to_pono_property(filter);
  //       }
  //   bool inductiveness;
  //     // int step = pono_options.step_;
    vector<UnorderedTermMap> cex;
  //   std::cout <<"The initial property is : "<< prop_filter->to_raw_string() << std::endl;
  //   if( ((inductiveness = check_for_inductiveness(prop_filter, fts)) == false)&&(step>0)) {
  //     RepeatFilter filter_re(filename_origin,fts,step);
  //     std::cout<<"The reduction property cannot be used"<<std::endl;
  //     Term prop_filter_single;
  //     prop_filter_single = prop_cex.cex_parse_to_pono_property(filter);
  //     std::cout <<"The new reduction property for the width filter is : "<< prop_filter_single->to_raw_string() << std::endl;
  //     if((prop_filter_single == prop_filter)||((inductiveness = check_for_inductiveness(prop_filter_single, fts)) == false)){
  //       std::cout<<"The reduction property cannot be used"<<std::endl;
  //       Term prop_filter_single_re;
  //       prop_filter_single_re = prop_cex.cex_parse_to_pono_property(filter_re);
  //       std::cout <<"The new reduction property for the repeat filter is : "<< prop_filter_single_re->to_raw_string() << std::endl;
  //       if (((inductiveness = check_for_inductiveness(prop_filter_single_re, fts)) == false)){
  //         std::cout <<"We cannot get any reduction."<<std::endl;
  //         Term prop;
  //         prop = prop_cex.cex_parse_to_pono_property();
  //         std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //         // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //         res = check_prop_inv(pono_options, prop, fts, s, cex, step);
  //       }
  //       else{
  //           // res = check_prop(pono_options, prop_filter_single_re, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //           res = check_prop_inv(pono_options, prop_filter_single_re, fts, s, cex, step);
  //           if(res ==FALSE){
  //           s.reset();
  //           SmtSolver s = create_solver_for(pono_options.smt_solver_,
  //                                         pono_options.engine_,
  //                                         true,
  //                                         pono_options.ceg_prophecy_arrays_);
  //           FunctionalTransitionSystem fts(s);
  //           BTOR2Encoder btor_enc(pono_options.filename_, fts);
  //           PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);   
  //           if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //           {       
  //             PropertyInterface add_to_frame(filename_origin, fts);
  //             add_to_frame.AddAssumptionsToTS();
  //           }
  //           cex.clear();         
  //           std::cout <<"We cannot get any reduction."<<std::endl;
  //           Term prop;
  //           prop = prop_cex.cex_parse_to_pono_property();
  //           std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //           // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //           res = check_prop_inv(pono_options, prop, fts, s, cex, step);

  //         }
  //       }
  //     }
  //     else{
  //       // res = check_prop(pono_options, prop_filter_single, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //       res = check_prop_inv(pono_options, prop_filter_single, fts, s, cex, step);
  //       if (res ==FALSE){
  //         std::cout<<"The reduction property cannot be used"<<std::endl;
  //         s.reset();
  //         SmtSolver s = create_solver_for(pono_options.smt_solver_,
  //                                       pono_options.engine_,
  //                                       true,
  //                                       pono_options.ceg_prophecy_arrays_);
  //         FunctionalTransitionSystem fts(s);
  //         BTOR2Encoder btor_enc(pono_options.filename_, fts);
  //         PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);
  //         if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //           {       
  //             PropertyInterface add_to_frame(filename_origin, fts);
  //             add_to_frame.AddAssumptionsToTS();
  //           }
  //         Term prop_filter_single_re;
  //         cex.clear();
  //         prop_filter_single_re = prop_cex.cex_parse_to_pono_property(filter_re);
  //         std::cout <<"The new reduction property for the repeat filter is : "<< prop_filter_single_re->to_raw_string() << std::endl;
  //         if (((inductiveness = check_for_inductiveness(prop_filter_single_re, fts)) == false)){
  //           std::cout <<"We cannot get any reduction."<<std::endl;
  //           Term prop;
  //           std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //           res = check_prop_inv(pono_options, prop, fts, s, cex,step);
  //           // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //         }
  //         else{
  //           res = check_prop_inv(pono_options, prop_filter_single_re, fts, s, cex, step);
  //           // res = check_prop(pono_options, prop_filter_single_re, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //           if(res ==FALSE){
  //             std::cout <<"We cannot get any reduction."<<std::endl;
  //             s.reset();
  //             SmtSolver s = create_solver_for(pono_options.smt_solver_,
  //                                           pono_options.engine_,
  //                                           true,
  //                                           pono_options.ceg_prophecy_arrays_);
  //             FunctionalTransitionSystem fts(s);
  //             BTOR2Encoder btor_enc(pono_options.filename_, fts);
  //             PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);
  //             if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //             {       
  //               PropertyInterface add_to_frame(filename_origin, fts);
  //               add_to_frame.AddAssumptionsToTS();
  //             }
  //             Term prop;
  //             cex.clear();
  //             prop = prop_cex.cex_parse_to_pono_property();
  //             std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //             res = check_prop_inv(pono_options, prop, fts, s, cex, step);
  //             // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //         }
  //       }
  //     }
  //     }    
  //   }
  
  // else{
  //     // std::cout << prop_filter->to_raw_string() << std::endl;
  //     res = check_prop_inv(pono_options, prop_filter, fts, s, cex, step);
  //     // res = check_prop(pono_options, prop_filter, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //     if (res ==FALSE){
  //       s.reset();
  //       SmtSolver s = create_solver_for(pono_options.smt_solver_,
  //                                     pono_options.engine_,
  //                                     true,
  //                                     pono_options.ceg_prophecy_arrays_);
  //       FunctionalTransitionSystem fts(s);
  //       BTOR2Encoder btor_enc(pono_options.filename_, fts);
  //       PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);
  //       if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //       {       
  //         PropertyInterface add_to_frame(filename_origin, fts);
  //         add_to_frame.AddAssumptionsToTS();
  //       }
  //       cex.clear();
  //       if(step==0){
  //           std::cout <<"We cannot get any reduction."<<std::endl;
  //           Term prop;
  //           prop = prop_cex.cex_parse_to_pono_property();
  //           std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //           res = check_prop_inv(pono_options, prop, fts, s, cex, step);
  //           // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
            
  //       }
  //       else{
  //         RepeatFilter filter_re(filename_origin,fts,step);
  //         Term prop_filter_single;
  //         std::cout<<"The reduction property cannot be used"<<std::endl;
  //         prop_filter_single = prop_cex.cex_parse_to_pono_property(filter);
  //         std::cout <<"The new reduction property for the width filter is : "<< prop_filter_single->to_raw_string() << std::endl;
  //         if((prop_filter_single == prop_filter)||((inductiveness = check_for_inductiveness(prop_filter_single, fts)) == false)){
  //           std::cout<<"The reduction property cannot be used"<<std::endl;
  //           Term prop_filter_single_re;
  //           prop_filter_single_re = prop_cex.cex_parse_to_pono_property(filter_re);
  //           std::cout <<"The new reduction property for the repeat filter is : "<< prop_filter_single_re->to_raw_string() << std::endl;
  //           if (((inductiveness = check_for_inductiveness(prop_filter_single_re, fts)) == false)){
  //             std::cout <<"We cannot get any reduction."<<std::endl;
  //             Term prop;
  //             std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //             res = check_prop_inv(pono_options, prop, fts, s, cex,step);
  //             // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //           }
  //           else{
  //             res = check_prop_inv(pono_options, prop_filter_single_re, fts, s, cex,step);
  //             // res = check_prop(pono_options, prop_filter_single_re, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //             if(res ==FALSE){
  //               std::cout <<"We cannot get any reduction."<<std::endl;
  //               s.reset();
  //               SmtSolver s = create_solver_for(pono_options.smt_solver_,
  //                                             pono_options.engine_,
  //                                             true,
  //                                             pono_options.ceg_prophecy_arrays_);
  //               FunctionalTransitionSystem fts(s);
  //               BTOR2Encoder btor_enc(pono_options.filename_, fts);
  //               PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);
  //               if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //               {       
  //                 PropertyInterface add_to_frame(filename_origin, fts);
  //                 add_to_frame.AddAssumptionsToTS();
  //               }
  //               Term prop;
  //               cex.clear();
  //               prop = prop_cex.cex_parse_to_pono_property();
  //               std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //               res = check_prop_inv(pono_options, prop, fts, s, cex,step);
  //               // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //             }
  //          }
  //         }
  //         else{
     
  //           res = check_prop_inv(pono_options, prop_filter_single, fts, s, cex,step);
  //           // res = check_prop(pono_options, prop_filter_single, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);


  //           if (res ==FALSE){
  //             s.reset();
  //             SmtSolver s = create_solver_for(pono_options.smt_solver_,
  //                                           pono_options.engine_,
  //                                           true,
  //                                           pono_options.ceg_prophecy_arrays_);
  //             FunctionalTransitionSystem fts(s);
  //             BTOR2Encoder btor_enc(pono_options.filename_, fts);
  //             PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);       
  //             if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //             {       
  //               PropertyInterface add_to_frame(filename_origin, fts);
  //               add_to_frame.AddAssumptionsToTS();
  //             }
  //             std::cout<<"The reduction property cannot be used"<<std::endl;
  //             Term prop_filter_single_re;
  //             cex.clear();
  //             prop_filter_single_re = prop_cex.cex_parse_to_pono_property(filter_re);
  //             std::cout <<"The new reduction property for the repeat filter is : "<< prop_filter_single_re->to_raw_string() << std::endl;
  //             if (((inductiveness = check_for_inductiveness(prop_filter_single_re, fts)) == false)){
  //               std::cout <<"We cannot get any reduction."<<std::endl;
  //               Term prop;
  //               std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //               res = check_prop_inv(pono_options, prop, fts, s, cex,step);
  //               // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //             }
  //             else{
  //               res = check_prop_inv(pono_options, prop_filter_single_re, fts, s, cex, step);
  //               // res = check_prop(pono_options, prop_filter_single_re, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);
  //               if(res ==FALSE){
  //                 s.reset();
  //                 SmtSolver s = create_solver_for(pono_options.smt_solver_,
  //                                               pono_options.engine_,
  //                                               true,
  //                                               pono_options.ceg_prophecy_arrays_);
  //                 FunctionalTransitionSystem fts(s);
  //                 BTOR2Encoder btor_enc(pono_options.filename_, fts);
  //                 PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);      
  //                 if ((pono_options.add_assuption_in_origin_ == true)&&(step>0))
  //                 {       
  //                   PropertyInterface add_to_frame(filename_origin, fts);
  //                   add_to_frame.AddAssumptionsToTS();
  //                 }
  //                 cex.clear(); 
  //                 std::cout <<"We cannot get any reduction."<<std::endl;
  //                 Term prop;
  //                 prop = prop_cex.cex_parse_to_pono_property();
  //                 std::cout << "The final property is:"<<prop->to_raw_string() << std::endl;
  //                 res = check_prop_inv(pono_options, prop, fts, s, cex,step);
  //                 // res = check_prop(pono_options, prop, fts, s, cex, pono_options.smt_solver_,pono_options.engine_,step);

  //               }
  //             }
  //           }
  //         }
  //       }  
  //     }
  //     }   
      
      res = get_prop_inv(pono_options, 
                  fts, 
                  step, 
                  s,
                  cex);
      // we assume that a prover never returns 'ERROR'
      assert(res != ERROR);
      // ofstream res_collect;
      std::string filename = "/data/zhiyuany/cosa2/result_2.txt";
      // print btor output
      if (res == FALSE) {
        cout << "sat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect<<"step: "<<  pono_options.step_ << "sat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<<"step: "<<  pono_options.step_ << "sat" <<endl;
        }
        assert(pono_options.witness_ || !cex.size());
        if (cex.size()) {
          print_witness_btor(btor_enc, cex, fts);
          if (!pono_options.vcd_name_.empty()) {
            VCDWitnessPrinter vcdprinter(fts, cex);
            vcdprinter.dump_trace_to_file(pono_options.vcd_name_);
          }
        }

      } else if (res == TRUE) {
        cout << "unsat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect<<"step: "<<  pono_options.step_ << "unsat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<<"step: "<<  pono_options.step_ << "unsat" <<endl;
        }
      } else {
        assert(res == pono::UNKNOWN);
        cout << "unknown" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;

    }

    
    }
    else{
    Term prop;
    if (pono_options.cex_reader_.empty()){
        const TermVec & propvec = btor_enc.propvec();
        unsigned int num_props = propvec.size();
        /// YZY: I am not sure whether we need to comment the following code

        if (pono_options.prop_idx_ >= num_props) {
          throw PonoException(
              "Property index " + to_string(pono_options.prop_idx_)
              + " is greater than the number of properties in file "
              + pono_options.filename_ + " (" + to_string(num_props) + ")");
        }
    
        prop = propvec[pono_options.prop_idx_];
    }
      if(!pono_options.property_file_.empty()) {
        PropertyInterface prop_if (pono_options.property_file_,fts);
        prop_if.AddAssumptionsToTS();
        prop = prop_if.AddAssertions(prop);
      }
      //////TODO: Add the transformation of the vcd at here!!!!//////////
      if(!pono_options.cex_reader_.empty()){
        PropertyInterfacecex prop_cex(pono_options.cex_reader_, std::string("RTL"), true, fts);
        FilterConcat filter;
        prop = prop_cex.cex_parse_to_pono_property(filter);
        std::cout << prop->to_raw_string() << std::endl;

          
      }

      vector<UnorderedTermMap> cex;
      // res = check_prop(pono_options, prop, fts, s, cex);
      // we assume that a prover never returns 'ERROR'
      assert(res != ERROR);
      
      std::string filename = "/data/zhiyuany/cosa2/result_2.txt";
      // print btor output
      if (res == FALSE) {
        cout << "sat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect<<"step: "<<  pono_options.step_ << "sat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<<"step: "<<  pono_options.step_ << "sat" <<endl;
        }
        assert(pono_options.witness_ || !cex.size());
        if (cex.size()) {
          print_witness_btor(btor_enc, cex, fts);
          if (!pono_options.vcd_name_.empty()) {
            VCDWitnessPrinter vcdprinter(fts, cex);
            vcdprinter.dump_trace_to_file(pono_options.vcd_name_);
          }
        }

      } else if (res == TRUE) {
        cout << "unsat" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
        if (FILE* file = fopen(filename.c_str(), "r")){        
          ofstream res_collect;
          res_collect.open(filename, ios::app);
          res_collect<<"step: "<<  pono_options.step_ << "unsat" <<endl;
        }
        else{
          ofstream res_collect(filename.c_str());
          res_collect<<"step: "<<  pono_options.step_ << "unsat" <<endl;
        }
      } else {
        assert(res == pono::UNKNOWN);
        cout << "unknown" << endl;
        cout << "b" << pono_options.prop_idx_ << endl;
      }
    }
    } 
    return res;
}
