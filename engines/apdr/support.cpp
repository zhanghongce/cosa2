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
 ** \brief Apdr class's support functions
 **
 ** 
 **/

#include "apdr.h"
#include "support.h"

#include "utils/logger.h"
#include "utils/container_shortcut.h"
#include "utils/multitimer.h"

namespace cosa {


// ---------------------------------------------------- //
//                                                      //
//       Basic Check Utilities                          //
//                                                      //
// ---------------------------------------------------- //

bool Apdr::is_valid(const smt::Term & e) {
  solver_->push();
  solver_->assert_formula(NOT(e));
  auto result = solver_->check_sat();
  solver_->pop();
  return (result.is_unsat());
}


bool Apdr::is_valid_imply(const smt::Term & pre, const smt::Term & post) {
  solver_->push();
  solver_->assert_formula(pre);
  solver_->assert_formula(NOT(post));
  auto result = solver_->check_sat();
  solver_->pop();
  return (result.is_unsat());
}


// this function is only used in recursive block
// in checking the same cycle solve
Model * Apdr::solve(const smt::Term & formula) {
#ifdef DEBUG
  assert(ts_.only_curr(formula)); // TO REMOVE when not DEBUG
#endif
  solver_->push();
  solver_->assert_formula(formula);
  auto result = solver_->check_sat();
  if (result.is_sat()) {
    varset_t varset;
    partial_model_getter.GetVarList(formula, varset, GlobalAPdrConfig.CACHE_PARTIAL_MODEL_CONDITION);
    cut_vars_cur(varset);
    Model * m = new_model(varset);
    solver_->pop();
    // must after pop
    CHECK_MODEL(solver_, formula, 1, m); // expect formula to be always 1 give the model

    return m;
  } // else
  solver_->pop();

  return NULL;
}

// ---------------------------------------------------- //
//                                                      //
//       frame handling                                 //
//                                                      //
// ---------------------------------------------------- //

smt::Term Apdr::frame_prop_btor(unsigned fidx) const {
  assert(fidx < frames.size());
  auto & lemmas = frames.at(fidx);
  if(lemmas.size() == 0)
    return TERM_TRUE;
  if(lemmas.size() == 1)
    return lemmas.at(0)->expr();
  smt::Term e = lemmas.at(0)->expr();
  for (auto lp_pos = lemmas.begin() + 1; lp_pos != lemmas.end() ; ++ lp_pos)
    e = AND(e, (*lp_pos)->expr() );
  return e;
} // frame_prop_btor



smt::Term Apdr::frame_prop_msat(unsigned fidx) const {
  assert(fidx < frames.size());
  auto & lemmas = frames.at(fidx);
  if(lemmas.size() == 0)
    return TERM_TRUE_msat;
  if(lemmas.size() == 1)
    return ( lemmas.at(0)->expr_msat() );
  smt::Term e = (lemmas.at(0)->expr_msat());
  for (auto lp_pos = lemmas.begin() + 1; lp_pos != lemmas.end() ; ++ lp_pos)
    e = AND_msat(e, ((*lp_pos)->expr_msat()) );
  return e;
}


bool Apdr::frame_implies(unsigned fidx, const smt::Term &prop) {
  // will not use 
  // return is_valid(IMPLY(frame_prop_btor(fidx), prop));
  assert(fidx < frames.size());
  const auto & lemmas = frames.at(fidx);
  solver_->push();
    for (const auto & lemma : lemmas)
      solver_->assert_formula(lemma->expr());
    solver_->assert_formula(NOT(prop));
  auto res = solver_->check_sat();
  solver_->pop();
  return res.is_unsat();
}

Model * Apdr::frame_not_implies_model(unsigned fidx, const smt::Term &prop) {
  assert(fidx < frames.size());
  const auto & lemmas = frames.at(fidx);
  solver_->push();
    for (const auto & lemma : lemmas)
      solver_->assert_formula(lemma->expr());
    solver_->assert_formula(NOT(prop));
  auto res = solver_->check_sat();
  if (res.is_sat()) {
    // get model
    Model * m = new_model();
    partial_model_getter.GetPartialModel(prop, m->cube, GlobalAPdrConfig.CACHE_PARTIAL_MODEL_CONDITION);
    solver_->pop();
    // must after pop
    CHECK_MODEL(solver_, prop, 0, m); // expect prop to be always 0 given the model
    return m;
  }
  solver_->pop();
  return NULL;
}


void Apdr::_add_lemma(Lemma * lemma, unsigned fidx) {
  if (fidx == frames.size())
    frames.push_back(frame_t());
  assert (fidx < frames.size());
  frames.at(fidx).push_back(lemma);
}

void Apdr::_add_pushed_lemma(Lemma * lemma, unsigned start, unsigned end) {
  Lemma * l_prev = lemma->copy(*this);
  l_prev->pushed = true;
  for (size_t fidx = start; fidx <= end; ++ fidx)
    _add_lemma(l_prev, fidx);
}


// ---------------------------------------------------- //
//                                                      //
//       Partial Model Related : Keep vars current      //
//                                                      //
// ---------------------------------------------------- //

void Apdr::cut_vars_cur(std::unordered_set<smt::Term> & v) {
  auto pos = v.begin();
  if (has_assumptions) {
    while(pos != v.end()) {
      // if has assumption
      // will not remove input var
      if (!ts_.is_curr_var(*pos) && 
          ts_.inputs().find(*pos) == ts_.inputs().end())
        pos = v.erase(pos);
      else
        ++pos;
    }
  } else { // if no assumption, will not keep input, erase everything but current var
    while(pos != v.end()) {
      if (!ts_.is_curr_var(*pos))
        pos = v.erase(pos);
      else
        ++pos;
    }
  } // else : no assumption

  if ( !keep_vars_.empty() || !remove_vars_.empty()){
    auto pos = v.begin();
    while(pos != v.end()) {
      if ( (!keep_vars_.empty() && !IN(*pos, keep_vars_)) ||
         (IN(*pos, remove_vars_)))
        pos = v.erase(pos);
      else
        ++pos;
    }
  }
} // cut_vars_cur

// ---------------------------------------------------- //
//                                                      //
//                   frames checks                      //
//                                                      //
// ---------------------------------------------------- //


smt::Term Apdr::get_inv() const {
  return frame_prop_btor(frames.size() - 1);
}


void Apdr::validate_inv() {
  dump_frames(std::cerr);
  smt::Term inv = get_inv();
  D(1, "INV: {}", inv->to_string());
  assert (is_safe_inductive_inv(inv));

  print_time_stat();
}

bool Apdr::is_last_two_frames_inductive() {
  auto fn = frames.size();
  if (fn > 1 && frame_implies(fn-1, frame_prop_btor(fn-2)))
      return true;
  return false;
}

// inv = get_inv()
bool Apdr::is_safe_inductive_inv(const smt::Term & inv) {
  assert (ts_.no_next(inv));
  auto inv_prime = ts_.next(inv);

  if(! is_valid_imply(ts_.init(), inv) ) {
    logger.log(0, "Failed: INIT => inv");
    return false;
  }
  if(! is_valid_imply(AND(inv, ts_.trans()), inv_prime) ) {
    logger.log(0, "Failed: inv /\\ T => inv'");
    return false;
  }
  if(! is_valid_imply(inv, property_.prop())) {
    logger.log(0, "Failed: inv => p");
    return false;
  }
  return true;
}

// Fi /\ T => F'i+1
void Apdr::sanity_check_imply() {
  if (frames.size() <= 1)
    return;
  // assert (frames.size() > 1);
  smt::Term T = ts_.trans();
  for (size_t fidx = 1; fidx < frames.size(); ++ fidx) {
    auto next_frame = ts_.next( frame_prop_btor(fidx) );
    assert ( is_valid_imply(AND(frame_prop_btor(fidx-1), T), next_frame)) ;
  }
}

// Fi => Fi+1
void Apdr::sanity_check_frame_monotone() {
  if (frames.size() <= 1)
    return;
  // assert (frames.size() > 1);
  for (size_t fidx = 1; fidx < frames.size(); ++ fidx) {
    assert ( frame_implies(fidx-1, frame_prop_btor(fidx)));
  }
}

void Apdr::sanity_check_last_frame_nopushed() {
  if (frames.size() <= 1)
    return;
  const auto & lastf = frames.back();
  for (Lemma * l : lastf) {
    if (l->pushed) {
      dump_frames(std::cout);
      D(0,"Last frame has pushed_lemma (why?) {} ", l->to_string());
    }
    assert (!l->pushed);
  }
}

smt::Result Apdr::sanity_check_property_at_length_k(const smt::Term & btor_p, unsigned k) {
  solver_->push();
  solver_->assert_formula(unroller_.at_time(ts_.init(), 0));
  for (unsigned i = 0; i<=k; ++i) {
    bool res = true;
    if (i > 0)
      solver_->assert_formula(unroller_.at_time(ts_.trans(), i - 1));

    {
      auto r = solver_->check_sat();
      if (!r.is_sat()) {
        logger.log(0, "Transition dead-end at bound: {}, constraint may be too tight.", i);
      }
    }
  } // unroll to frame i
  solver_->assert_formula(unroller_.at_time(btor_p, k));
  auto r = solver_->check_sat();
  solver_->pop();
  return r;
} // sanity_check_property_at_length_k

void Apdr::sanity_check_prop_fail(const std::vector<fcex_t> & path) {
  const auto & init_model = path.back();
  assert(init_model.fidx == 0);
  auto prev_res = sanity_check_property_at_length_k(init_model.cex->to_expr_btor(solver_), 0);
  assert (prev_res.is_sat());
  const fcex_t * pre_cex = & init_model;
  // fidx must be continues here

  for(int idx = path.size() -2 ;  idx > -1; --idx) {
    const auto & cex_info = path.at(idx);
    assert(cex_info.cex_origin == Lemma::LemmaOrigin::MUST_BLOCK);
    assert(cex_info.fidx == pre_cex->fidx+1);

    auto res = sanity_check_property_at_length_k(cex_info.cex->to_expr_btor(solver_), cex_info.fidx);
    
    if (!res.is_sat() && prev_res.is_sat() ) {
      solver_->assert_formula(pre_cex->cex->to_expr(solver_));
      solver_->assert_formula(ts_.trans());
      solver_->assert_formula(ts_.next(cex_info.cex->to_expr(solver_)));
      auto result = solver_->check_sat();
      solver_->pop();

      logger.log(0, "      [block-check] V{} /\\ T(V{}, V{}) /\\ V{} SAT?= {}", cex_info.fidx-1, cex_info.fidx-1, cex_info.fidx, cex_info.fidx, 
        result.is_sat() ? "True" : "False" );
    }
    prev_res = res;
    pre_cex = &cex_info;
  }
} // sanity_check_prop_fail


// ---------------------------------------------------- //
//                                                      //
//                    DUMPING                           //
//                                                      //
// ---------------------------------------------------- //


void Apdr::dump_frames(std::ostream & os) const {
  os << "---------- Frames DUMP ----------" << std::endl;
  for (size_t fidx = 0; fidx < frames.size() ; ++ fidx) {
    os << "Frame : " << fidx << std::endl;
    const auto & frame = frames.at(fidx);
    // dump lemmas
    for (size_t lidx = 0; lidx < frame.size() ; ++ lidx) {
      os << "  l" << lidx <<  " : " << frame.at(lidx)->dump_expr() << std::endl;
    }

    // dump cexs
    os << "  CEX blocked :" << std::endl;
    for (size_t lidx = 0; lidx < frame.size() ; ++ lidx) {
      os << "  c" << lidx <<  " : " << (frame.at(lidx)->dump_cex()) << std::endl;
    }
    
  } // for each frame
  os << "---------- END Frames DUMP ----------" << std::endl;
} // dump_frames


void Apdr::print_frame_stat(const std::string & extra_info) const {
  std::string output = "F[{}] ";
  if (frames.size() < 20) {
    for (auto && f : frames)
      output += std::to_string(f.size()) + ' ';
    output += extra_info;
    INFO(output, frames.size());
  } else {
    for(unsigned idx = 0; idx < 10; ++ idx)
      output += std::to_string(frames.at(idx).size()) + ' ';
    for(unsigned idx = frames.size()-10; idx < frames.size(); ++ idx)
      output += std::to_string(frames.at(idx).size()) + ' ';
    output += extra_info;
    INFO(output, frames.size());
  }
#ifdef DEBUG
  print_time_stat();
#endif
}

void Apdr::print_time_stat() const {
  std::vector<std::string> stat_to_show = {
    "Enum.Z3Query",
    "Enum.PredicateGen",
    "Enum.EnumPredConj",

    "APDR.interpolant",
    "APDR.SyGuS"
  };

  INFO("-----------Time Stat --------");
  for(const auto & s : stat_to_show) {
    if (GlobalTimer.EventExists(s)) {
      auto [tm,quant,speed] = GlobalTimer.GetTotal(s);
      INFO(s+"  {} / {}s = {}", quant,tm,speed);
    }
  }
}


} // namespace cosa

