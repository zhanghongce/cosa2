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
 ** \brief Pdr's sygus interface
 **
 ** 
 **/

#include "apdr.h"

#include "utils/exec.h"
#include "utils/logger.h"
#include "utils/exceptions.h"
#include "utils/multitimer.h"
#include "utils/term_analysis.h"
#include "frontends/smtlib2parser.h"

#include <fstream>
#include <sstream>

#define INFO(...) logger.log(1, __VA_ARGS__)

// #define DEBUG_DUMP_ENUM_STAT 1
#ifdef DEBUG_DUMP_ENUM_STAT
  #define ENUM_STAT_INFO(...) INFO(__VA_ARGS__)
#else
  #define ENUM_STAT_INFO(...) do{}while(0)
#endif

namespace cosa {

#define MAX(a,b) ((a)>(b) ? (a) : (b))
// extracting information from interpolant of certain round
void ApdrSygusHelper::SetItpForCurrentRound(const smt::Term & itp, unsigned fidx_prev) {
  itp_btor = itp; fidx = fidx_prev; max_var_width = 0;
  itp_vars.clear();
  conj_depth_threshold_for_internal_sygus = GlobalAPdrConfig.STARTING_CONJ_DEPTH;

  if (itp_btor) {
    get_free_symbols(itp_btor, itp_vars); // TODO: CHANGE TO constants here
    for (auto && p : itp_vars)
      max_var_width = MAX(max_var_width, p->get_sort()->get_width()); // std::max does not fit here
    conj_depth_threshold_for_internal_sygus = itp_vars.size();
  }
}
#undef MAX


void Apdr::reset_sygus_syntax() {
  sygus_query_gen_.reset(
    new sygus::SyGusQueryGen(
      op_extract_->GetSyntaxConstruct(),
      sygus_tf_buf_, sygus_symbol_names_, {}));
}

void Apdr::propose_new_lemma_to_block(fcex_t * pre, fcex_t * post) {
  // TODO: here
}

// extract_model_t
// set 

// lemma_btor and lemma_msat, return may_block
std::pair<smt::Term, smt::Term> Apdr::gen_lemma(
    unsigned fidx,
    const smt::Term & Fprev_msat, 
    const smt::Term & Fprev_btor, 
    const smt::Term & prop_msat,
    const smt::Term & prop_btor,
    const std::vector<Model *> & cexs ) {

  if (lemma_btor == nullptr || lemma_msat == nullptr ) {
    INFO("Failed to get ITP, use prop instead.");
    return solve_trans_result(false, NULL, NULL, prop_btor, prop_msat);
  }

  D(3,"      [solveTrans] get lemma : {}", lemma_btor->to_string());



    // this is the key point
  smt::Term itp_msat;
  smt::Term itp_btor;
  bool get_itp = false;

  if (GlobalAPdrConfig.LEMMA_GEN_MODE != APdrConfig::LEMMA_GEN_MODE_T::SYGUS_ONLY) {
    // will do itp anyway
    smt::Term prop_msat_nxt = ts_msat_.next(prop_msat); 
    smt::Term A_msat = OR_msat( AND_msat(prevF_msat, T_msat), init_msat_nxt  );
    smt::Term B_msat = NOT_msat( prop_msat_nxt );
    // if not using init:
    // A_msat = AND_msat(prevF_msat, T_msat);
    // B_msat = NOT_msat(prop_msat_nxt);
    // will use init anyway 
    GlobalTimer.RegisterEventStart("APDR.interpolant",0);
    auto res = itp_solver_->get_interpolant(A_msat,B_msat,itp_msat);
    GlobalTimer.RegisterEventEnd("APDR.interpolant",1);
    get_itp = res.is_unsat();

    if (get_itp) {
      itp_msat = ts_msat_.curr(bv_to_bool_msat(itp_msat, itp_solver_));
      itp_btor = to_btor_.transfer_term(itp_msat, false);
      D(2, "         [lemma-gen] get itp {}.", itp_msat->to_string());
    } else {
      D(1, "         [lemma-gen] interpolation failed.");
      D(1, "            [A_msat] : ", A_msat->to_string());
      D(1, "            [B_msat] : ", B_msat->to_string());
      itp_msat = itp_btor = nullptr;
    }
  } // end of interpolant computing

  if (GlobalAPdrConfig.LEMMA_GEN_MODE == APdrConfig::LEMMA_GEN_MODE_T::ITP_ONLY) {
    GlobalAPdrConfig.STAT_LEMMA_USE_ITP ++;
    return std::make_pair(itp_btor, itp_msat);
  }

  bool change_syntax = false;
  // now sygus feature
  if ( (GlobalAPdrConfig.LEMMA_GEN_MODE & APdrConfig::LEMMA_GEN_MODE_T::ITP_VAR_EXTRACT)
      && (itp_msat != nullptr)) {
    smt::UnorderedTermSet new_vars;
    get_free_symbols(itp_msat, new_vars);
    if (new_vars != sygus_symbol_) {
      sygus_symbol_ = new_vars;

      sygus_symbol_names_.clear();
      for (auto && s : sygus_symbol_)
          sygus_symbol_names_.insert( sygus::name_sanitize( s->to_string()) );
      
      change_syntax  = true;
    }
  }

  if ( (GlobalAPdrConfig.LEMMA_GEN_MODE & APdrConfig::LEMMA_GEN_MODE_T::ITP_SYNTAX_EXTRACT) 
       && (itp_msat != nullptr)  ) {
    op_extract_->GetSyntaxConstruct().new_constructs = false;
    op_extract_->WalkBFS(itp_msat);
    if (op_extract_->GetSyntaxConstruct().new_constructs)
      change_syntax = true;
  }

  if (change_syntax) {
    // we need to recompute the syntax
    D(2, "         [lemma-gen] sygus syntax updated");
    reset_sygus_syntax( /*will use new op_extract*/ ); // use var-set to recompute
  }

  sygus_info_helper_.SetItpForCurrentRound(itp_btor, fidx);

  if (sygus_info_helper_.itp_btor != NULL && sygus_info_helper_.max_var_width < GlobalAPdrConfig.NO_SYGUS_IF_ITP_VARWIDTH_LESS_THAN)
  { 
    return std::make_pair(itp_btor, itp_msat);
  }

  GlobalTimer.RegisterEventStart("APDR.SyGuS", 0);
  // gen exec and extract
  smt::Term lemma_btor = do_sygus(prevF_msat,  prevF_btor,
    prop_msat, prop_btor,
    // cexs.empty() ? prop_msat : nullptr, // depends on whether we use cexs or not
    cexs, facts, false /*assert inv in previous frame*/,
    sygus_info_helper_);
  GlobalTimer.RegisterEventEnd("APDR.SyGuS", 1);

  if (lemma_btor != nullptr) {
    D(2, "         [lemma-gen] sygus: {}", lemma_btor->to_string());
    smt::Term lemma_msat = bv_to_bool_msat(to_itp_solver_.transfer_term(lemma_btor, false), itp_solver_);
    GlobalAPdrConfig.STAT_LEMMA_USE_SYGUS ++;
    return std::make_pair(lemma_btor, lemma_msat);
  } else {
    dump_frames(std::cout);
    if(itp_btor)
      D(0, "Will use itp: {}", itp_btor->to_raw_string());
    assert(false);
  }

  // at this point, sygus lemma gen has failed
  if (GlobalAPdrConfig.LEMMA_GEN_MODE != APdrConfig::LEMMA_GEN_MODE_T::SYGUS_ONLY) {
    if (get_itp && itp_msat != nullptr && itp_btor != nullptr) {
      D(2, "         [lemma-gen] sygus failed, use itp instead.");
      D(2, "         [lemma-gen] itp: {}", itp_msat->to_string());
      GlobalAPdrConfig.STAT_LEMMA_USE_ITP ++;
      return std::make_pair(itp_btor, itp_msat);
    }
  }

  GlobalAPdrConfig.STAT_LEMMA_USE_NOT_CEX ++;
  return std::make_pair(nullptr, nullptr);
} // Apdr::gen_lemma

smt::Term Apdr::do_sygus(const smt::Term & prevF_msat, 
    const smt::Term & prevF_btor,
    const smt::Term & prop_msat,
    const smt::Term & prop_btor,
    const std::vector<Model *> & cexs, const std::vector<Model *> & facts,
    bool assert_inv_in_prevF,
    ApdrSygusHelper & sygus_info /* use itp var size*/) {
  
  if (sygus_info.itp_btor != NULL && sygus_info.max_var_width < GlobalAPdrConfig.NO_SYGUS_IF_ITP_VARWIDTH_LESS_THAN)
    return nullptr; // no need for sygus

  if (GlobalAPdrConfig.SYGUS_MODE & APdrConfig::SYGUS_MODE_T::INTERNAL) {
    // do it here
    ENUM_STAT_INFO(" -- Building term & pred ...");
    GlobalTimer.ClearEventFlag("Enum.PredicateGen");
    GlobalTimer.ClearEventFlag("Enum.EnumPredConj");


    assert (!cexs.empty());

    unsat_enum::Enumerator sygus_enumerator(
      to_next_func_,
      btor(),
      ts_.trans(), ts_.init(),
      prevF_btor /*prevF*/, 
      cexs /*cexs \*/,
      sygus_term_manager_   
    );
  auto ret = sygus_enumerator.GetCandidate();
  if (ret)
    return ret;
  ENUM_STAT_INFO(" --internal sygus fail");
  } // end of sygus mode : INTERNAL

  return nullptr;
} // do_sygus


} // namespace cosa

