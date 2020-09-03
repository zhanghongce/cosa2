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
#include "support.h"
#include "sort_convert_util.h"

#include "utils/logger.h"
#include "utils/exceptions.h"
#include "utils/term_analysis.h"

#include <fstream>
#include <sstream>


// #define DEBUG_DUMP_ENUM_STAT 1
#ifdef DEBUG_DUMP_ENUM_STAT
  #define DENUM(...) INFO(__VA_ARGS__)
#else
  #define DENUM(...) do{}while(0)
#endif

namespace cosa {

// extracting information from interpolant of certain round
void ApdrSygusHelper::SetItpForCurrentRound(const smt::Term & itp, unsigned fidx_prev) {
  itp_btor = itp; 
  fidx = fidx_prev;
  itp_vars.clear();

  if (itp_btor) {
    get_free_symbols(itp_btor, itp_vars); // TODO: CHANGE TO constants here
    max_const_width = get_constants_max_width(itp_btor);
  }
}

#define MAX(a,b) ((a)>(b) ? (a) : (b))
uint64_t ApdrSygusHelper::get_constants_max_width(const smt::Term & term)
{
  smt::TermVec to_visit({ term });
  smt::UnorderedTermSet visited;

  uint64_t max_width = 0;

  smt::Term t;
  while (to_visit.size()) {
    t = to_visit.back();
    to_visit.pop_back();

    if (visited.find(t) == visited.end()) {
      visited.insert(t);
      // add children to queue
      for (auto tt : t) {
        to_visit.push_back(tt);
      }

      if (t->is_value()) {
        auto sort_kind = t->get_sort()->get_sort_kind() ;
        if ( sort_kind == smt::SortKind::BOOL)
          max_width = MAX(max_width, 1);
        else if (sort_kind == smt::SortKind::BV)
          max_width = MAX(max_width, t->get_sort()->get_width());
      }
    }
  } // while
  return max_width;
} // get_constants_max_width

#undef MAX


void Apdr::reset_sygus_syntax() {
  sygus_query_gen_.reset(
    new sygus::SyGusQueryGen(
      op_extract_->GetSyntaxConstruct(),
      sygus_tf_buf_, sygus_symbol_names_, {}));
}


void Apdr::propose_new_lemma_to_block(fcex_t * pre, fcex_t * post) {
  // TODO: here

  // if failed

  { // interpolant
    Model * model_to_block = post->cex;
    auto fidx = post->fidx;
    smt::Term prop_msat = NOT_msat(model_to_block->to_expr_msat(itp_solver_, to_itp_solver_));

    auto prevF_msat = frame_prop_msat(fidx-1);
    if (GlobalAPdrConfig.RM_CEX_IN_PREV)
      prevF_msat = AND_msat(prevF_msat, prop_msat);

  std::cerr << "about to use itp;"  << std::endl;// for debug purpose
 
    smt::Term itp_msat = get_interpolant(prevF_msat, prop_msat);
    smt::Term itp_btor = nullptr;
  
  dump_frames(std::cout);
  assert(false); // for debug purpose

    if(itp_msat) {
      itp_btor = to_btor_.transfer_term(itp_msat, false);
      Lemma * itp = new_lemma(itp_btor, itp_msat, post->cex, post->cex_origin);
      frames.at(fidx).push_back(itp);
      return;
    }
  } // interpolant

  { // not Post state
    auto prop_btor = NOT(post->cex->to_expr_btor(solver_));
    auto prop_msat = NOT_msat(post->cex->to_expr_msat(itp_solver_, to_itp_solver_));

    Lemma * itp = new_lemma(prop_btor, prop_msat, post->cex, post->cex_origin);
    frames.at(post->fidx).push_back(itp);
    return;
  }
} // propose_new_lemma_to_block

// extract_model_t
// set 


// lemma_btor and lemma_msat, return may_block model and init
std::pair<Model *, bool> Apdr::gen_lemma(
    unsigned fidx,
    //const smt::Term & Fprev_msat, 
    const smt::Term & Fprev_btor, 
    //const smt::Term & prop_msat,
    const smt::Term & prop_btor,
    Model * cex,
    smt::TermVec & lemmas_msat /*OUT*/,
    smt::TermVec & lemmas_btor /*OUT*/ ) {

  // call gen_sygus
  sygus_info_helper_.SetItpForCurrentRound(NULL, fidx);
  auto ret = do_sygus(Fprev_btor, cex , sygus_info_helper_, lemmas_btor);
  for (const auto & t : lemmas_btor) {
    D(2, "         [lemma-gen] get sygus {}.", t->to_string());
    lemmas_msat.push_back(bv_to_bool_msat(to_itp_solver_.transfer_term(t, false), itp_solver_));
  }
    
  // an alternative : if fail, do something here
  // do the amendment here and return no may-block

  return ret;

} // Apdr::gen_lemma


smt::Term Apdr::get_interpolant(
    const smt::Term & Fprev_msat, 
    const smt::Term & prop_msat) { // init and T are pre-computed

  smt::Term prop_msat_nxt = ts_msat_.next(prop_msat); 
  smt::Term A_msat = OR_msat( AND_msat(Fprev_msat, T_msat), init_msat_nxt  );
  smt::Term B_msat = NOT_msat( prop_msat_nxt );
  // if not using init:
  // A_msat = AND_msat(prevF_msat, T_msat);
  // B_msat = NOT_msat(prop_msat_nxt);
  // will use init anyway 
  smt::Term itp_msat;
  GlobalTimer.RegisterEventStart("APDR.interpolant",0);
  auto res = itp_solver_->get_interpolant(A_msat,B_msat,itp_msat);
  GlobalTimer.RegisterEventEnd("APDR.interpolant",1);
  assert( res.is_unsat() );

  if (itp_msat) { // should be okay to use curr
    itp_msat = ts_msat_.curr(bv_to_bool_msat(itp_msat, itp_solver_));
    D(2, "         [lemma-gen] get itp {}.", itp_msat->to_string());
  } else {
    D(1, "         [lemma-gen] interpolation failed.");
    D(1, "            [A_msat] : ", A_msat->to_string());
    D(1, "            [B_msat] : ", B_msat->to_string());
  }
  return itp_msat;
} // end of 

// may block model and fail at init
std::pair<Model *, bool> Apdr::do_sygus( 
    const smt::Term & prevF_btor,
    Model * cex,
    ApdrSygusHelper & sygus_info, /* use itp var size*/
    smt::TermVec & lemmas_btor /*OUT*/ 
    ) {
  

  assert (cex);

  unsat_enum::Enumerator sygus_enumerator(
    to_next_func_,
    extract_model_func_,
    btor(),
    ts_.trans(), ts_.init(),
    prevF_btor /*prevF*/, 
    cex /*cexs \*/,
    sygus_term_manager_   
  );
  sygus_failed_at_init = false;
  extract_model_output_ = NULL;
  // this function will change sygus_failed_at_init and extract_model_output_
  // by the lambda function extract_model_func_
  sygus_enumerator.GetNCandidates(lemmas_btor, GlobalAPdrConfig.UNSAT_CORE_MULTI);
  assert(lemmas_btor.empty() == (extract_model_output_ != NULL));
  if(extract_model_output_)
    assert(!extract_model_output_->cube.empty());
  return std::make_pair(extract_model_output_, sygus_failed_at_init);
} // do_sygus


} // namespace cosa

