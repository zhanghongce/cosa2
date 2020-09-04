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
 ** \brief Apdr core agorithm
 **
 ** 
 **/


#include "apdr.h"
#include "sort_convert_util.h"

#include "utils/container_shortcut.h"
#include "utils/term_analysis.h"
#include "utils/logger.h"
#include "utils/multitimer.h"

#include <cassert>
#include <queue>

#include "support.h"

namespace cosa {

// ---------------------------------------------------------------------


// -----------------------------------------------------------------------
// HERE begins Apdr's function definitions

Apdr::Apdr(const Property & p, smt::SmtSolver & s, 
    smt::SmtSolver & itp_solver,
    const std::unordered_set<smt::Term> & keep_vars,
    const std::unordered_set<smt::Term> & remove_vars) :
  Prover(p,s), keep_vars_(keep_vars), remove_vars_(remove_vars),
  partial_model_getter(s), 
  itp_solver_(itp_solver),
  to_itp_solver_(itp_solver_),
  to_btor_(solver_),
  ts_msat_(ts_, itp_solver, to_itp_solver_),
  property_msat_(bv_to_bool_msat(to_itp_solver_.transfer_term(p.prop(),false), itp_solver_)),
  sygus_symbol_(ts_msat_.states()),
  sygus_tf_buf_(ts_msat_, ts_),
  sygus_info_helper_()
  // cache the transition and init condition formula -- trans/init
  // no need actually.
  // - itp_solver_trans_term_(to_itp_solver_.transfer_term(ts_.trans())),
  // - itp_solver_init_term_(to_itp_solver_.transfer_term(ts_.init()))
  {     
    initialize();
  }

void Apdr::initialize() {

  Prover::initialize();

  // reverse populate msat_to_btor's cache
  ts_msat_.setup_reverse_translator(to_btor_);

  has_assumptions = !is_valid(ts_.constraint());

  // vars initialization
  for (auto && v : keep_vars_) {
    // assert it is state-var
    assert(ts_.is_curr_var(v));
    keep_vars_nxt_.insert(ts_.next(v));
  }
  for (auto && v : remove_vars_) {
    assert(ts_.is_curr_var(v));
    remove_vars_nxt_.insert(ts_.next(v));
  }

  if (GlobalAPdrConfig.CACHE_PARTIAL_MODEL_CONDITION) {
    // cache partial model getter
    partial_model_getter.CacheNode(ts_.init());
    // create the cache of next vars in 
    for (const auto & nxt : ts_.state_updates()) {
      partial_model_getter.CacheNode(nxt.second);
    }
  }

  // cache msat expression
  init_msat_nxt = bv_to_bool_msat(ts_msat_.next(ts_msat_.init()), itp_solver_);
    // to_itp_solver_.transfer_term(ts_.next(ts_.init())), itp_solver_);
  T_msat = bv_to_bool_msat(ts_msat_.trans(), itp_solver_);
    // bv_to_bool_msat(to_itp_solver_.transfer_term(ts_.trans()), itp_solver_);

  // build frames
  frames.push_back(frame_t()); // F0 = [init]
  frames.back().push_back(
    new_lemma(
      ts_.init(), bv_to_bool_msat( ts_msat_.init() , itp_solver_),
      NULL, Lemma::LemmaOrigin::ORIGIN_FROM_INIT) );
  // frames.push_back(frame_t()); // F1 = []

  // sygus state name initialization
  for (auto && s : sygus_symbol_)
      sygus_symbol_names_.insert( sygus::name_sanitize( s->to_string()) );

  // extract the operators
  op_extract_ = std::make_unique<OpExtractor>();
  op_extract_->WalkBFS(ts_msat_.init());
  op_extract_->WalkBFS(ts_msat_.trans());
  op_extract_->GetSyntaxConstruct().RemoveConcat();
  op_extract_->GetSyntaxConstruct().RemoveExtract();
  //if (GlobalAPdrConfig.COMP_DEFAULT_OVERRIDE && GlobalAPdrConfig.COMP_DEFAULT_BVULTULE)
  //  op_extract_->GetSyntaxConstruct().AddBvultBvule();

  op_extract_->GetSyntaxConstruct().AndOrConvert();
  op_extract_->GetSyntaxConstruct().RemoveUnusedStructure();

  reset_sygus_syntax();

  // cache two lambda functions for sygus enum
  to_next_func_ = [&] (const smt::Term & v) -> smt::Term {
    return ts_.next(v);
  };
  // this is to get the pre model
  // varset is the set of cex (post)
  extract_model_func_ = [this] (const smt::UnorderedTermSet & varset, bool failed_at_init) -> void {
    this->sygus_failed_at_init = failed_at_init;
    if (!failed_at_init) {
      smt::UnorderedTermSet var_pre;
      smt::TermVec var_next;
      for (const auto & v:varset)
        var_next.push_back( this->ts_.next_to_expr( this->ts_.next(v) ) );
      this->partial_model_getter.GetVarListForAsts(var_next, var_pre,  GlobalAPdrConfig.CACHE_PARTIAL_MODEL_CONDITION);
      this->cut_vars_curr(var_pre, !(this->has_assumptions));
      // we will not try to cut inputs away
      this->extract_model_output_ = this->new_model(var_pre); // get the model on thies vars
    } else {
      // get the next vars and make them the current ones
      smt::UnorderedTermSet var_next;
      for (const auto & v:varset)
        var_next.insert(this->ts_.next(v));
      this->extract_model_output_ = this->new_model_replace_var( var_next, this->ts_.curr_map() );
    }
  };

  { // register terms to find exprs
    for (auto && v_nxtexpr_pair : ts_.state_updates())
      sygus_term_manager_.RegisterTermsToWalk(v_nxtexpr_pair.second);
    sygus_term_manager_.RegisterTermsToWalk(ts_.init());
    sygus_term_manager_.RegisterTermsToWalk(ts_.constraint());
    sygus_term_manager_.RegisterTermsToWalk(property_.prop());
  }
}

Apdr::~Apdr() {
  unsat_enum::Enumerator::ClearCache(); // finally: make sure terms are destructed first
}

// ----------- TRANS - related  -------------------
//  you may want to have the interpolant here
//  used in recursive_block  and  get_bad_state_from_property_invalid_after_trans
//  use frame_prop_list for prevF !!!
//  --------------------------------------------------------------
//  NOTE:
//        to be used as get_pre_post_state_from_property_invalid_after_trans:
//        init = None, findItp = False, get_post_state = True

// 1. T is by default the transition relation
// -- please note this could be different for btor/msat
// 2. Variables will be by default trans.variables (for btor)
// 3. init will be by default the init (will need to trans to msat)
// 

// init, init_msat_next, T_msat    are pre-computed any way


// solveTrans : T/F
// will only use btor
Apdr::solve_trans_result Apdr::solveTrans( unsigned prevFidx, 
  const smt::Term & prop_btor,
  bool remove_prop_in_prev_frame,
  bool use_init, bool get_pre_state
  ) {
  
  assert(prop_btor != NULL);

  PUSH_STACK(APdrConfig::Apdr_working_state_t::SOLVE_TRANS);

  if (use_init) {
    solver_->push();
    solver_->assert_formula(ts_.init());
    solver_->assert_formula(NOT(prop_btor));
    auto res = solver_->check_sat();
    if (res.is_sat()) {
      if (!get_pre_state) {
        solver_->pop();
        POP_STACK;
        return solve_trans_result(true, true, NULL); 
      } // get pre state

      std::unordered_set<smt::Term> varlist;
      partial_model_getter.GetVarList(prop_btor, varlist, GlobalAPdrConfig.CACHE_PARTIAL_MODEL_CONDITION);

      D(3, "Before var cut: {}", new_model(varlist)->to_string());
      cut_vars_curr(varlist , !has_assumptions); // if we don't have assumptions we can cut current input
      Model * prev_ex = new_model(varlist);
      solver_->pop();
      // must after pop
      if(has_assumptions) // when there are assumptions, we will not cut inputs, therefore it should be good
        CHECK_MODEL(solver_, prop_btor, 0, prev_ex);

      POP_STACK;
      return solve_trans_result(true, true, prev_ex);       
    } // end is_sat
    solver_->pop();
  } // use_init

  auto prevF_btor = frame_prop_btor(prevFidx);
  auto prop_no_nxt_btor = ts_.next_to_expr( ts_.next( prop_btor ) ); // p(T(s))
  // constraints
  auto constraints_btor = ts_.next_to_expr( ts_.constraint() ); // c(s,T(s))

  solver_->push();
  solver_->assert_formula(prevF_btor);
  if (remove_prop_in_prev_frame)
    solver_->assert_formula(prop_btor);
  solver_->assert_formula(constraints_btor);
  solver_->assert_formula(NOT(prop_no_nxt_btor));
  auto result = solver_->check_sat();
  if (result.is_unsat()) {
    solver_->pop();
    POP_STACK;
    return solve_trans_result(false, false, NULL);
  } // now is sat
  if (!get_pre_state) {
    solver_->pop();
    POP_STACK;
    return solve_trans_result(true, false, NULL);
  } // now get the state
  std::unordered_set<smt::Term> varlist;
  partial_model_getter.GetVarList(prop_no_nxt_btor, varlist, GlobalAPdrConfig.CACHE_PARTIAL_MODEL_CONDITION);

  D(3, "Before var cut: {}", new_model(varlist)->to_string());
  cut_vars_curr(varlist, !has_assumptions); // // if we don't have assumptions we can cut current input
  Model * prev_ex = new_model(varlist);
  solver_->pop();

  // must after pop
  if(has_assumptions)
    CHECK_MODEL(solver_, prop_no_nxt_btor, 0, prev_ex);

  POP_STACK;
  return solve_trans_result(true, false, prev_ex); 
} // end of solveTrans


// solveTransLemma Unblockable, No_pred, Lemmas (vector)
// result: Prev_No_Pred
Apdr::solve_trans_lemma_result Apdr::solveTransLemma(
  unsigned prevFidx, 
  Model * model_to_block,
  bool remove_prop_in_prev_frame,
  // bool use_init = true, bool findItp = true,
  bool get_pre_state) {
  
  assert ( model_to_block );

  // construct ...
  smt::Term prop_btor = NOT(model_to_block->to_expr_btor(solver_));

  auto res = solveTrans(prevFidx, prop_btor, remove_prop_in_prev_frame, true /*use init*/, get_pre_state);
  if (res.not_hold)
    return solve_trans_lemma_result(res); // this is before push
  
  PUSH_STACK(APdrConfig::Apdr_working_state_t::SOLVE_TRANS_LEMMA);
  
  //D(3,"      [solveTrans] Property: {} , v=>v', useinit: {}", prop_btor->to_string(), use_init  );
  //D(4,"      [solveTrans] formula : {}", F_to_check->to_string());

  auto prevF_btor = frame_prop_btor(prevFidx);
  // the init' thing is in gen_lemma
  
  solve_trans_lemma_result ret_lemmas(false, false, NULL, NULL, false);
  std::tie(ret_lemmas.may_block,ret_lemmas.may_block_at_init)
    = gen_lemma( prevFidx,  prevF_btor,
        prop_btor, model_to_block,  /*OUT*/ ret_lemmas.itp_msat, /*OUT*/ ret_lemmas.itp );

  #ifdef DEBUG
    assert (!ret_lemmas.unblockable());
    if (ret_lemmas.no_good_syntax()) {
      assert(ret_lemmas.itp.empty() && ret_lemmas.itp_msat.empty());
      assert (!ret_lemmas.has_lemma());
    } else {
      assert (ret_lemmas.has_lemma());
      assert (!ret_lemmas.unblockable());
      assert (!ret_lemmas.no_good_syntax());
    }
  #endif

  POP_STACK;
  return ret_lemmas;
} // solveTrans


// if blocked return true
// else false
bool Apdr::recursive_block(Model * cube, unsigned idx, Lemma::LemmaOrigin cex_origin) {
  assert (cex_origin == Lemma::LemmaOrigin::MUST_BLOCK);

  PUSH_STACK(APdrConfig::Apdr_working_state_t::RECURSIVE_BLOCK);
  D(2, "      [block F{}] Try @F{} id {} : {}", idx, idx, reinterpret_cast<long>(cube), cube->to_string());

  smt::Term prop_btor = NOT(cube->to_expr_btor(solver_));
  if (frame_implies(idx, prop_btor)) {
    D(3, "      [block F{}] already blocked by F{}", idx, idx);
    POP_STACK;
    return true; // already blocked
  }

  enum prev_action_t {NONE, PREV_PUSH, PREV_POP} prev_action = prev_action_t::NONE;

  std::vector<fcex_t> cexs_to_block;
  cexs_to_block.push_back(fcex_t(idx,cube, true, cex_origin));
  while(!cexs_to_block.empty()) {
    const auto & head = cexs_to_block.back(); // the last one is the smallest
    unsigned fidx = head.fidx;
    Model * cex = head.cex;
    Lemma::LemmaOrigin cex_type = head.cex_origin;
    if (fidx == 0) {
      // may or may not matter, because it could be just a may block
      // TODO: find the lowest !can_transit_to_next's next
      // there propose new terms and must get lemma to block it
      // and then pop it, and see

      // revsersely traverse
      fcex_t * pre = NULL, * post = NULL;
      unsigned idx;
      for (idx = cexs_to_block.size()-1; idx > 0; --idx) {
        if (!(cexs_to_block.at(idx).can_transit_to_next) ){
          pre = & (cexs_to_block.at(idx));
          post = & (cexs_to_block.at(idx-1));
          break;          
        }
      } // reverse find
      if (idx == 0) { // always able to transit_to_next 
        CHECK_PROP_FAIL(cexs_to_block);
        D(3, "      [block-try] CEX found!"); // because we always start from MUST block
        // cex found
        POP_STACK;
        return false;
      } // else
      assert (pre && post);
      propose_new_lemma_to_block(pre, post); // must succeed, worse case itp/not post
      // pop till idx-1 (idx-1 will also be removed)
      unsigned post_fidx = post->fidx;
      cexs_to_block.erase(cexs_to_block.begin() + idx - 1 , cexs_to_block.end());
      prev_action = prev_action_t::PREV_POP;
      // cexs_to_block.resize(idx-1); //
      // p
      if (!cexs_to_block.empty()) 
        push_lemma_from_frame(post_fidx, false); // because next we will be on post + 1 frame
    }

    D(3, "      [block] check at F{} -> @F{} {} : {}", fidx-1, fidx, Lemma::origin_to_string(cex_type), cex->to_string());

    // check already block ? especially if we are from a lower-end
    if (prev_action == prev_action_t::PREV_POP) {
      // check already block by current frame (newly pushed ones)

      smt::Term prop_btor = NOT(cex->to_expr_btor(solver_));
      if (frame_implies(fidx, prop_btor)){
        cexs_to_block.pop_back();
        prev_action = prev_action_t::PREV_POP;
        if (!cexs_to_block.empty()) 
          push_lemma_from_frame(fidx, false);
        continue;
      }
    } // if prev pop

    // check at F Fidx-1 -> F idx 
    auto trans_result = solveTransLemma(fidx-1,
      cex, GlobalAPdrConfig.RM_CEX_IN_PREV,
      true /*pre state*/ ); // with init already

    if (trans_result.unblockable()) {
      unsigned prev_fidx = trans_result.not_hold_at_init ? 0 : fidx-1;
      cexs_to_block.push_back(fcex_t(prev_fidx, trans_result.prev_ex, true, cex_type));
      D(3, "      [block] push to queue, @F{} --cT--> prime : {}", prev_fidx,  trans_result.prev_ex->to_string());
    } else {
      if (trans_result.has_lemma()) {
        unsigned n_lemma = trans_result.itp.size();           assert (n_lemma == trans_result.itp_msat.size());
        for(unsigned lidx = 0; lidx < n_lemma; ++ lidx)  {
          Lemma * lemma = new_lemma(trans_result.itp.at(lidx), trans_result.itp_msat.at(lidx),
            cex, cex_type); // Question cex origin?
          _add_lemma(lemma, fidx);
          _add_pushed_lemma(lemma, 1, fidx - 1);
        } // new lemmas added, and we can pop the queue
        cexs_to_block.pop_back();
        prev_action = prev_action_t::PREV_POP;
        if (!cexs_to_block.empty()) 
          push_lemma_from_frame(fidx, false);

      } else {
        assert(trans_result.no_good_syntax()); // we don't have good syntax to gen a lemma

        // we may want to tighten a bit the prev frame
        unsigned prev_fidx = trans_result.may_block_at_init ? 0 : fidx-1;
        cexs_to_block.push_back(fcex_t(prev_fidx, trans_result.may_block, false, Lemma::LemmaOrigin::MAY_BLOCK));
        prev_action = prev_action_t::PREV_PUSH;
        D(3, "      [block] push to queue, @F{} --aT--> prime : {}", prev_fidx,  trans_result.may_block->to_string());
      }
    } // --cT--/--> , may or may not have good lemmas
    

  } // end of while(has some to block)


  D(2, "      [block F{}] succeed in block goal: F{} id {} ", idx, idx,  reinterpret_cast<long>(cube));
  POP_STACK;
  return true;

} // recursive_block



// ---------------------------------------------------- //
//                                                      //
//       PROCEDURES                                     //
//                                                      //
// ---------------------------------------------------- //

bool Apdr::check_init_failed() { // will use the prop specified by property
  Model * failed_m = frame_not_implies_model(0, property_.prop());
  if (failed_m) {
    D(1, "Property failed at init.");
    return true; // failed
  }  
  return false;
}


ProverResult Apdr::check_until(int k) {
  assert (k>=0);
  
  PUSH_STACK(APdrConfig::Apdr_working_state_t::CHECK_UNTIL);

  D(1, "[Checking property] start");
  if (check_init_failed()) {
    POP_STACK;
    return ProverResult(FALSE);
  }

  D(1, "[Checking property] init passed");
  while (frames.size() < k) {
    // removable checks
    #ifdef DEBUG
      sanity_check_frame_monotone();
      sanity_check_imply();
      // sanity_check_last_frame_nopushed();
    #endif

    // initially F1 is [], will fail, then add 
    Model * cube = frame_not_implies_model(frames.size() -1, property_.prop());
    // recursive block cube 
    if (cube) {
      INFO("{} , blocking..." , print_frame_stat());
      if (!recursive_block(cube, frames.size() -1, Lemma::LemmaOrigin::MUST_BLOCK)) {
        D(1, "[Checking property] Bug found at step {}", frames.size()-1);
        
        {
          #ifdef DEBUG
            auto cube_bmc_reachable = sanity_check_property_at_length_k(NOT(property_.prop()), frames.size() -1);
            D(1, "[Checking property] BMC result sat: {} ", cube_bmc_reachable.is_sat() ? "True" : "False");
            sanity_check_frame_monotone();
            sanity_check_imply();
            assert ( cube_bmc_reachable.is_sat());
          #endif
        }

        POP_STACK;
        return ProverResult(FALSE);
      } else { // blocked
        D(1, "[Checking property] Cube block at F{}", frames.size()-1);
      }
      // will try to block a second cex in the next round
    } else {
      if (is_last_two_frames_inductive()) {
        D(1, "[Checking property] The system is safe, frame : {}", frames.size());
        validate_inv();
        POP_STACK;
        return ProverResult(TRUE);
      } else {
        INFO("{} , pushing..." , print_frame_stat());
        D(1, "[Checking property] Adding frame {} ...", frames.size());
        // TODO: check F[last] /\ T 
        if(!sanity_check_trans_not_deadended() ) {
          D(1, "[Checking property] Transition dead-ended @ {} (cannot extend to {}), constraints may be too tight", frames.size(), frames.size()+1);
          POP_STACK;
          return ProverResult(UNKNOWN);
        }
        //  can still be SAT (note T already include constraints)
        frames.push_back(frame_t());
        push_lemma_from_the_lowest_frame();
        if (is_last_two_frames_inductive()) { // if we are lucky to have pushed all
          // Fn -> Fn-1 -> P, so Fn -> P
          D(1, "[Checking property] The system is safe, frame : {}", frames.size());
          validate_inv();
          POP_STACK;
          return ProverResult(TRUE);
        }
      } // adding a frame
    } // ind or add new frame
  } // step k
  POP_STACK;
  D(1, "[Checking property] bound {} reached, result : unknown", k);
  return ProverResult(UNKNOWN);
} // check_until







} // namespace cosa
