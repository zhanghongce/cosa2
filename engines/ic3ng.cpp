/*********************                                                  */
/*! \file ic3ng.cpp
** \verbatim
** Top contributors (to current version):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2019 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Bit-level IC3 implementation that splits bitvector variables
**        into the individual bits for bit-level cubes/clauses
**        However, the transition system itself still uses bitvectors
**/

#include "utils/logger.h"
#include "engines/ic3ng.h"
#include "engines/ic3ng-support/debug.h"
#include "utils/container_shortcut.h"
#include "utils/sygus_ic3formula_helper.h"

#include "smt-switch/printing_solver.h"

namespace pono
{
    
IC3ng::IC3ng(const Property & p, const TransitionSystem & ts,
            const smt::SmtSolver & s,
            PonoOptions opt) :
  Prover(p, ts, s, opt)
#ifdef DEBUG_IC3
  // , debug_fout("debug.smt2")
#endif
  // partial_model_getter(s)
  // bitwuzla can accept non-literal to reduce anyway
  {     
    initialize();
  }

IC3ng::~IC3ng() { }

void IC3ng::check_ts() {
  // check if there are arrays or uninterpreted sorts and fail if so
  if (!ts_.is_functional())
    throw PonoException(
      "IC3ng only supports functional transition systems.");
    // check if there are arrays or uninterpreted sorts and fail if so
  for (const auto & vec : { ts_.statevars(), ts_.inputvars() }) {
    for (const auto & st : vec) {
      smt::SortKind sk = st->get_sort()->get_sort_kind();
      if (sk == smt::ARRAY) {
        throw PonoException("IC3ng does not support arrays yet");
      } else if (sk == smt::UNINTERPRETED) {
        throw PonoException(
            "IC3ng does not support uninterpreted sorts yet.");
      }
    }
  }
  // requires all input variables become state variables
  if (!ts_.inputvars().empty()) {
    throw PonoException("IC3ng requries promoting input variables to state variables.");
  }
  // maybe you don't need to use ts.constraints. Because they are already conjuncted to init
  // and trans
  if (!can_sat(ts_.init())) {
    throw PonoException("constraint is too tight that conflicts with init.");
  }
  if (!can_sat(smart_and(smt::TermVec({ts_.init(), ts_.trans()})))) {
    throw PonoException("constraint is too tight that conflicts with init and trans");
  }

}

void IC3ng::initialize() {
  if (initialized_) {
    return;
  }

  if(!options_.promote_inputvars_) {
    throw PonoException("IC3ng must be used together with --promote-inputvars");
  }

  // solver_ = smt::create_printing_solver(solver_, &debug_fout, smt::PrintingStyleEnum::DEFAULT_STYLE);

  boolsort_ = solver_->make_sort(smt::BOOL);
  solver_true_ = solver_->make_term(true);
  solver_false_ = solver_->make_term(false);

  bv1_sort_ = solver_->make_sort(smt::BV, 1);
  solver_1_1 = solver_->make_term(1, bv1_sort_);
  solver_0_1 = solver_->make_term(0, bv1_sort_);;


  Prover::initialize();
  check_ts();

  // 1. build related information
  // all input will be promoted to statevar anyway
  actual_statevars_ = ts_.statevars();
  const auto & all_state_vars = ts_.statevars();
  const auto & s_updates = ts_.state_updates();
  for (const auto & sv : all_state_vars) {
    if (!IN(sv, s_updates)) {
      no_next_vars_.insert(sv);
      no_next_vars_nxt_.insert(ts_.next(sv));
      actual_statevars_.erase(sv);
    }
    else
      nxt_state_updates_.emplace(ts_.next(sv), s_updates.at(sv));
  }

  has_assumptions = !ts_.constraints().empty();
  assert(!nxt_state_updates_.empty());

  for (const auto & c_initnext : ts_.constraints()) {
    // if (!c_initnext.second)
    //  continue; // should not matter
    assert(ts_.no_next(c_initnext.first));
    // if (no_next) {
    constraints_curr_var_.push_back(c_initnext.first);
    smt::get_free_symbolic_consts(constraints_curr_var_.back(), vars_in_constraints_);

    // translate input_var to next input_var
    // but the state var ...
    // we will get to next anyway
    constraints_curr_var_.push_back(
      next_trans_replace(ts_.next(c_initnext.first)));
    smt::get_free_symbolic_consts(constraints_curr_var_.back(), vars_in_constraints_);
    // } // else skip
  }
  all_constraints_ = has_assumptions ? smart_and(constraints_curr_var_) : solver_true_;
  bad_next_trans_subst_ = next_trans_replace(ts_.next(bad_)); // bad_ is only available after Prover's initialize()
  init_prime_ = ts_.next(ts_.init());

  // 2. set up the label system

  frames.clear();
  frame_labels_.clear();
  // first frame is always the initial states
  
  append_frame();
  add_lemma_to_frame(new_lemma(ts_.init(), NULL, LCexOrigin::FromInit()), 0);
  append_frame();
  add_lemma_to_frame(new_lemma(all_constraints_, NULL,  LCexOrigin::FromConstraint()), 1);
  add_lemma_to_frame(new_lemma(smart_not(bad_), NULL, LCexOrigin::FromProperty()), 1);

  // set semantics of TS labels
  assert(!init_label_);
  // frame 0 label is identical to init label
  init_label_ = frame_labels_[0];


  lowest_frame_touched_ = frames.size() - 1;

  // build the initial aiger
  build_initial_aiger();
}

void IC3ng::append_frame()
{
  assert(frame_labels_.size() == frames.size());

  frame_labels_.push_back(
      solver_->make_symbol("__frame_label_" + std::to_string(frames.size()),
                           solver_->make_sort(smt::BOOL)));
  frames.push_back({});
}

void IC3ng::add_lemma_to_frame(Lemma * lemma, unsigned fidx) {
  assert (fidx < frames.size());
  frames.at(fidx).push_back(lemma);

  solver_->assert_formula(
      solver_->make_term(smt::Implies, frame_labels_.at(fidx), lemma->expr()));

}

static bool set_intersect(const smt::UnorderedTermSet & a, const smt::UnorderedTermSet & b) {
  const auto & smaller = a.size() < b.size() ? a : b;
  const auto & other = a.size() < b.size() ? b : a;
  for (const auto & e : smaller)
    if (other.find(e) != other.end())
      return true;
  return false;
}


// F /\ T /\ not(p)
// F /\ T /\ cube    sat?   
ic3_rel_ind_check_result IC3ng::rel_ind_check( unsigned prevFidx, 
  const smt::Term & bad_next_trans_subst_,
  Model * cex_to_block,
  bool get_pre_state
  ) {
  
  auto bad_next_to_assert = cex_to_block ? 
    // NOTE: this is next state, you should not use NOT here
    next_trans_replace( ts_.next( cex_to_block->to_expr(solver_) ) ) :
    bad_next_trans_subst_   ; // p(T(s))

  solver_->push();
  assert_frame(prevFidx); // this will also enforce the constraints
  if (cex_to_block) // you need to use NOT here
    solver_->assert_formula( smart_not(cex_to_block->to_expr(solver_)) );
  solver_->assert_formula(bad_next_to_assert);
  auto result = solver_->check_sat();
  if (result.is_unsat()) {
    solver_->pop();
    return ic3_rel_ind_check_result(false, NULL);
  } // now is sat
  if (!get_pre_state) {
    solver_->pop();
    return ic3_rel_ind_check_result(true, NULL);
  } // now get the state


  //  c = a /\ b
  // predecessor generalization is implemented through partial model
  // not good enough
  smt::UnorderedTermSet sliced_varset;
  smt::UnorderedTermSet unsliced_varset;
  smt::TermVec eqs;
  // use unsatcore reduction

  // solver_->pop(); is called in `get_min_pred`
  get_min_pred(bad_next_to_assert, 
    prevFidx, sliced_varset, unsliced_varset, eqs);

#if 0
  std::unordered_map<smt::Term,std::vector<std::pair<int,int>>> input_asts_slices = {
    {bad_next_to_assert, { {0,0} }}
  };
  if (has_assumptions) {
    // get free vars of bad_next_to_assert
    // for each constraint, if there are intersection of vars
    //   add contraint to input_asts_slices
    smt::UnorderedTermSet var_set_;
    get_free_symbolic_consts(bad_next_to_assert, var_set_ );

    // Below is to collect constraints that have common variables with bad_next_to_assert
    bool changed;
    do {
      changed = false;
      for (size_t cidx = 0; cidx < constraints_curr_var_.size(); ++ cidx) {
        // if we already include this assumption, we can skip
        if (input_asts_slices.find(constraints_curr_var_.at(cidx)) != input_asts_slices.end())
          continue;

        const auto & cnstr_vars = vars_in_constraints_.at(cidx);
        // for each variable in var_set_, see if there are any common variables
        bool intersect = set_intersect(cnstr_vars, var_set_); 
        if (intersect) {
          input_asts_slices.emplace(constraints_curr_var_.at(cidx),  std::vector<std::pair<int,int>>({ {0,0} }));
          for (const auto & v : cnstr_vars) {
            auto res = var_set_.emplace(v);
            if (res.second) // if a new variable is added to the set
              changed = true;
          }
        }
      } // end of for each constraint
    } while(changed); // keep iterating until no new variable added
    // HZ: will not insert all constraints
    // input_asts_slices.emplace(all_constraints_, std::vector<std::pair<int,int>>({ {0,0} }));
    D(3,"[get_model] # constraint: {}, used:{}", constraints_curr_var_.size(), input_asts_slices.size() - 1);
  } // end of has assumption

  partial_model_getter.GetVarListForAsts_in_bitlevel(input_asts_slices, varlist_slice);
#endif
  // after this step varlist_slice may contain 
  // 1. current state var , 2. current input var
  // 3. next input var (it should not contain next state var)
  // if there is no assumption, we can remove 2&3
  // if there is assumption, we can only remove 3
  
  Model * prev_ex = new_model(std::move(sliced_varset), std::move(unsliced_varset), std::move(eqs)); // just move to avoid copy

  // must after pop
  //if(has_assumptions)
  //  CHECK_MODEL(solver_, prop_no_nxt_btor, 0, prev_ex);

  return ic3_rel_ind_check_result(true, prev_ex); 
} // end of solveTrans




// if blocked return true
// else false

// < Model * cube, unsigned idx, LCexOrigin cex_origin >
// should have already been put into the queue
bool IC3ng::recursive_block_all_in_queue() {
  // queue not empty
  if(proof_goals.empty())
    return true;
  
  std::unordered_map<unsigned, unsigned> original_frame_sizes;

  unsigned prior_round_frame_no =  proof_goals.top()->fidx;

  while(!proof_goals.empty()) {
    fcex_t * fcex = proof_goals.top();

    D(2, "[recursive_block] Try to block {} @ F{}", (long long)(fcex->cex), fcex->fidx);
    D(3, "[recursive_block] Try to block {} @ F{}", fcex->cex->to_string(), fcex->fidx);
    // if we arrive at a new frame, eager push from prior frame
    if (fcex->fidx > prior_round_frame_no) {
      assert(fcex->fidx == prior_round_frame_no + 1);
      eager_push_lemmas(prior_round_frame_no, original_frame_sizes.at(prior_round_frame_no));
      // pop the stack
      D(2,"Eager push from {} --> {}", prior_round_frame_no, fcex->fidx);
    }
    prior_round_frame_no = fcex->fidx;
    // HZ: TODO: add a syntactic check here!
    bool trivial_block = false;
    for (Lemma * l : frames.at(fcex->fidx)) {
      if (l->cex() == fcex->cex) {
        trivial_block = true;
        break;
      }
    }

    if (trivial_block || frame_implies(fcex->fidx, smart_not(fcex->cex->to_expr(solver_)))) {
      proof_goals.pop();
      D(2, "[recursive_block] F{} -> not(cex)", fcex->fidx);
      continue;
    }
    if (fcex->fidx == 0) {
      // generally should fail
      // check that it has intersection with init
      // and the chain is actually all reachable (by creating an unroller)
      
      D(2, "[recursive_block] Cannot block @0");
      sanity_check_cex_is_correct(fcex);
      return false;
    } // else check if reachable from prior frame
    auto reachable_from_prior_frame =  rel_ind_check(fcex->fidx-1, nullptr, fcex->cex, true);
    if(!reachable_from_prior_frame.not_hold) {
      // unsat/unreachable
      // TODO make a lemma, to explain why F(i) /\ T => not MODEL
      
      D(2, "[recursive_block] Not reachable on F{}", fcex->fidx);
      inductive_generalization_mic(fcex->fidx-1, fcex->cex, fcex->cex_origin);
      proof_goals.pop();

      if (lowest_frame_touched_ > fcex->fidx)
        lowest_frame_touched_ = fcex->fidx;

      continue;
    } // else push queue
    Model * pre_model = reachable_from_prior_frame.prev_ex;
    proof_goals.new_proof_goal(fcex->fidx-1, pre_model, fcex->cex_origin.to_prior_frame(), fcex);
    
    // push the stack
    original_frame_sizes[fcex->fidx-1] = frames.at(fcex->fidx-1).size();
    // record_frame_size(fcex->fidx-1);

    D(2, "[recursive_block] reachable, traceback to F{}", fcex->fidx-1);
  } // end of while proof_goal is not empty
  proof_goals.clear(); // clear the model buffer, required by proof_goals class
  return true;
} // recursive_block_all_in_queue


void IC3ng::dump_invariants(std::ostream & os) const {
  if (frames.empty()) {
      os << "No frames available.\n";
      return;
  }

  D(1, "Starting to dump invariants from the last frame");
  
  const auto & last_frame = frames.back();
  os << "Dumping invariants from the last frame:\n";
  for (const Lemma * lemma : last_frame) {
    // os << "Clause: " << lemma->to_string() << "\n";
    // if (lemma->cex()) {
    //     os << "Model: " << lemma->cex()->to_string() << "\n";
    // }
    D(2, "Clause: {}", lemma->to_string());
  }
  
  D(1, "Finished dumping {} lemmas", last_frame.size());
}


ProverResult IC3ng::step(int i)
{
  if (i <= reached_k_) {
    return ProverResult::UNKNOWN;
  }

  if (reached_k_ < 1) {
    if(check_init_failed())
      return ProverResult::FALSE;
    D(1, "[Checking property] init passed");
    
    reached_k_ = 1;
    return ProverResult::UNKNOWN;
  }

  if (options_.ic3ng_update_inn) {
    // try to dump aiger here
    if (frames.back().size() > 50 || frames.size() > 5 ) {
      auto fname_in = "frame_" + std::to_string(frames.size()) + ".aig";
      auto fname_out = "frame_" + std::to_string(frames.size()) + ".opt.aig";
      dump_clause_to_aiger( fname_in );
      aiger_simplify(fname_in, fname_out);
      load_aiger_internal_nodes (fname_out); // loaded in internal_nodes_to_aiglit_map
      std::cout << "loaded " << loaded_preds_from_aiger_.size() << " preds." << std::endl;
      // clear this so, it will rebuild the predicates for counterexamples
      clear_cex_info();
    }
  }

  
  // `last_frame_reaches_bad` will add to proof obligation
  while (last_frame_reaches_bad()) {
    size_t nCube = proof_goals.size();
    if(! recursive_block_all_in_queue() )
      return ProverResult::FALSE;
    D(1, "[step] Blocked {} CTI on F{}", nCube, frames.size()-1);
  }
  logger.log(1,"[step] {}", print_frame_stat());
  
  append_frame();
  D(1, "[step] Extend to F{}", frames.size()-1);
  // TODO: print cubes?  

  // recursive block should have already pushed everything pushable to the last frame
  // so, we can simply push from the previous last frame
  //  should return true if all pushed
  //  should push necessary cex to the queue
  auto old_fsize = (++frames.rbegin())->size();
  if ( push_lemma_to_new_frame() ) {
    validate_inv();
    return ProverResult::TRUE;
  }
  
  lowest_frame_touched_ = frames.size() - 1 ;
  auto new_fsize = (frames.rbegin())->size();
  D(1, "[step] Pushed {}/{} Lemmas to F{}", new_fsize, old_fsize, frames.size()-1 );
  D(1, "[step] Added {} CTI on F{} ", proof_goals.size(), frames.size()-1 );

  // new proof obligations may be added
  size_t nCube = proof_goals.size();
  if (!recursive_block_all_in_queue()) {
    return ProverResult::FALSE;
  }

  D(1, "[step] Blocked {} CTI resulted from pushing on F{}", nCube, frames.size()-1);

  ++reached_k_;
  
  return ProverResult::UNKNOWN;
} // end of step


ProverResult IC3ng::check_until(int k) {
  initialize();
  assert(initialized_);

  ProverResult res;
  int i = reached_k_ + 1;
  assert(reached_k_ + 1 >= 0);
  while (i <= k) {
    res = step(i);
    if (res == ProverResult::FALSE) {
      // currently no abstraction
      return res;
    } else {
      ++i;
    }

    if (res != ProverResult::UNKNOWN) {
      return res;
    }
  }

  return ProverResult::UNKNOWN;
}


/**
 * This function should check F[-1] /\ T/\ P'
 * Need to consider assumptions!
 * Need to insert the model into proof_goals
*/
bool IC3ng::last_frame_reaches_bad() {
  // use relative inductive check?
  auto result = rel_ind_check(frames.size()-1, bad_next_trans_subst_, NULL, true);
  if (!result.not_hold) 
    return false;
  proof_goals.new_proof_goal(frames.size()-1, result.prev_ex, LCexOrigin::MustBlock(1), NULL);
  // else
  return true;
}


} // namespace pono
