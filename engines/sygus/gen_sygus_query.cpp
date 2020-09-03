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
 ** \brief SyGuS Query Generator
 **
 ** 
 **/

#include "utils/str_util.h"
#include "utils/container_shortcut.h"
#include "gen_sygus_query.h"
#include "utils/logger.h"

#define FMT_HEADER_ONLY

#include <fmt/format.h>
#include <fstream>
#include <queue>

namespace cosa {

namespace sygus {

static std::string body_paranthesis_auto(const std::string & in) {
  std::string body(in);
  StrTrim(body);
  if (! ( body.front() == '(' && body.back() == ')' ) )
    body = "(" + body + ")";
  return body;
}

SyGuSTransBuffer::SyGuSTransBuffer ( const TransitionSystem & ts_msat, const TransitionSystem & ts_btor):
ts_msat_(ts_msat), ts_btor_(ts_btor),
states_(ts_msat.states()), next_states_(ts_msat.next_states()), inputs_(ts_msat.inputs()) {
  std::vector<std::string> arg_lists_init_;
  std::vector<std::string> arg_lists_trans_;
  std::vector<std::string> arg_lists_call_init_;
  std::vector<std::string> arg_lists_call_trans_;
  // compute vars
  for (const auto &s : states_) {
    auto name = name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    primal_var_def_ += "(declare-var " + name + " " + sort + ")\n";
    arg_lists_init_.push_back("("+name + " " + sort+")");
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_init_.push_back(name);
    arg_lists_call_trans_.push_back(name);

    auto name_next = name_sanitize(ts_msat.next(s)->to_string());
    state_to_next_map_.emplace(name, name_next);
  }
  for (const auto &s : next_states_) {
    auto name = name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    prime_var_def_ += "(declare-var " + name + " " + sort + ")\n";
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_trans_.push_back(name);
  }
  for (const auto &s : inputs_) {
    auto name = name_sanitize(s->to_string());
    auto sort = s->get_sort()->to_string();
    input_var_def_ += "(declare-var " + name + " " + sort + ")\n";
    arg_lists_init_.push_back("("+name + " " + sort+")");
    arg_lists_trans_.push_back("("+name + " " + sort+")");
    arg_lists_call_init_.push_back(name);
    arg_lists_call_trans_.push_back(name);
  }

  trans_def_ = "(define-fun Trans \n    (" + Join(arg_lists_trans_, " ") +")\n    Bool\n     "
    + body_paranthesis_auto(ts_msat.trans()->to_string()) + ")";
  trans_use_ = "(Trans " + Join(arg_lists_call_trans_, " ") + ")";

  // (define-fun Fprev (state_arg_def_) Bool (...))
  // (Fprev )
  state_arg_def_ = Join(arg_lists_init_, " ");
  state_arg_use_ = Join(arg_lists_call_init_, " ");

  init_def_ = "(define-fun Init \n    (" + state_arg_def_ +")\n     Bool\n     "
    + body_paranthesis_auto(ts_msat.init()->to_string()) + ")";
  init_use_ = "(Init " + state_arg_use_ + ")";

}

std::string SyGuSTransBuffer::GetFprevDef(const smt::Term & Fprev) const {
  return ("(define-fun Fprev \n    (" +state_arg_def_+")\n     Bool\n     "
    + body_paranthesis_auto(Fprev->to_string()) + ")");
}
std::string SyGuSTransBuffer::GetFprevUse() const {
  return ("(Fprev " + state_arg_use_ + ")");
}


std::string SyGuSTransBuffer::StateToNext(const std::string & name) const {
  auto pos = state_to_next_map_.find(name);
  if ( pos!= state_to_next_map_.end() )
    return pos->second;
  pos = state_to_next_map_.find(name_sanitize(name));
  if ( pos!= state_to_next_map_.end() )
    return pos->second;
  pos = state_to_next_map_.find(name_desanitize(name));
  if ( pos!= state_to_next_map_.end() )
    return pos->second;
  assert(false);
  return "";
}

// ------------ END of buffer functions ------------ //

std::vector<std::string_view> operator_symbols = 
{
  "And",
  "Or",
  "Xor",
  "Not",
  "=>", // Implies
  "=", // Iff
  "----", // Ite
  "=", // Equal
  "=", // Distinct: Not equal should work
  "----", // Apply

  /* Arithmetic Theories */
  "----", // Plus,
  "----", // Minus,
  "----", // Negate,
  "----", // Mult,
  "----", // Div,
  "----", // Lt,
  "----", // Le,
  "----", // Gt,
  "----", // Ge,
  // Integers only
  "----", //Mod,
  "----", //Abs,
  "----", //Pow,
  "----", //IntDiv,
  // Int/Real Conversion and Queries
  "----", //To_Real,
  "----", //To_Int,
  "----", //Is_Int,
  /* Fixed Size BitVector Theory */
  "----", // Concat,
  "----", // Extract,
  "bvnot", // BVNot,
  "bvneg", // BVNeg,
  "bvand", // BVAnd,
  "bvor", // BVOr,
  "bvxor", // BVXor,
  "bvnand", // BVNand,
  "bvnor", // BVNor,
  "bvxnor", // BVXnor,
  "=", // BVComp,
  "bvadd", // BVAdd,
  "bvsub", // BVSub,
  "bvmul", // BVMul,
  "bvudiv", // BVUdiv,
  "bvsdiv", // BVSdiv,
  "bvurem", // BVUrem,
  "bvsrem", // BVSrem,
  "bvsmod", // BVSmod,
  "bvshl", // BVShl,
  "bvashr", // BVAshr,
  "bvlshr", // BVLshr,
  "bvult", // BVUlt,
  "bvule", // BVUle,
  "bvugt", // BVUgt,
  "bvuge", // BVUge,
  "bvslt", // BVSlt,
  "bvsle", // BVSle,
  "bvsgt", // BVSgt,
  "bvsge", // BVSge,
  "zero_extend", // Zero_Extend,
  "sign_extend", // Sign_Extend,
  "----", // Repeat,
  "rotate_left", // Rotate_Left,
  "rotate_right", // Rotate_Right,
  // BitVector Conversion
  "----", // BV_To_Nat,
  "----", // Int_To_BV,
  /* Array Theory */
  "----", // Select,
  "----", // Store,
  /**
     Serves as both the number of ops and a null element for builtin operators.
   */
  "----", // NUM_OPS_AND_NULL
};

static std::string width_to_type(uint64_t w) {
  if (w == 0)
    return "Bool";
  return "(_ BitVec " + std::to_string(w) +")";
}


// ------------ END of Constants------------ //

static std::string syntax_constraints_template = R"**(
(synth-fun INV 
   %args% Bool
( (Conj Bool) (Disj Bool) (Literal Bool) (Atom Bool)
  %nonterminals%
)
(
    (Conj Bool (Disj 
                (and Disj Conj)))
    (Disj Bool (Literal 
                (or Literal Disj)))
    (Literal Bool (Atom
                (not Atom)))
    (Atom Bool (
      %comps%
      ))
      %evcs%
   ))

)**";


static std::string syntax_no_constraints_template = R"**(
(synth-fun INV 
   %args% Bool)
)**";

SyGusQueryGen::SyGusQueryGen(
  const SyntaxStructure & syntax,
  const SyGuSTransBuffer & sygus_ts_buf,
  const std::unordered_set<std::string> & keep_vars_name,
  const std::unordered_set<std::string> & remove_vars_name) :
  syntax_(syntax), sygus_ts_buf_(sygus_ts_buf)
{ 
	// compute the all variable list
  // gen necessary strings
  std::vector<std::string> inv_def_vars;
  // std::vector<std::string> inv_use_vars;

  syntax_.CutVars(keep_vars_name, remove_vars_name);
  syntax_.RemoveUnusedStructure();

  for (auto && w_cnstr : syntax_.GetSyntaxConstruct()) {
    auto width = w_cnstr.first;
    const auto & cnstr = w_cnstr.second;
    for (const auto & name : cnstr.symbol_names) {
      new_variable_set_[width].insert(name);
      inv_def_vars.push_back("("+ name + " " + width_to_type(width) + ")" );
      ordered_vars.push_back(name);
      ordered_vars_next.push_back(sygus_ts_buf_.StateToNext(name));
      vars_kept.insert(name);
    }
  } // here we compute the vars to keep
  inv_def_var_list = Join(inv_def_vars, " ");
  inv_use_var_list = Join(ordered_vars, " ");
  inv_use = "(INV " + inv_use_var_list + ")";
  inv_use_next = "(INV " + Join(ordered_vars_next, " ") + ")";

  generate_syntax_cnstr_string();  // -> syntax_constraints

} // SyGusQueryGen::SyGusQueryGen

// _to_sygus_tree
void SyGusQueryGen::generate_syntax_cnstr_string() {
  typedef std::vector<std::string> stvec;
  // 1. refilter again the vars
  stvec comps_list;
  stvec nonterminal_list;
  std::string evcs;
  for (auto && width_syn_pair : syntax_.GetSyntaxConstruct()) {
    auto width = width_syn_pair.first;
    const auto & syn = width_syn_pair.second;
    std::unordered_set<std::string> empty_vars;
    const auto & var = IN(width, new_variable_set_) ? new_variable_set_.at(width) : empty_vars ;

    comps_list.push_back( fmt::format("(= E{0} E{0})", width) );
    for (auto primop : syn.op_comp ) {
      unsigned opnum = (unsigned)primop;
      assert(opnum < operator_symbols.size());
      std::string_view opstr = operator_symbols.at(opnum);
      assert(opstr != "----");
      if (opstr == "=")
        continue; // already has it
      if (primop != smt::BVComp && primop != smt::Equal )
        comps_list.push_back( fmt::format("({1} E{0} E{0})", width, opstr) );
    }

    auto tp = width_to_type(width);
    evcs += "(E"+std::to_string(width) + "  " + tp + " (";
    nonterminal_list.push_back("(E"+std::to_string(width) + "  " + tp + ")");

    if (!var.empty()) {
      evcs += "V"+std::to_string(width)+" ";
      nonterminal_list.push_back("(V"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.constants.empty()) {
      evcs += "C"+std::to_string(width)+" ";
      nonterminal_list.push_back("(C"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_binary.empty() || !syn.op_unary.empty()) {
      evcs += "Arithm"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Arithm"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_concat.empty()) {
      evcs += "Concat"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Concat"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_extract.empty()) {
      evcs += "Extract"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Extract"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_rotate.empty()) {
      evcs += "Rotate"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Rotate"+std::to_string(width) + "  " + tp + ")");
    }
    if (!syn.op_extend.empty()) {
      evcs += "Ext"+std::to_string(width)+" ";
      nonterminal_list.push_back("(Ext"+std::to_string(width) + "  " + tp + ")");
    }

    evcs += "))\n";

    if (!var.empty()) {
      evcs += "(V"+std::to_string(width)+" " + tp +" (";
      for (auto pos = var.begin() ; pos != var.end(); ++ pos) {
        if (pos == var.begin())
          evcs += *pos; // already sanitized
        else
          evcs += " "  +  *pos;
      }
      evcs += "))\n";
    }
    if (!syn.constants.empty()) {
      evcs += "(C"+std::to_string(width)+" " + tp +" (";
      for (auto pos = syn.constants.begin() ; pos != syn.constants.end(); ++ pos) {
        if (pos == syn.constants.begin())
          evcs += (*pos);
        else
          evcs += " "  + (*pos);
      }
      evcs += "))\n";
    }
    if (!syn.op_binary.empty() || !syn.op_unary.empty()) {
      evcs += "(Arithm"+std::to_string(width)+" " + tp + " (";
      stvec arithm;
      for (auto op : syn.op_unary) {
        unsigned opnum = (unsigned)op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        arithm.push_back(fmt::format("({1} E{0})", width, opstr));
      }
      for (auto op : syn.op_binary) {
        unsigned opnum = (unsigned)op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        arithm.push_back(fmt::format("({1} E{0} E{0})", width, opstr));
      }
      evcs += Join(arithm, " ");
      evcs += "))\n";
    }
    if (!syn.op_concat.empty()) {
      evcs += "(Concat"+std::to_string(width)+" " + tp + " (";
      stvec concats;
      for (auto && concat : syn.op_concat)
        concats.push_back( fmt::format("(concat E{0} E{1})", concat.width1, concat.width2 ) );
      evcs += Join(concats, " ");
      evcs += "))\n";
    }
    if (!syn.op_extract.empty()) {
      evcs += "(Extract"+std::to_string(width)+" " + tp + " (";
      stvec extracts;
      for (auto && extract : syn.op_extract)
       extracts.push_back( fmt::format("((_ extract {0} {1}) E{2})", extract.h, extract.l, extract.input_width) );
      evcs += Join(extracts, " ");
      evcs += "))\n";
    }
    if (!syn.op_rotate.empty()) {
      evcs += "(Rotate"+std::to_string(width)+" " + tp + " (";
      stvec rotates;
      for (auto && rotate : syn.op_rotate) {
        unsigned opnum = (unsigned)rotate.op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        rotates.push_back( fmt::format("((_ {} {}) E{})", opstr, rotate.param, width) );
      }
      evcs += Join(rotates, " ");
      evcs += "))\n";
    }
    if (!syn.op_extend.empty()) {
      evcs += "(Ext"+std::to_string(width)+" " + tp + " (";
      stvec exts;
      for (auto && ext : syn.op_extend) {
        unsigned opnum = (unsigned)ext.op;
        assert(opnum < operator_symbols.size());
        std::string_view opstr = operator_symbols.at(opnum);
        assert(opstr != "----");
        exts.push_back( fmt::format("((_ {} {}) E{})", opstr, ext.extw, ext.input_width) );
      }
      evcs += Join(exts, " ");
      evcs += "))\n";
    }
  } // for all reachable width

  syntax_constraints = 
    ReplaceAll( ReplaceAll( ReplaceAll( ReplaceAll(syntax_constraints_template,
      "%args%", "(" + inv_def_var_list + ")"),
      "%nonterminals%", Join(nonterminal_list, " ") ),
      "%comps%", Join(comps_list, " ")),
      "%evcs%", evcs);
      
  syntax_no_constraints = 
    ReplaceAll(syntax_no_constraints_template,
      "%args%", "(" + inv_def_var_list + ")");
} // SyGusQueryGen::generate_syntax_cnstr_string()



bool SyGusQueryGen::contains_extra_var(Model * m) const {
  for ( auto && v_val : m->cube ) {
    if (!IN(name_sanitize( v_val.first->to_string() ), vars_kept))
      return true;
  }
  return false;
} // SyGusQueryGen::contains_extra_var

// return true if there are cex left
unsigned SyGusQueryGen::dump_cex_block(
  const cexs_t  & cex_to_block, 
  const SyGuSTransBuffer & sygus_ts_buf,
  std::ostream & os) {

  unsigned n_cex = 0;
  // use_var_name to find the states and do an index into it
  const auto & symbols = sygus_ts_buf.ts_btor_.symbols(); // we expect models are from btor
  for (auto model_ptr : cex_to_block) {
    if (contains_extra_var(model_ptr))
      continue;
    os<<"(constraint (not (INV";
    for (auto && vname : ordered_vars) {
      auto desanitized_name = name_desanitize(vname);
      auto pos = symbols.find(desanitized_name);
      assert(pos != symbols.end());
      auto val_pos = model_ptr->cube.find(pos->second);
      if (val_pos == model_ptr->cube.end()) {
        // not found
        os << " " << vname; // keep the value symbolic
      } else { // gen the value string
        os << " " << val_pos->second->to_string();
      }
    } // for each v in INV
    os << ")))\n";
    n_cex ++;
  }
  return n_cex;
} // SyGusQueryGen::dump_cex_block

// return true if there are fact left
unsigned SyGusQueryGen::dump_fact_allow(
  const facts_t  & facts_all, 
  const SyGuSTransBuffer & sygus_ts_buf,
  std::ostream & os) {
  unsigned n_fact = 0;
  for (auto model_ptr : facts_all) {
    std::string constraint = "(constraint (INV";
    bool skip_this_fact = false;
    const auto & symbols = sygus_ts_buf.ts_btor_.symbols(); // we expect models are from btor
    for (auto && vname : ordered_vars) {
      auto desanitized_name = name_desanitize(vname);
      auto pos = symbols.find(desanitized_name);
      assert(pos != symbols.end());
      auto val_pos = model_ptr->cube.find(pos->second);
      if (val_pos == model_ptr->cube.end()) {
        // not found
        skip_this_fact = true;
        break;
      } else { // gen the value string
        os << " " << val_pos->second->to_string();
      }
    } // for each v in INV
    if (skip_this_fact)
      continue;
    constraint += "))\n";
    os << constraint;
    n_fact ++;
  } // for each fact
  return n_fact;
} // SyGusQueryGen::dump_fact_allow


// (constraint (=> (INV ...) ()))
void SyGusQueryGen::dump_inv_imply_prop(
  const smt::Term & prop, 
  const SyGuSTransBuffer & sygus_ts_buf,
  std::ostream & os) {
  if (prop == nullptr)
    return;
  os << "(constraint (=> " << inv_use << " "
     << body_paranthesis_auto(prop->to_string()) <<"))\n";
}


void SyGusQueryGen::GenToFile(
    const smt::Term & prevF,
    const facts_t & facts_all, // internal filters
    const cexs_t  & cex_to_block,
    const smt::Term & prop_to_imply,
    bool assert_in_prevF,
    bool use_syntax,
    std::ostream &fout,
    const std::string & additional_info) {
  
  fout << "; ----- INFO SUMMARY -----" << std::endl;
  fout << "; cex_to_block : " << cex_to_block.size() << std::endl;
  fout << "; facts_all : " << facts_all.size() << std::endl;
  fout << "; prop_to_imply : " << (prop_to_imply == nullptr ? "None" : "Y") << std::endl;
  fout << "; assert_in_prevF : " << (assert_in_prevF ? "Y" : "N") << std::endl;
  fout << "; use_syntax : " << (use_syntax ? "Y" : "N") << std::endl;
  fout << "; additional_info : " << additional_info << std::endl;
  fout << "; ----- END of INFO SUMMARY -----\n" << std::endl;
  fout << "(set-logic BV)\n";
  
  if (use_syntax)
    fout << syntax_constraints << std::endl;
  else
    fout << syntax_no_constraints << std::endl;

  fout << sygus_ts_buf_.GetInitDef() << std::endl;
  fout << std::endl;
  fout << sygus_ts_buf_.GetTransDef() << std::endl;
  fout << std::endl;
  fout << sygus_ts_buf_.GetFprevDef(prevF) << std::endl;
  fout << std::endl;
  fout << sygus_ts_buf_.GetPrimalVarDef() << std::endl;
  fout << std::endl;
  fout << sygus_ts_buf_.GetPrimeVarDef() << std::endl;
  fout << std::endl;
  fout << sygus_ts_buf_.GetInputVarDef() << std::endl;
  
  // facts  -- filter needed with more vars
  fout << std::endl;
  unsigned n_cex = dump_cex_block(cex_to_block, sygus_ts_buf_, fout);
  fout << std::endl;
  dump_fact_allow(facts_all, sygus_ts_buf_, fout);
  fout << std::endl;
  dump_inv_imply_prop(prop_to_imply, sygus_ts_buf_, fout);
  fout << std::endl;

  assert (!(n_cex == 0 && prop_to_imply == nullptr));

  // imply  // '(constraint (=> (and (Fminus2 {argV}) (Tr {argV} {argP})) (INV {argInvP})))'
  if (assert_in_prevF)
    fout << "(constraint (=> (and (and " << sygus_ts_buf_.GetFprevUse() << " " << inv_use << ") "
         << sygus_ts_buf_.GetTransUse()  << ") " 
         << inv_use_next << "))" << std::endl;
  else
    fout << "(constraint (=> (and " << sygus_ts_buf_.GetFprevUse() << " " << sygus_ts_buf_.GetTransUse()  << ") " 
         << inv_use_next << "))" << std::endl;
  // init_imply // '(constraint (=> (Init {argV}) (INV {argInvV})))'
  fout << std::endl;
  fout << "(constraint (=> " << sygus_ts_buf_.GetInitUse() << " " << inv_use + "))" << std::endl;
  fout << std::endl;
  fout << "(check-synth)\n";
  fout << std::endl;

} // SyGusQueryGen::GenToFile



} // namespace sygus

} // namespace cosa