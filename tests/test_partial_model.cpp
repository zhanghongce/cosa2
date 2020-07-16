#include <utility>
#include <vector>
#include <fstream>
#include <unistd.h>

#include "available_solvers.h"
#include "core/fts.h"
#include "engines/sygus/partial_model.h"
#include "engines/sygus/opextract.h"
#include "core/unroller.h"
#include "gtest/gtest.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smt.h"
#include "utils/exceptions.h"
#include "utils/container_shortcut.h"
#include "frontends/btor2_encoder.h"
#include "frontends/smtlib2parser.h"
#include "sygus/gen_sygus_query.h"
#include "sygus/sat_enum.h"
#ifdef WITH_MSAT
  #include "smt-switch/msat_factory.h"
#endif

using namespace cosa;
using namespace smt;
using namespace std;

namespace cosa_tests {

#define NOT(x)    (s->make_term(Not, (x)))
#define ADD(x, y) (s->make_term(BVAdd, (x), (y)))
#define SUB(x, y) (s->make_term(BVSub, (x), (y)))
#define BVAND(x, y) (s->make_term(BVAnd, (x), (y)))
#define BVOR(x, y) (s->make_term(BVOr, (x), (y)))
#define EQ(x, y) (s->make_term(BVComp, (x), (y)))
#define BoolEQ(x, y) (s->make_term(Iff, (x), (y)))
#define ITE(c, x, y) (s->make_term(Ite, (c), (x), (y)))

bool SameVar(const Model &m, const std::unordered_set<smt::Term> & vars) {
  for (auto && v : vars)
    if (!IN(v, m.cube))
      return false;
  for (auto &&v_val : m.cube)
    if (!IN(v_val.first, vars))
      return false;
  return true;
}

#define PM(p,u) \
    {      \
      s->push();                         \
      auto ast = EQ(p, u);        \
      s->assert_formula(ast);            \
      if ( s->check_sat().is_sat() ) {   \
        Model m;                         \
        pt.GetPartialModel(ast, m.cube, false); \
        pt.CacheNode(ast);\
        CondVarBuffer * tree = pt.CheckCache(ast); assert(tree); \
        std::unordered_set<smt::Term> v2; \
        pt.InterpretCache(tree, v2);\
        EXPECT_TRUE(SameVar(m, v2));\
        std::cout << "expr: " << ast << std::endl; \
        std::cout << m << std::endl;     \
        Model m2(s, v2);\
        std::cout << m2 << std::endl;     \
        smt::Term v_assign = m.to_expr(s); \
        s->pop(); s->push();\
        s->assert_formula(NOT(ast));\
        s->assert_formula(v_assign);\
        EXPECT_TRUE(s->check_sat().is_unsat()); \
      }                                  \
      s->pop();                          \
    }                                    \

TEST(PartialModelGen, PartialModelBoolector) {
    SmtSolver s;
    s = BoolectorSolverFactory::create(false);
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");
    Sort bvsort = s->make_sort(BV, 8);

    Term a = s->make_symbol("a", bvsort);
    Term b = s->make_symbol("b", bvsort);
    Term c = s->make_symbol("c", bvsort);
    Term d = s->make_symbol("d", bvsort);
    Term e = s->make_symbol("e", bvsort);
    Term f = s->make_symbol("f", bvsort);
    Term g = s->make_symbol("g", bvsort);

    Term u = s->make_symbol("u", bvsort);
    Term v = s->make_symbol("v", bvsort);
    Term w = s->make_symbol("w", bvsort);
    Term x = s->make_symbol("x", bvsort);
    Term y = s->make_symbol("y", bvsort);
    Term z = s->make_symbol("z", bvsort);

    auto x_plus_1 = s->make_term(BVAdd, x, s->make_term(1, bvsort));
    auto x_sub_1 = s->make_term(BVSub, x, s->make_term(1, bvsort));
    auto x_and_1 = s->make_term(BVAnd, x, s->make_term(1, bvsort));
    auto x_plus_y = ADD(x, y);
    auto x_sub_y = SUB(x, y);
    auto x_and_y = BVAND(x, y);
    auto t0 = BVAND(x, x_sub_1);
    auto t1 = BVAND(y, x_sub_1);
    auto t2 = ADD(x, x_sub_1);
    auto t3 = ADD(x, s->make_term(BVSub, x, s->make_term(1, bvsort)));
    auto t4 = ADD(x, x_and_1);
    auto t5 = ADD(y, x_and_1);
    auto t6 = ADD(y, s->make_term(BVAnd, x, s->make_term(1, bvsort)));

    auto e1 = ITE(EQ(SUB(x, y), z), ADD(a, b), c);
    auto e2 = ITE(EQ(SUB(x, y), x), ADD(a, b), SUB(a, c));
    auto e3 = ITE(EQ(BVAND(x, y), x), BVAND(a, b), BVOR(a, c));
    auto e4a = ITE(EQ(SUB(u, SUB(v,w)), d), ADD(e, f), g);
    auto e4b = ITE( BoolEQ( EQ(BVAND(a, SUB(e1,e2)), f), EQ(BVAND(x, y), x) ), ADD(e4a, f), e1);


    PartialModelGen pt(s);
    PM(x_plus_1, u);
    PM(x_sub_1, u);
    PM(x_and_1, u);
    PM(x_plus_y, u);
    PM(x_sub_y, u);
    PM(x_and_y, u);
    PM(t0, u);
    PM(t1, u);
    PM(t2, u);
    PM(t3, u);
    PM(t4, u);
    PM(t5, u);
    PM(t6, u);
    PM(e1, u);
    PM(e2, u);
    PM(e3, u);
    PM(e4a, u);
    PM(e4b, u);

}

TEST (OpExtract, OpExtractAllBtor) {
    SmtSolver s;
    s = BoolectorSolverFactory::create(false);
    Sort bvsort8 = s->make_sort(BV, 8);
    Sort bvsort4 = s->make_sort(BV, 4);
    Sort bvsort1 = s->make_sort(BV, 1);
    Sort boolean = s->make_sort(BOOL);

    Term a8 = s->make_symbol("a.^8", bvsort8);
    Term b8 = s->make_symbol("b8", bvsort8);
    Term c4 = s->make_symbol("c.^4", bvsort4);
    Term d4 = s->make_symbol("d4", bvsort4);
    Term eb = s->make_symbol("eb", boolean);
    Term fb = s->make_symbol("fb", boolean);

    Term bv8_1 = s->make_term(1, bvsort8);
    Term bv8_2 = s->make_term(2, bvsort8);
    Term bv4_3 = s->make_term(3, bvsort4);
    Term bv4_4 = s->make_term(4, bvsort4);
    Term b0 = s->make_term(false);
    Term b1 = s->make_term(true);

    auto p1 = s->make_term(BVAdd, a8, b8);
    auto p2 = s->make_term(BVSub, p1, b8);
    
    auto p3 = s->make_term(Op(Extract, 3, 0), s->make_term(BVAdd,a8,bv8_2) );
    auto p4 = s->make_term(BVAdd, s->make_term(Op(Extract, 4, 1), b8), bv4_3);
    auto p5 = s->make_term(BVAdd, s->make_term(BVAdd, c4, p3), p4);
    auto p6 = s->make_term(Op(Rotate_Left, 2), p5);
    auto p7 = s->make_term(Op(Sign_Extend, 1), s->make_term(BVXor, p6, bv4_3));
    auto p8 = s->make_term(Op(Zero_Extend, 3), p7);
    auto p9 = s->make_term(BVUle, s->make_term(BVXor, p1, p8), p2);
    auto p10 = s->make_term(Iff, fb, s->make_term(Implies, eb, p9));

    OpExtractor opext;
    std::cout << "Expr:" <<  p10->to_string() << std::endl;
    opext.WalkBFS(p10);
    opext.GetSyntaxConstruct().RemoveUnusedStructure();
    const auto & lang_constructs = opext.GetSyntaxConstruct().GetSyntaxConstruct();
    std::cout << "Syntax width " ;
    for (auto && w_c : lang_constructs) {
      std::cout << w_c.first << " " ;
    }
    std::cout << "\n" ;
    for (auto && w_c : lang_constructs) {
      std::cout << "-----------------------" << std::endl ;
      std::cout << "width " << w_c.first << std::endl << "V: " ;
      for (auto && s: w_c.second.symbol_names)
        std::cout << s << " ";
      std::cout << "\nConsts: ";
      for (auto && s: w_c.second.constants)
        std::cout << s << " ";
      std::cout << "\n";
    }

    std::cout << std::endl ;

}

extern const char * ts_btor;
extern const char * inv_string;

static std::string mktemp() {
  char tmpl [] = "/tmp/XXXXXX";
  int fd = mkstemp(tmpl);
  close(fd);

  std::string retname(tmpl);
  return retname;
}

static std::string mktemp_btor() {
  char tmpl [] = "/tmp/XXXXXX";
  int fd = mkstemp(tmpl);
  size_t len = write(fd, (const void *) ts_btor, strlen(ts_btor));
  assert(len == strlen(ts_btor));
  std::string retname(tmpl);
  return retname;
}

#ifdef WITH_MSAT
TEST (OpExtract, OpExtractAllMathSat) {
    SmtSolver s;
    s = MsatSolverFactory::create_interpolating_solver();
    Sort bvsort8 = s->make_sort(BV, 8);
    Sort bvsort4 = s->make_sort(BV, 4);
    Sort bvsort1 = s->make_sort(BV, 1);
    Sort boolean = s->make_sort(BOOL);

    Term a8 = s->make_symbol("a.^8", bvsort8);
    Term b8 = s->make_symbol("b8", bvsort8);
    Term c4 = s->make_symbol("c.^4", bvsort4);
    Term d4 = s->make_symbol("d4", bvsort4);
    Term eb = s->make_symbol("eb", boolean);
    Term fb = s->make_symbol("fb", boolean);

    Term bv8_1 = s->make_term(1, bvsort8);
    Term bv8_2 = s->make_term(2, bvsort8);
    Term bv4_3 = s->make_term(3, bvsort4);
    Term bv4_4 = s->make_term(4, bvsort4);
    Term b0 = s->make_term(false);
    Term b1 = s->make_term(true);

    auto p1 = s->make_term(BVAdd, a8, b8);
    auto p2 = s->make_term(BVSub, p1, b8);
    
    auto p3 = s->make_term(Op(Extract, 3, 0), s->make_term(BVAdd,a8,bv8_2) );
    auto p4 = s->make_term(BVAdd, s->make_term(Op(Extract, 4, 1), b8), bv4_3);
    auto p5 = s->make_term(BVAdd, s->make_term(BVAdd, c4, p3), p4);
    auto p6 = s->make_term(Op(Rotate_Left, 2), p5);
    auto p7 = s->make_term(Op(Sign_Extend, 1), s->make_term(BVXor, p6, bv4_3));
    auto p8 = s->make_term(Op(Zero_Extend, 3), p7);
    auto p9 = s->make_term(BVUle, s->make_term(BVXor, p1, p8), p2);
    auto p10 = s->make_term(Iff, fb, s->make_term(Implies, eb, p9));

    OpExtractor opext;
    std::cout << "Expr:" <<  p10->to_string() << std::endl;
    opext.WalkBFS(p10);
    opext.GetSyntaxConstruct().RemoveUnusedStructure();
    const auto & lang_constructs = opext.GetSyntaxConstruct().GetSyntaxConstruct();
    std::cout << "Syntax width " ;
    for (auto && w_c : lang_constructs) {
      std::cout << w_c.first << " " ;
    }
    std::cout << "\n" ;
    for (auto && w_c : lang_constructs) {
      std::cout << "-----------------------" << std::endl ;
      std::cout << "width " << w_c.first << std::endl << "V: " ;
      for (auto && s: w_c.second.symbol_names)
        std::cout << s << " ";
      std::cout << "\nConsts: ";
      for (auto && s: w_c.second.constants)
        std::cout << s << " ";
      std::cout << "\n";
    }

    std::cout << std::endl ;
}

TEST (SygusGen, SygusGen)  {
    std::string fname = mktemp_btor();
    std::string sygus_file = mktemp();
    SmtSolver msat;
    SmtSolver btor;
    msat = MsatSolverFactory::create_interpolating_solver();
    btor = BoolectorSolverFactory::create(false);

    FunctionalTransitionSystem fts_msat(msat);
    BTOR2Encoder btor_enc_msat(fname, fts_msat);

    FunctionalTransitionSystem fts_btor(btor);
    BTOR2Encoder btor_enc_btor(fname, fts_btor);

    sygus::SyGuSTransBuffer sygus_buf(fts_msat, fts_btor);

    OpExtractor opext;
    opext.WalkBFS(fts_msat.trans());
    opext.WalkBFS(fts_msat.init());
    opext.GetSyntaxConstruct().RemoveUnusedStructure();
    const auto & lang_constructs = opext.GetSyntaxConstruct();
    
    std::unordered_set<std::string> state_name;
    for (auto && msat : fts_msat.states()) {
      state_name.insert(msat->to_string());
    }

    sygus::SyGusQueryGen sygus_query_gen(lang_constructs, sygus_buf, state_name , {});
    
    {
      std::ofstream fout(sygus_file);
      sygus_query_gen.GenToFile(fts_msat.init(), {} , {} , fts_msat.init(), true,true, fout, "");
    }

    {
      std::ifstream fin(sygus_file);
      std::string line;
      while (std::getline(fin, line))
      {
          std::cout << line << std::endl;
      }
    }
    std::cout << "BTOR file : " << fname << std::endl;
    std::cout << "Sygus Query file : " << sygus_file << std::endl;
    
    smt::Term t;
    {
      Smtlib2Parser parser(msat, fts_msat.symbols());
      t = parser.ParseSmtFromString(inv_string);
      ASSERT_NE(t, nullptr);
      if (!t) {
        std::cout << "Parser failed: " << parser.GetParserErrorMessage();
      }
    }
    std::cout <<"Parsed smtlib2: " << t->to_string() << std::endl;
}


TEST (SygusInternal, FromCex)  {
    std::string fname = mktemp_btor();
    SmtSolver msat;
    SmtSolver btor;
    msat = MsatSolverFactory::create_interpolating_solver();
    btor = BoolectorSolverFactory::create(false);
    btor->set_opt("produce-models", "true");
    btor->set_opt("incremental", "true");
    TermTranslator to_msat(msat);

    FunctionalTransitionSystem fts_msat(msat);
    BTOR2Encoder btor_enc_msat(fname, fts_msat);

    FunctionalTransitionSystem fts_btor(btor);
    BTOR2Encoder btor_enc_btor(fname, fts_btor);
    auto prop_btor = btor_enc_btor.propvec()[0];

    OpExtractor opext;
    opext.WalkBFS(fts_msat.trans());
    opext.WalkBFS(fts_msat.init());
    opext.GetSyntaxConstruct().RemoveUnusedStructure();
    const auto & lang_constructs = opext.GetSyntaxConstruct();

    // you need to get cex
    
    PartialModelGen pt(btor);
    Model m;
    {
      btor->push();
      auto t = btor->make_term(smt::Not, prop_btor);
      btor->assert_formula(t);
      auto ret = btor->check_sat();
      EXPECT_EQ(ret.is_sat(), true);
      pt.GetPartialModel(t, m.cube, false);
      btor->pop();
    }
    // and then start the enumerator

    auto btor_var_to_msat_var = [&] (const smt::Term & v) -> smt::Term {
      return to_msat.transfer_term(v, fts_msat.symbols());
    };
    auto to_next = [&] (const smt::Term & v)  -> smt::Term {
      return fts_btor.next(v);
    };

    
    sat_enum::Enumerator sygus_enumerator(
      btor_var_to_msat_var,
      to_next,
      btor,msat,
      fts_btor.trans(), fts_btor.init(),
      fts_btor.init() /*prevF*/, 
      {&m} /*cexs \*/,
      {} /*facts*/,
      nullptr /*prop_btor*/,
      lang_constructs      
    );

    std::cout << "Cex : " << m.to_string() << std::endl;
    std::cout << "Enum # = " << sygus_enumerator.GetCurrentLevelMaxEffort() << std::endl;
    auto res = sygus_enumerator.EnumCurrentLevel();

    std::cout << "Result btor : " << res.first->to_string() << std::endl;

    sygus_enumerator.ClearCache();
} // InternalSygus from cex


TEST (SygusInternal, FromProp)  {
    std::string fname = mktemp_btor();
    SmtSolver msat;
    SmtSolver btor;
    msat = MsatSolverFactory::create_interpolating_solver();
    btor = BoolectorSolverFactory::create(false);
    btor->set_opt("produce-models", "true");
    btor->set_opt("incremental", "true");
    TermTranslator to_msat(msat);

    FunctionalTransitionSystem fts_msat(msat);
    BTOR2Encoder btor_enc_msat(fname, fts_msat);

    FunctionalTransitionSystem fts_btor(btor);
    BTOR2Encoder btor_enc_btor(fname, fts_btor);
    auto prop_btor = btor_enc_btor.propvec()[0];

    OpExtractor opext;
    opext.WalkBFS(fts_msat.trans());
    opext.WalkBFS(fts_msat.init());
    opext.GetSyntaxConstruct().RemoveUnusedStructure();
    const auto & lang_constructs = opext.GetSyntaxConstruct();

    // you need to get cex
    
    // and then start the enumerator

    auto btor_var_to_msat_var = [&] (const smt::Term & v) -> smt::Term {
      return to_msat.transfer_term(v, fts_msat.symbols());
    };
    auto to_next = [&] (const smt::Term & v)  -> smt::Term {
      return fts_btor.next(v);
    };

    
    sat_enum::Enumerator sygus_enumerator(
      btor_var_to_msat_var,
      to_next,
      btor,msat,
      fts_btor.trans(), fts_btor.init(),
      fts_btor.init() /*prevF*/, 
      {} /*cexs \*/,
      {} /*facts*/,
      prop_btor /*prop_btor*/,
      lang_constructs      
    );

    std::cout << "Prop : " << prop_btor -> to_string() << std::endl;
    std::cout << "Enum # = " << sygus_enumerator.GetCurrentLevelMaxEffort() << std::endl;
    auto res = sygus_enumerator.EnumCurrentLevel();

    std::cout << "Result btor : " << res.first->to_string() << std::endl;

    sygus_enumerator.ClearCache();
} // InternalSygus

#endif

const char * inv_string = "(define-fun INV ((cnt (_ BitVec 16)) (|base$5#3| (_ BitVec 16)) (addr-1 (_ BitVec 16))) Bool (and (= addr-1 cnt) (and (= addr-1 |base$5#3|) (= addr-1 (_ bv0 16)))))";

const char * ts_btor = R"***(
; BTOR description generated by Yosys 0.9+2406 (git sha1 c37a278d, gcc 7.5.0-3ubuntu1~18.04 -fPIC -Os) for module cnt.
1 sort bitvec 1
2 input 1 clk*' ; cnt.v:5.9-5.12
3 input 1 en.d ; cnt.v:5.51-5.53
4 sort bitvec 16
5 input 4 inp ; cnt.v:5.40-5.43
6 input 1 rst_ ; cnt.v:5.20-5.23
7 const 4 0000000000000000
8 state 4
9 init 4 8 7
10 output 8 addr-1 ; cnt.v:6.49-6.53
11 state 4
12 init 4 11 7
13 output 11 base$5#3 ; cnt.v:6.23-6.27
14 state 4
15 init 4 14 7
16 output 14 cnt ; cnt.v:6.74-6.77
17 sort bitvec 15
18 const 17 111011000000100
19 uext 4 18 1
20 eq 1 11 19 $eq$cnt.v:20$8 ; cnt.v:20
21 const 4 1101110001100111
22 eq 1 8 21 $eq$cnt.v:20$9 ; cnt.v:20
23 and 1 20 22
24 const 4 1101100001100111
25 eq 1 14 24 $eq$cnt.v:20$11 ; cnt.v:20
26 and 1 23 25
27 not 1 26
28 const 1 1
29 not 1 27
30 and 1 28 29
31 uext 4 28 15
32 add 4 8 31 $add$cnt.v:15$3 ; cnt.v:15
33 ite 4 3 5 32 $ternary$cnt.v:15$5 ; cnt.v:15
34 ite 4 6 7 33 $procmux$19 ; cnt.v:9.6-9.9|cnt.v:9.3-17.6
35 next 4 8 34 $procdff$26 ; cnt.v:8.1-18.4
36 ite 4 3 5 11 $ternary$cnt.v:14$2 ; cnt.v:14
37 ite 4 6 7 36 $procmux$22 ; cnt.v:9.6-9.9|cnt.v:9.3-17.6
38 next 4 11 37 $procdff$25 ; cnt.v:8.1-18.4
39 uext 4 28 15
40 add 4 14 39 $add$cnt.v:16$6 ; cnt.v:16
41 ite 4 3 7 40 $ternary$cnt.v:16$7 ; cnt.v:16
42 ite 4 6 7 41 $procmux$16 ; cnt.v:9.6-9.9|cnt.v:9.3-17.6
43 next 4 14 42 $procdff$24 ; cnt.v:8.1-18.4
44 bad 30
; end of yosys output
)***";

}  // namespace cosa_tests
