#include "gtest/gtest.h"
#include "utils/partial_model.h"
#include "utils/sygus_ic3formula_helper.h"
#include "smt/available_solvers.h"


using namespace pono;
using namespace smt;
using namespace std;

namespace pono_tests {

class DynamicCoiUnitTests : 
                     public ::testing::Test,
                     public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    s->set_opt("produce-models", "true");
    s->set_opt("incremental", "true");
    boolsort = s->make_sort(BOOL);
    bvsort8 = s->make_sort(BV, 8);
  }
  SmtSolver s;
  Sort boolsort, bvsort8;
};

#define V(name)   (s->make_symbol((name), bvsort8))
#define C(num)    (s->make_term((num), bvsort8))
#define NOT(x)    (s->make_term(Not, (x)))
#define ADD(x, y) (s->make_term(BVAdd, (x), (y)))
#define SUB(x, y) (s->make_term(BVSub, (x), (y)))
#define BVAND(x, y) (s->make_term(BVAnd, (x), (y)))
#define L_AND(x, y) (s->make_term(And, (x), (y)))
#define BVOR(x, y) (s->make_term(BVOr, (x), (y)))
#define EQ(x, y) (s->make_term(Equal, (x), (y)))
#define BVULT(x, y) (s->make_term(BVUlt, (x), (y)))
//#define BoolEQ(x, y) (s->make_term(Iff, (x), (y)))
#define ITE(c, x, y) (s->make_term(Ite, (c), (x), (y)))

#define CheckPartialModel(p,u) \
    {      \
      s->push();                         \
      auto ast = EQ(p, u);        \
      s->assert_formula(ast);            \
      if ( s->check_sat().is_sat() ) {   \
        auto m_cube = pt.GetPartialModelInCube(ast);   \
        std::cout << "expr: " << ast << std::endl; \
        std::cout << m_cube.first.term << std::endl;     \
        std::cout << m_cube.second.to_string() << std::endl; \
        s->pop(); s->push();\
        s->assert_formula(NOT(ast));\
        s->assert_formula(m_cube.first.term);\
        EXPECT_TRUE(s->check_sat().is_unsat()); \
      }                                  \
      s->pop();                          \
    }

TEST_P(DynamicCoiUnitTests, SimpleCoiTest)
{
  
    Term a = V("a");
    Term b = V("b");
    Term c = V("c");
    Term d = V("d");
    Term e = V("e");
    Term f = V("f");
    Term g = V("g");

    Term u = V("u");
    Term v = V("v");
    Term w = V("w");
    Term x = V("x");
    Term y = V("y");
    Term z = V("z");
    
    auto x_plus_1 = ADD(x, C(1));
    auto x_sub_1 = SUB(x, C(1));
    auto x_and_1 = BVAND(x, C(1));
    auto x_plus_y = ADD(x, y);
    auto x_sub_y = SUB(x, y);
    auto x_and_y = BVAND(x, y);
    auto t0 = BVAND(x, x_sub_1);
    auto t1 = BVAND(y, x_sub_1);
    auto t2 = ADD(x, x_sub_1);
    auto t4 = ADD(x, x_and_1);
    auto t5 = ADD(y, x_and_1);
    auto t6 = ADD(y, x_sub_1);

    auto e1 = ITE(EQ(SUB(x, y), z), ADD(a, b), c);
    auto e2 = ITE(EQ(SUB(x, y), x), ADD(a, b), SUB(a, c));
    auto e3 = ITE(EQ(BVAND(x, y), x), BVAND(a, b), BVOR(a, c));
    auto e4a = ITE(EQ(SUB(u, SUB(v,w)), d), ADD(e, f), g);
    auto e4b = ITE( EQ( EQ(BVAND(a, SUB(e1,e2)), f), EQ(BVAND(x, y), x) ), ADD(e4a, f), e1);


    PartialModelGen pt(s);
    
    CheckPartialModel(x_plus_1, u);
    CheckPartialModel(x_sub_1, u);
    CheckPartialModel(x_and_1, u);
    CheckPartialModel(x_plus_y, u);
    CheckPartialModel(x_sub_y, u);
    CheckPartialModel(x_and_y, u);
    CheckPartialModel(t0, u);
    CheckPartialModel(t1, u);
    CheckPartialModel(t2, u);
    CheckPartialModel(t4, u);
    CheckPartialModel(t5, u);
    CheckPartialModel(t6, u);
    CheckPartialModel(e1, u);
    CheckPartialModel(e2, u);
    CheckPartialModel(e3, u);
    CheckPartialModel(e4a, u);
    CheckPartialModel(e4b, u);
}


#define CheckPartialModel_bitlevel(ast_in) \
    {      \
      s->push();                         \
      auto ast = (ast_in);  \
      s->assert_formula(ast);            \
      auto r = s->check_sat(); \
      if ( r.is_sat() ) {   \
        auto m_cube = pt.GetPartialModelInCube_bitlevel(ast);   \
        std::cout << "expr: " << (ast) << std::endl; \
        std::cout << m_cube.first.term << std::endl;     \
        std::cout << m_cube.second.to_string() << std::endl; \
        s->pop(); s->push();\
        s->assert_formula(NOT(ast));\
        s->assert_formula(m_cube.first.term);\
        EXPECT_TRUE(s->check_sat().is_unsat()); \
      }                                  \
      s->pop();                          \
    }

TEST_P(DynamicCoiUnitTests, BitCoiTest)
{
    Term a = V("a");
    Term b = V("b");
    Term c = V("c");
    Term d = V("d");
    Term e = V("e");
    Term f = V("f");
    Term g = V("g");

    Term u = V("u");
    Term v = V("v");
    Term w = V("w");
    Term x = V("x");
    Term y = V("y");
    Term z = V("z");
    
    auto x_plus_1 = ADD(x, C(1));
    auto x_sub_1 = SUB(x, C(1));
    auto x_and_1 = BVAND(x, C(1));
    auto x_plus_y = ADD(x, y);
    auto x_sub_y = SUB(x, y);
    auto x_and_y = BVAND(x, y);
    auto t0 = BVAND(x, x_sub_1);
    auto t1 = BVAND(y, x_sub_1);
    auto t2 = ADD(x, x_sub_1);
    auto t4 = ADD(x, x_and_1);
    auto t5 = ADD(y, x_and_1);
    auto t6 = ADD(y, x_sub_1);
    auto tc1 = L_AND(L_AND(L_AND(BVULT(x, C(8)), BVULT(C(4), x)), L_AND(BVULT(y, C(4)), BVULT(C(1), y))), EQ(BVAND(x,y), C(0)));
    auto tc2 = L_AND(BVULT(C(2),x), BVULT(C(2),y));
    auto tc3 = L_AND(L_AND(BVULT(C(2),x), BVULT(C(2),y)), BVULT(x,y));


    auto e1 = ITE(EQ(SUB(x, y), z), ADD(a, b), c);  // x-y==z ? a+b : c
    auto e2 = ITE(EQ(SUB(x, y), x), ADD(a, b), SUB(a, c)); // x-y==z ? a+b : a-c
    auto e3 = ITE(EQ(BVAND(x, y), x), BVAND(a, b), BVOR(a, c)); // x&y == x ? a&b : a|c
    auto e4a = ITE(EQ(SUB(u, SUB(v,w)), d), ADD(e, f), g); // u-(v-w) == d ? e+f : g
    auto e4b = ITE( EQ( EQ(BVAND(a, SUB(e1,e2)), f), EQ(BVAND(x, y), x) ), ADD(e4a, f), e1); 
    // (a & (e1-e2) == f) == (x & y == x) ? e4a+f : e1


    PartialModelGen pt(s);
    
    CheckPartialModel_bitlevel(EQ(x_plus_1, u));
    CheckPartialModel_bitlevel(EQ(x_sub_1, u));
    CheckPartialModel_bitlevel(EQ(x_and_1, u));
    CheckPartialModel_bitlevel(EQ(x_plus_y, u));
    CheckPartialModel_bitlevel(EQ(x_sub_y, u));
    CheckPartialModel_bitlevel(EQ(x_and_y, u));
    CheckPartialModel_bitlevel(EQ(t0, u));
    CheckPartialModel_bitlevel(EQ(t1, u));
    CheckPartialModel_bitlevel(EQ(t2, u));
    CheckPartialModel_bitlevel(EQ(t4, u));
    CheckPartialModel_bitlevel(EQ(t5, u));
    CheckPartialModel_bitlevel(EQ(t6, u));
    CheckPartialModel_bitlevel(EQ(e1, u));
    CheckPartialModel_bitlevel(EQ(e2, u));
    CheckPartialModel_bitlevel(EQ(e3, u));
    CheckPartialModel_bitlevel(EQ(e4a, u));
    CheckPartialModel_bitlevel(EQ(e4b, u));
    CheckPartialModel_bitlevel(tc1);
    CheckPartialModel_bitlevel(tc2);
    CheckPartialModel_bitlevel(tc3);
}


INSTANTIATE_TEST_SUITE_P(ParameterizedDynamicCoiUnitTests,
                         DynamicCoiUnitTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace pono_tests
