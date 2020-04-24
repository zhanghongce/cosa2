#include <utility>
#include <vector>

#include "available_solvers.h"
#include "core/fts.h"
#include "engines/sygus/container_shortcut.h"
#include "engines/sygus/partial_model.h"
#include "core/unroller.h"
#include "gtest/gtest.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/smt.h"
#include "utils/exceptions.h"

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
    s = BoolectorSolverFactory::create();
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

}  // namespace cosa_tests
