#include <utility>
#include <vector>
#include <fstream>

#include "core/fts.h"
#include "core/prop.h"
#include "core/rts.h"
#include "core/unroller.h"
#include "gtest/gtest.h"
#include "smt/available_solvers.h"
#include "utils/exceptions.h"
#include "frontends/property_if.h"

using namespace pono;
using namespace smt;
using namespace std;

namespace pono_tests {

class PropertyInterfaceUnitTests : public ::testing::Test,
                    public ::testing::WithParamInterface<SolverEnum>
{
 protected:
  void SetUp() override
  {
    s = create_solver(GetParam());
    bvsort = s->make_sort(BV, 8);
  }
  SmtSolver s;
  Sort bvsort;
};

TEST_P(PropertyInterfaceUnitTests, PropertyParsing)
{
  FunctionalTransitionSystem fts(s);

  // state variables without state updates
  // will make the system non-deterministic
  Term x = fts.make_statevar("x", bvsort);

  // x' := x + 1
  fts.assign_next(x, s->make_term(BVAdd, x, s->make_term(1, bvsort)));

  Term y = fts.make_statevar("y", bvsort);
  // y' := y
  fts.assign_next(y, y);

  {
    std::ofstream fout("/tmp/pono_property_if_test.smt2");
    EXPECT_TRUE(fout.is_open());
    fout << "(define-fun assumption.0 ((y (_ BitVec 8))) Bool (bvule y y))" << std::endl;
    fout << "(define-fun assertion.0 ((x (_ BitVec 8)) (y (_ BitVec 8))) Bool (bvult y x))" << std::endl;
  }

  PropertyInterface prop_if("/tmp/pono_property_if_test.smt2", fts);
  
  EXPECT_EQ(fts.constraints().size(), 0);
  prop_if.AddAssumptionsToTS();
  EXPECT_EQ(fts.constraints().size(), 1);

  auto term_true = s->make_term(true);
  auto prop_new = prop_if.AddAssertions(term_true);

  EXPECT_TRUE(term_true->to_string() == "true" || term_true->to_string() == "#b1");
  EXPECT_NE(prop_new->to_string(), "true" );
  EXPECT_NE(prop_new->to_string(), "#b1" );
}


INSTANTIATE_TEST_SUITE_P(ParameterizedSolverPropertyInterfaceUnitTests,
                         PropertyInterfaceUnitTests,
                         testing::ValuesIn(available_solver_enums()));

}  // namespace pono_tests
