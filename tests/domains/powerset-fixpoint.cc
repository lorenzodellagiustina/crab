#include "../common.hpp"
#include "../program_options.hpp"

using namespace std;
using namespace crab::cfg;
using namespace crab::cfg_impl;
using namespace crab::domain_impl;

/*
  The post-fixpoint check of a loop must not stop before the loop head's
  invariant covers every state that reaches it.

    x = 0;
    z = 0;
    while (nd()) {
      if (x == 5) z = 1;
      if (x == 0) x = 10; else x = 5;
    }
    assert(z == 0);   // does not hold: x is 5 at the head of the third iteration

  With the powerset of intervals, the head holds {x=0}, then {x=0} or {x=10},
  then {x=0} or {x=10} or {x=5}. The state x=5 is new at the third step, but its
  convex hull, x in [0,10], is the hull of the previous step. An inclusion check
  that compares the convex hulls declares the post-fixpoint there, before the
  loop body is analyzed from x=5, and the assertion is wrongly proven.
 */
std::unique_ptr<z_cfg_t> prog(variable_factory_t &vfac) {
  z_var x(vfac["x"], crab::INT_TYPE, 32);
  z_var z(vfac["z"], crab::INT_TYPE, 32);

  auto cfg = std::make_unique<z_cfg_t>("entry", "exit");
  BB(cfg, entry);
  BB(cfg, head);
  BB(cfg, is5);
  BB(cfg, not5);
  BB(cfg, mid);
  BB(cfg, is0);
  BB(cfg, not0);
  BB(cfg, latch);
  BB(cfg, exit);

  entry >> head;
  head >> is5;
  head >> not5;
  is5 >> mid;
  not5 >> mid;
  mid >> is0;
  mid >> not0;
  is0 >> latch;
  not0 >> latch;
  latch >> head;
  head >> exit;

  entry.assign(x, 0);
  entry.assign(z, 0);
  is5.assume(x == 5);
  is5.assign(z, 1);
  not5.assume(x != 5);
  is0.assume(x == 0);
  is0.assign(x, 10);
  not0.assume(x != 0);
  not0.assign(x, 5);
  exit.assertion(z == 0);
  return cfg;
}

int main(int argc, char **argv) {
  bool stats_enabled = false;
  if (!crab_tests::parse_user_options(argc, argv, stats_enabled)) {
    return 0;
  }
  variable_factory_t vfac;
  auto cfg = prog(vfac);
  crab::outs() << *cfg << "\n";

  // The assertion must be reported as possibly failing ("warning"), never
  // as proven ("safe").
  check_all<z_pow_aa_int_t>(cfg, stats_enabled);
  return 0;
}
