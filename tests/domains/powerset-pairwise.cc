#include "../common.hpp"
#include "../program_options.hpp"

using namespace std;
using namespace crab::cfg;
using namespace crab::cfg_impl;
using namespace crab::domain_impl;

/*
  Disjuncts that enter a loop separately stay separate through it with
  powerset.pairwise_widening.

    if (mode == 3)      k = 40;
    else if (mode == 7) k = 10;
    else                k = 0;     // mode >= 8
    for (i = 0; i < k; i++) {}
    if (mode == 3)  assert(i == 40);
    if (mode == 7)  assert(i == 10);
    if (mode >= 8)  assert(i == 0);

  The three assertions hold. Smashing the disjuncts at the loop head
  gives k in [0, 40] and i in [0, 40], unrelated to mode, so none of
  them is proven. Widening each disjunct separately keeps one disjunct
  per value of k, and proves all three, with intervals.
 */
std::unique_ptr<z_cfg_t> prog(variable_factory_t &vfac) {
  z_var mode(vfac["mode"], crab::INT_TYPE, 32);
  z_var k(vfac["k"], crab::INT_TYPE, 32);
  z_var i(vfac["i"], crab::INT_TYPE, 32);

  auto cfg = std::make_unique<z_cfg_t>("entry", "exit");
  BB(cfg, entry);
  BB(cfg, m3);
  BB(cfg, m7);
  BB(cfg, mother);
  BB(cfg, pre);
  BB(cfg, head);
  BB(cfg, body);
  BB(cfg, after);
  BB(cfg, a3);
  BB(cfg, a7);
  BB(cfg, aother);
  BB(cfg, exit);

  entry >> m3;
  entry >> m7;
  entry >> mother;
  m3 >> pre;
  m7 >> pre;
  mother >> pre;
  pre >> head;
  head >> body;
  body >> head;
  head >> after;
  after >> a3;
  after >> a7;
  after >> aother;
  a3 >> exit;
  a7 >> exit;
  aother >> exit;

  m3.assume(mode == 3);
  m3.assign(k, 40);
  m7.assume(mode == 7);
  m7.assign(k, 10);
  mother.assume(mode >= 8);
  mother.assign(k, 0);
  pre.assign(i, 0);
  body.assume(i <= k - 1);
  body.add(i, i, 1);
  after.assume(i >= k);
  a3.assume(mode == 3);
  a3.assertion(i == 40);
  a7.assume(mode == 7);
  a7.assertion(i == 10);
  aother.assume(mode >= 8);
  aother.assertion(i == 0);
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

  // The default: the disjuncts are smashed at widening. Nothing is proven.
  crab::outs() << "=== smashing widening ===\n";
  check_all<z_pow_aa_int_t>(cfg, stats_enabled);

  // Pairwise widening (with the exact meet that the narrowing phase starts
  // with). All three assertions are proven.
  crab::outs() << "=== pairwise widening ===\n";
  powerset_domain_params p(true /*exact_meet*/, 16 /*max_disjuncts*/,
                           true /*merge_closest*/, true /*pairwise_widening*/);
  crab_domain_params_man::get().update_params(p);
  check_all<z_pow_aa_int_t>(cfg, stats_enabled);
  return 0;
}
