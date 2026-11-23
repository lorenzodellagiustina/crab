#include "../common.hpp"
#include "../program_options.hpp"

using namespace std;
using namespace crab::cfg;
using namespace crab::cfg_impl;
using namespace crab::domain_impl;

/*
  With powerset.merge_closest, exceeding powerset.max_disjuncts joins the
  two closest disjuncts instead of smashing all of them.

    // x in [0, 255]
    c = 2;
    if (x <= 9) c += 500; else c += 10;
    c += 1;
    if (x <= 199) c += 1;
    c += 1;
    if (x <= 9)  assert(c == 505);
    if (x >= 10) assert(c >= 14 && c <= 15);

  Before the last block, three disjuncts reach the join:
    x in [0, 9]     c = 504
    x in [10, 199]  c = 14
    x in [200, 255] c = 13
  With at most two disjuncts, smashing them loses the relation between x
  and c, and proves no assertion. Joining the closest two (the last two)
  keeps x in [0, 9] with c = 505 apart, and proves all of them.
 */
std::unique_ptr<z_cfg_t> prog(variable_factory_t &vfac) {
  z_var x(vfac["x"], crab::INT_TYPE, 32);
  z_var c(vfac["c"], crab::INT_TYPE, 32);

  auto cfg = std::make_unique<z_cfg_t>("entry", "exit");
  BB(cfg, entry);
  BB(cfg, cheap);
  BB(cfg, dear);
  BB(cfg, mid);
  BB(cfg, small);
  BB(cfg, big);
  BB(cfg, last);
  BB(cfg, low);
  BB(cfg, high);
  BB(cfg, exit);

  entry >> dear;
  entry >> cheap;
  dear >> mid;
  cheap >> mid;
  mid >> small;
  mid >> big;
  small >> last;
  big >> last;
  last >> low;
  last >> high;
  low >> exit;
  high >> exit;

  entry.assume(x >= 0);
  entry.assume(x <= 255);
  entry.assign(c, 2);
  dear.assume(x <= 9);
  dear.add(c, c, 500);
  cheap.assume(x >= 10);
  cheap.add(c, c, 10);
  mid.add(c, c, 1);
  small.assume(x <= 199);
  small.add(c, c, 1);
  big.assume(x >= 200);
  last.add(c, c, 1);
  low.assume(x <= 9);
  low.assertion(c == 505);
  high.assume(x >= 10);
  high.assertion(c >= 14);
  high.assertion(c <= 15);
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

  crab::outs() << "=== at most 2 disjuncts, smashing ===\n";
  powerset_domain_params smash(false /*exact_meet*/, 2 /*max_disjuncts*/,
                               false /*merge_closest*/,
                               false /*pairwise_widening*/);
  crab_domain_params_man::get().update_params(smash);
  check_all<z_pow_aa_int_t>(cfg, stats_enabled);

  crab::outs() << "=== at most 2 disjuncts, merging the closest ===\n";
  powerset_domain_params closest(false /*exact_meet*/, 2 /*max_disjuncts*/,
                                 true /*merge_closest*/,
                                 false /*pairwise_widening*/);
  crab_domain_params_man::get().update_params(closest);
  check_all<z_pow_aa_int_t>(cfg, stats_enabled);
  return 0;
}
