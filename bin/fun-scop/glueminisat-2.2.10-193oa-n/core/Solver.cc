/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>
#include <float.h>           // added by nabesima
#include <cstdio>            // added by nabesima
#include <cstdlib>           // added by nabesima
#include <string>            // added by nabesima
#include <fstream>           // added by nabesima
#include <sstream>           // added by nabesima
#include <algorithm>         // added by nabesima

#include "mtl/Sort.h"
#include "mtl/Select.h"      // added by nabesima
#include "utils/System.h"    // added by nabesima
#include "core/Solver.h"
#include "utils/Util.h"      // added by nabesima

using namespace GlueMiniSat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay             (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, true));
static DoubleOption  opt_clause_decay          (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq       (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed           (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode            (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving          (_cat, "phase-saving","Controls the level of phase saving (0=none, 1=limited, 2=full, 3=invert top lv)", 2, IntRange(0, 3));
static BoolOption    opt_rnd_init_act          (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart          (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first         (_cat, "rfirst",      "The base restart interval", 1000, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc           (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac          (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_conf_limit            (_cat, "conf-limit",  "Stopps the solver after the specified number of conflicts occurst (-1=no limit)", -1, IntRange(-1, INT32_MAX));

// added by nabesima
static const char*   _model = "MODEL";
static BoolOption    opt_partial_model         (_model, "partial-model",         "Generate a partial model if possible", false);
static BoolOption    opt_verify_model          (_model, "verify",                "Verify the found model", false);
static const char*   _prop = "PROPAGATION";
static BoolOption    opt_bin_propagation       (_prop,  "bin",                   "Propagation by binary clauses are preferred to longer clauses", true);
static const char*   _simp = "SIMPLIFICATION";
static IntOption     opt_lrn_max_size          (_simp,  "lrn-max-size",          "The maximum size required to minimize a clause", 100, IntRange(0, INT32_MAX));
static BoolOption    opt_lazy_simp             (_simp,  "lazy-simp",             "Use lazy simplification techniques", true);
static IntOption     opt_lazy_interval         (_simp,  "lazy-interval",         "The interval of lazy simplification", 10, IntRange(1, INT32_MAX));
static BoolOption    opt_lazy_fld_probing      (_simp,  "lazy-fld",              "Apply lazy failed-literal probing", true);
static BoolOption    opt_lazy_pol_probing      (_simp,  "lazy-pol",              "Apply lazy polarity probing", true);
static BoolOption    opt_lazy_nec_probing      (_simp,  "lazy-nec",              "Apply lazy necessary assignment probing", true);
static BoolOption    opt_lazy_eqv_probing      (_simp,  "lazy-eqv",              "Apply lazy equivalent variable probing", true);
static BoolOption    opt_lazy_cla_probing      (_simp,  "lazy-cla",              "Apply lazy clause probing", true);
static IntOption     opt_lazy_lrn_min          (_simp,  "lazy-lrn-min",          "Apply learnt clause minimization by binary resolvents (0=none, 1=shallow, 2=deep)", 2, IntRange(0, 2));
static BoolOption    opt_lazy_uw_lit_elim      (_simp,  "lazy-uw-lit-elim",      "Apply lazy unwatched literal elimination", true);
static BoolOption    opt_lazy_pr_lit_elim      (_simp,  "lazy-pr-lit-elim",      "Apply lazy probed literal elimination", false);
static BoolOption    opt_lazy_lit_drop         (_simp,  "lazy-lit-drop",         "Apply lazy literal dropping", false);
static IntOption     opt_lazy_bin_add          (_simp,  "lazy-bin-add",          "On-demand addition of binary resolvents (0=none, 1=prop, 2=conf, 3=1+2)", 3, IntRange(0, 3));
static BoolOption    opt_probed_lit_chain      (_simp,  "probed-lit-chain",      "Identify values of literals propagated by probed ones", true);
static DoubleOption  opt_pr_min_lits           (_simp,  "pr-min-lits",           "The minimum rate of newly probed literals for propagation", 0.0002, DoubleRange(0, true, 1, true));
static IntOption     opt_pr_min_starts         (_simp,  "pr-min-starts",         "The minimum number of restarts to propagate probed literals", 500, IntRange(0, INT32_MAX));
static DoubleOption  opt_rw_min_lits           (_simp,  "rw-min-lits",           "The minimum rate of newly probed equivalent literals for rewriting", 0.01, DoubleRange(0, true, 1, true));
static IntOption     opt_rw_min_starts         (_simp,  "rw-min-starts",         "The minimum number of restarts for rewriting", 500, IntRange(0, INT32_MAX));
static BoolOption    opt_rand_attach           (_simp,  "rand-attach",           "Attach clauses by randomized order after rewriting", false);
static BoolOption    opt_dec_elim              (_simp,  "dec-elim",              "Perform decision variable elimination", true);
static IntOption     opt_dec_elim_lim          (_simp,  "dec-elim-lim",          "Do not perform decision variable elimination if the estimeted number of resolvents > this value (-1 means no limit)", 25, IntRange(-1, INT32_MAX));
static IntOption     opt_dec_elim_len          (_simp,  "dec-elim-len",          "Do not perform decision variable elimination if the estimeted length of resolvents > this value (-1 means no limit)", -1, IntRange(-1, INT32_MAX));
static IntOption     opt_amo                   (_simp,  "amo",                   "Detect at-most-one constraints (0=none, 1=dynamic, 2=dynamic+static", 0, IntRange(0, 2));
static BoolOption    opt_amo_grp               (_simp,  "amo-grp",               "Apply grouping technique for at-most-one constraints", true);
static IntOption     opt_amo_max_bins          (_simp,  "amo-max-bins",          "Apply Mace if the number of bins <= this value", 1000000, IntRange(0, INT32_MAX));
static IntOption     opt_amo_starts            (_simp,  "amo-starts",            "The restart period for detecting at-most-one constraints", 50, IntRange(1, INT32_MAX));
static StringOption  opt_mace_cmd              (_simp,  "mace-cmd",              "The path to mace", "mace");
static const char*   _dec = "DECISION";
static BoolOption    opt_allow_var_act_tie     (_dec,   "allow-var-act-tie",     "Allow a tie of variable order", true);
static BoolOption    opt_rand_rebuild          (_dec,   "rand-rebuild",          "Periodically rebuild variable order heap randomly", false);
static IntOption     opt_rand_rebuild_confs    (_dec,   "rand-rebuild-confs",    "The interval of randomized rebuild", 10000, IntRange(1, INT_MAX));
static BoolOption    opt_inc_var_decay         (_dec,   "inc-var-decay",         "Increase variable decay factor in the initial search", true);
static IntOption     opt_inc_var_decay_period  (_dec,   "inc-var-decay-period",  "The incremental var decay period in the number of conflicts", 100000, IntRange(1, INT32_MAX));
static DoubleOption  opt_inc_var_decay_init    (_dec,   "inc-var-decay-init",    "Initial activity decay factor for incremental var decay", 0.6, DoubleRange(0, false, 1, false));
static IntOption     opt_var_decay_mode        (_dec,   "var-decay-mode",        "Variable decaying strategy (0=fixed, 1=depth)", 0, IntRange(0, 1));
static DoubleOption  opt_var_decay_gain        (_dec,   "var-decay-gain",        "The gain of sigmoid function for variable decaying strategy with depth", 0.01, DoubleRange(0, false, HUGE_VAL, false));
static BoolOption    opt_sloped_var_decay      (_dec,   "sloped-var-decay",      "Variable decaying factor is based on the number of variables", true);
static DoubleOption  opt_max_var_decay         (_dec,   "max-var-decay",         "The maximum value of sloped var-decay", 0.99, DoubleRange(0, false, 1, true));
static DoubleOption  opt_min_var_decay         (_dec,   "min-var-decay",         "The minimum value of sloped var-decay", 0.95, DoubleRange(0, false, 1, true));
static IntOption     opt_max_var_decay_vars    (_dec,   "max-var-decay-vars",    "The number of variables in which the maximum var-decay is used", 500, IntRange(1, INT32_MAX));
static IntOption     opt_min_var_decay_vars    (_dec,   "min-var-decay-vars",    "The number of variables in which the minimum var-decay is used", 10000, IntRange(1, INT32_MAX));
static BoolOption    opt_uip_bumping           (_dec,   "uip-bumping",           "Bump the uip for each conflict", true);
static BoolOption    opt_lbd_act_bumping       (_dec,   "lbd-act-bumping",       "Bump variable activity implied from lbd learnts in conflict analysis", true);
static BoolOption    opt_rand_tiebreak         (_dec,   "rand-tiebreak",         "Randomly select a variable from top ranked ones", false);
static BoolOption    opt_simp_rebuild          (_dec,   "simp-rebuild",          "Rebuild variable ordering heap in simplify", true);
static BoolOption    opt_oa_bin_dec            (_dec,   "oa-bin-dec",            "Apply binary search strategy for order encoded variables", false);
static IntOption     opt_oa_bin_dec_lb         (_dec,   "oa-bin-dec-lb",         "Lower-bound to apply binary search strategy for order encoded variables", 1024, IntRange(1, INT32_MAX));
static const char*   _res = "RESTART";
static IntOption     opt_restart_strategy      (_res,   "restart",               "The restart strategy (0=none, 1=minisat, 2=lbd, 3=dec/conf, 4=lbd + dec/conf)", 2, IntRange(0, 4));
static IntOption     opt_restart_blocking      (_res,   "restart-blocking",      "Block the restart if local propagations per conflict exceeds global one (0=none, 1=trail, 2=props/conf, 3=agility, 4=max trail, 5=props/conf & max trail)", 0, IntRange(0, 5));
static DoubleOption  opt_agility_decay         (_res,   "agility-decay",         "The agility decay factor", 0.9999, DoubleRange(0, true, 1, true));
static DoubleOption  opt_lbd_restart_rate      (_res,   "lbd-restart-rate",      "Restart if local LBD average * this val > threashold", 0.8, DoubleRange(0, true, 1, true));
static DoubleOption  opt_dec_restart_rate      (_res,   "dec-restart-rate",      "Restart if local average of decisions/conflict * this val > threashold", 0.95, DoubleRange(0, true, 1, true));
static DoubleOption  opt_blk_restart_rate      (_res,   "blk-restart-rate",      "Restart blocking factor", 0.7, DoubleRange(0, true, 5, true));
static IntOption     opt_lbd_queue_size        (_res,   "lbd-queue-size",        "The window size of local average for LBDs", 50, IntRange(1, INT32_MAX));
static IntOption     opt_dec_queue_size        (_res,   "dec-queue-size",        "The window size of local average for decisions/conflict", 50, IntRange(1, INT32_MAX));
static IntOption     opt_trl_queue_size        (_res,   "trl-queue-size",        "The window size of local trails", 5000, IntRange(10, INT32_MAX));
static DoubleOption  opt_blk_restart_weight    (_res,   "blk-restart-weight",    "The scale of wait time when restart is blocked", 1, DoubleRange(0, true, HUGE_VAL, false));
static BoolOption    opt_inc_rst_rate          (_res,   "inc-rst-rate",          "Increase restart-rate factor in the initial search", false);
static IntOption     opt_inc_rst_rate_period   (_res,   "inc-rst-rate-period",   "The incremental restart-rate period in the number of conflicts", 500000, IntRange(1, INT32_MAX));
static DoubleOption  opt_inc_lbd_rst_rate_init (_res,   "inc-lbd_rst-rate-init", "Initial LBD restart-rate factor for incremental restart-rate", 0.6, DoubleRange(0, false, 1, false));
static DoubleOption  opt_inc_dec_rst_rate_init (_res,   "inc-dec_rst-rate-init", "Initial DEC restart-rate factor for incremental restart-rate", 0.75, DoubleRange(0, false, 1, false));
static const char*   _red = "REDUCTION";
static BoolOption    opt_closed_lbd            (_red,   "closed-lbd",            "Use closed-lbd for evaluation criterial of learnts", false);
static DoubleOption  opt_closed_lbd_rate       (_red,   "closed-lbd-rate",       "Decreasing rate of closed-lbd", 0.5, DoubleRange(0, true, 1, true));
static BoolOption    opt_rm_simulate           (_red,   "rm-simulate",           "Simulate removal of learnt clauses", false);
static IntOption     opt_rdb_eval              (_red,   "rdb-eval",              "The evaluation criteria of reduction strategy (0=LRU, 1=LBD, 2=LBD-CVR)", 2, IntRange(0, 2));
static IntOption     opt_rdb_call              (_red,   "rdb-call",              "The call strategy of reduction (0=none, 1=minisat, 2=aggressive, 3=quadratic", 3, IntRange(0, 3));
static DoubleOption  opt_rdb_ub                (_red,   "rdb-ub",                "The upper-bound of reduction", 0.5, DoubleRange(0, true, 1, true));
static DoubleOption  opt_core_lbd_cvr          (_red,   "core-lbd-cvr",          "The use-coverage of core learnt clauses", 0.8, DoubleRange(0, true, 1, true));
static DoubleOption  opt_supp_lbd_cvr          (_red,   "supp-lbd-cvr",          "The use-coverage of supplemental learnt clauses", 0.99, DoubleRange(0, true, 1, true));
static IntOption     opt_core_lbd_lb           (_red,   "core-lbd-lb",           "The lower-bound of core LBD", 2, IntRange(0, INT32_MAX));
static IntOption     opt_supp_lbd_lb           (_red,   "supp-lbd-lb",           "The lower-bound of supp LBD", 2, IntRange(0, INT32_MAX));
static IntOption     opt_core_lbd_prd          (_red,   "core-lbd-prd",          "The holding period of used core learnt clauses", 7, IntRange(0, (1 << TTL_BITS) - 1));
static IntOption     opt_supp_lbd_prd          (_red,   "supp-lbd-prd",          "The holding period of used supplemental learnt clauses", 1, IntRange(0, (1 << TTL_BITS) - 1));
static IntOption     opt_othr_lbd_prd          (_red,   "othr-lbd-prd",          "The holding period of used other learnt clauses", 0, IntRange(0, (1 << TTL_BITS) - 1));
static IntOption	 opt_inc_lrn_limit         (_red,   "inc-lrn-limit",         "Increment the limit of learnt clauses if many better clauses exist", 1000, IntRange(0, INT32_MAX));
static IntOption     opt_frozen_lbd            (_red,   "frozen-lbd",            "Protect clauses if their LBD decrease and is lower than this threashold", 30, IntRange(0, INT32_MAX));
static IntOption     opt_simp_min_starts       (_red,   "simp-min-starts",       "The minimum number of restarts for simplifying clause database", 100, IntRange(0, INT32_MAX));
static BoolOption    opt_rm_low_act_learnts    (_red,   "rm-low-act-learnts",    "Remove learnt clauses whose activity is low", true);
static BoolOption    opt_lv0_reduce_db         (_red,   "lv0-reduce",            "The reduce DB is applied at DLV 0", false);
static IntOption     opt_learnts_init          (_red,   "linit",                 "The initial size of learnt clauses", 20000, IntRange(1, INT32_MAX));
static IntOption     opt_learnts_inc           (_red,   "linc",                  "The factor with which the limit of learnts is added in each reduction", 1000, IntRange(0, INT32_MAX));
static const char*   _inst = "INST";
static IntOption     opt_inst_check            (_inst,  "inst-check",            "Check a given instance is hard when the specified number of conflicts occurs (0=uncheck)", 200000, IntRange(0, INT32_MAX));
static DoubleOption  opt_small_block           (_inst,  "small-block",           "The threashold of small block instances", 1.75, DoubleRange(0, true, HUGE_VAL, false));
static DoubleOption  opt_slow_restart_speed    (_inst,  "slow-restart-speed",    "The threashold of slow-restart instances", 400, DoubleRange(0, true, HUGE_VAL, false));
static IntOption     opt_slow_restart_strategy (_inst,  "slow-restart",          "The restart strategy for slow instances (0=none, 1=minisat, 2=lbd, 3=dec/conf, 4=lbd + dec/conf)", 3, IntRange(0, 4));
static DoubleOption  opt_slow_lbd_restart_rate (_inst,  "slow-lbd-restart-rate", "Restart if local LBD average * this val > threashold", 0.7, DoubleRange(0, true, 2, true));
static DoubleOption  opt_slow_dec_restart_rate (_inst,  "slow-dec-restart-rate", "Restart if local average of decisions/conflict * this val > threashold", 1.0, DoubleRange(0, true, 2, true));
static IntOption     opt_slow_lbd_queue_size   (_inst,  "slow-lbd-queue-size",   "The window size of local average for LBDs", 50, IntRange(1, INT32_MAX));
static IntOption     opt_slow_var_decay_mode   (_inst,  "slow-var-decay-mode",   "The variable decaying strategy (0=fixed, 1=depth)", 0, IntRange(0, 1));
static DoubleOption  opt_slow_var_decay        (_inst,  "slow-var-decay",        "The variable activity decay factor", 0.95, DoubleRange(0, false, 1, true));
static IntOption     opt_slow_glue_threshold   (_inst,  "slow-glue-threshold",   "Learnts whose LBD <= threshold are survived", 2, IntRange(2, INT32_MAX));
static IntOption     opt_slow_phase_saving     (_inst,  "slow-phase-saving",     "The phase saving parameter for slow instances (0=none, 1=limited, 2=full, 3=invert top lv)", 2, IntRange(0, 3));
static DoubleOption  opt_fast_restart_speed    (_inst,  "fast-restart-speed",    "The threashold of fast-restart instances", 125, DoubleRange(0, true, HUGE_VAL, false));
static IntOption     opt_fast_restart_strategy (_inst,  "fast-restart",          "The restart strategy for fast instances (0=none, 1=minisat, 2=lbd, 3=dec/conf, 4=lbd + dec/conf)", 1, IntRange(0, 4));
static DoubleOption  opt_fast_lbd_restart_rate (_inst,  "fast-lbd-restart-rate", "Restart if local LBD average * this val > threashold", 0.8, DoubleRange(0, true, 2, true));
static DoubleOption  opt_fast_dec_restart_rate (_inst,  "fast-dec-restart-rate", "Restart if local average of decisions/conflict * this val > threashold", 0.95, DoubleRange(0, true, 2, true));
static IntOption     opt_fast_lbd_queue_size   (_inst,  "fast-lbd-queue-size",   "The window size of local average for LBDs", 50, IntRange(1, INT32_MAX));
static IntOption     opt_fast_var_decay_mode   (_inst,  "fast-var-decay-mode",   "The variable decaying strategy (0=fixed, 1=depth, 2=delay)", 0, IntRange(0, 2));
static DoubleOption  opt_fast_var_decay        (_inst,  "fast-var-decay",        "The variable activity decay factor", 0.9999, DoubleRange(0, false, 1, true));
static IntOption     opt_fast_glue_threshold   (_inst,  "fast-glue-threshold",   "Learnts whose LBD <= threshold are survived", 2, IntRange(2, INT32_MAX));
static IntOption     opt_fast_phase_saving     (_inst,  "fast-phase-saving",     "The phase saving parameter for fast instances (0=none, 1=limited, 2=full, 3=invert top lv)", 2, IntRange(0, 3));
static const char*   _stats = "STATS";
static IntOption     opt_stats_conf_size       (_stats, "stats-conf-size",       "The base number of conflicts for statistics infomation", 10000, IntRange(1, INT32_MAX));
static IntOption     opt_max_stats_size        (_stats, "max-stats-size",        "The size of statistics infomation", 30, IntRange(0, INT32_MAX));
static const char*   _solver = "SOLVER";
static BoolOption    opt_minisat		       (_solver, "minisat",              "Behaves as MiniSat 2.2.0 (experimental)", false);
static const char*   _cert = "CERTIFIED";
static BoolOption    opt_certified             (_cert,  "certified",             "Certified UNSAT using DRUP format", false);
static StringOption  opt_certified_file        (_cert,  "certified-output",      "Certified UNSAT output file", "NULL");
static BoolOption    opt_vbyte                 (_cert,  "vbyte",                 "Emit proof in variable-byte encoding", false);

// added by nabesima
// Reduce DB measure
#define RDB_LRU              0
#define RDB_LBD              1
#define RDB_LBD_CVR          2

// Call strategy of RDB
#define RDB_CALL_NONE        0
#define RDB_CALL_MINISAT     1
#define RDB_CALL_AGGRESSIVE  2
#define RDB_CALL_QUADRATIC   3

// On-demand adddition
#define ODA_NONE             0
#define ODA_PROP             1
#define ODA_CONF             2
#define ODA_PROP_CONF        3

// Restart strategy
#define RST_NONE             0
#define RST_MINISAT          1
#define RST_LBD              2
#define RST_DEC              3
#define RST_LBD_DEC          4

// The classified instance type
#define INS_UNDEF            0
#define INS_NORMAL           1
#define INS_HARD_FAST        2
#define INS_HARD_SLOW        3
static const char* inst_types[] = {"undef", "normal", "hard-fast", "hard-slow"};

// Restart blocking
#define RBK_NONE             0
#define RBK_TRAIL            1
#define RBK_PROPS_CONF       2
#define RBK_AGILITY          3
#define RBK_MAX_TRAIL        4
#define RBK_PROPS_MAX_TRAIL  5

// The type of probed literals
#define PRB_NONE             0
#define PRB_PREMISE_CHAIN    1
#define PRB_EQV_CHAIN        2
#define PRB_FAILED_LIT       3
#define PRB_POLALITY         4
#define PRB_NECESSARY        5
#define PRB_CLAUSE           6
#define PRB_AMO              7
#define PRB_NUM_TYPES        8

// Detection of at-most-one constraints
#define AMO_NONE             0
#define AMO_DYNAMIC          1
#define AMO_DYNAMIC_STATIC   2

#define NO_AMO              -1

//=================================================================================================
// Constructor/Destructor:

Solver::Solver() :

    // Parameters (user settable):
    //
    parsing          (false)    // added by nabesima
  , verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // added by nabesima
  , native_oa(false)

    // Statistics: (formerly in 'SolverStats')
    //
  // modified by nabesima
  //, solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  //, dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , solves(0), starts(0), decisions(0), rnd_decisions(0), bin_decisions(0), propagations(0), oa_propagations(0), rm_propagations(0), conflicts(0), bin_conflicts(0), rm_conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), tot_literals(0)

  // added by nabesima
  , real_stime(realTime())
  , init_vars(0), simp_vars(0), unit_clauses(0), init_clauses(0), simp_clauses(0), simp_clauses_literals(0)
  , max_confs(0), min_confs(UINT64_MAX), blocked_restarts(0), last_blocked(0), supp_backjumps(0), enqueues(0), dec_confs(0), tot_lbds(0), reduced_LBDs(0)
  , global_LBDs(0), global_lits(0), global_width(0), global_DLVs(0), backjump_dist(0), agility(0.0)
  , max_len_learnt(0), max_len_used_learnt(0), max_lbd_learnt(0), max_lbd_used_learnt(0)
  , rnd_polarities(0), premise_updates(0)
  , rec_rm_lrn_lits(0), bin_rm_lrn_lits(0), lazy_rm_uw_cla_lits(0), lazy_rm_uw_lrn_lits(0), lazy_rm_pr_cla_lits(0), lazy_rm_pr_lrn_lits(0)
  , lazy_lit_droppings(0), lazy_drp_cla_lits(0), lazy_drp_lrn_lits(0), lazy_add_prop_bins(0), lazy_add_conf_bins(0)
  , assign_probed_lits(0), lazy_bin_add_time(0.0)
  , eq_vars(0), eq_amo_vars(0), rewrite_dbs(0), rw_clause_lits(0), rw_learnt_lits(0), rw_taut_clauses(0), rw_taut_learnts(0)
  , rw_unit_clauses(0), rw_unit_learnts(0), subsumed_clauses(0), subsumed_learnts(0)
  , neck_cands(0), neck_preserved(0)
  , simp_dbs(0), reduce_dbs(0), removed_learnts(0), shrinked_assignments(0)
  , simplify_time(0.0), rescale_time(0.0), reduce_time(0.0), rewrite_time(0.0), bin_min_time(0.0), mace_time(0.0), amo_time(0.0), php_time(0.0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , bin_watches        (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity, opt_allow_var_act_tie))
  , progress_estimate  (0)
  , remove_satisfied   (true)

  // Options added by nabesima
  , partial_model         (opt_partial_model)
  , verify_model          (opt_verify_model)
  , bin_propagation       (opt_bin_propagation)
  , lrn_max_size          (opt_lrn_max_size)
  , use_lazy_simp         (opt_lazy_simp)
  , lazy_interval         (opt_lazy_interval)
  , lazy_fld_probing      (opt_lazy_fld_probing)
  , lazy_pol_probing      (opt_lazy_pol_probing)
  , lazy_nec_probing      (opt_lazy_nec_probing)
  , lazy_eqv_probing      (opt_lazy_eqv_probing)
  , lazy_cla_probing      (opt_lazy_cla_probing)
  , lazy_lrn_min          (opt_lazy_lrn_min)
  , lazy_uw_lit_elim      (opt_lazy_uw_lit_elim)
  , lazy_pr_lit_elim      (opt_lazy_pr_lit_elim)
  , lazy_lit_dropping     (opt_lazy_lit_drop)
  , lazy_bin_add          (opt_lazy_bin_add)
  , probed_lit_chain      (opt_probed_lit_chain)
  , pr_min_lits           (opt_pr_min_lits)
  , pr_min_starts         (opt_pr_min_starts)
  , rw_min_lits           (opt_rw_min_lits)
  , rw_min_starts         (opt_rw_min_starts)
  , rand_attach           (opt_rand_attach)
  , dec_elim              (opt_dec_elim)
  , dec_elim_lim          (opt_dec_elim_lim)
  , dec_elim_len          (opt_dec_elim_len)
  , amo                   (opt_amo)
  , amo_grp               (opt_amo_grp)
  , amo_max_bins          (opt_amo_max_bins)
  , amo_starts            (opt_amo_starts)
  , mace_cmd              (opt_mace_cmd)
  , allow_var_act_tie     (opt_allow_var_act_tie)
  , rand_rebuild          (opt_rand_rebuild)
  , rand_rebuild_confs    (opt_rand_rebuild_confs)
  , inc_var_decay         (opt_inc_var_decay)
  , inc_var_decay_period  (opt_inc_var_decay_period)
  , inc_var_decay_confs   (opt_inc_var_decay_period)
  , inc_var_decay_base    (0)
  , inc_var_decay_init    (opt_inc_var_decay_init)
  , inc_var_decay_finished(true)
  , var_decay_mode        (opt_var_decay_mode)
  , var_decay_gain        (opt_var_decay_gain)
  , sloped_var_decay      (opt_sloped_var_decay)
  , max_var_decay         (opt_max_var_decay)
  , min_var_decay         (opt_min_var_decay)
  , max_var_decay_vars    (opt_max_var_decay_vars)
  , min_var_decay_vars    (opt_min_var_decay_vars)
  , uip_bumping           (opt_uip_bumping)
  , lbd_act_bumping       (opt_lbd_act_bumping)
  , rand_tiebreak         (opt_rand_tiebreak)
  , simp_rebuild          (opt_simp_rebuild)
  , oa_bin_dec            (opt_oa_bin_dec)
  , oa_bin_dec_lb         (opt_oa_bin_dec_lb)
  , restart_strategy      (opt_restart_strategy)
  , restart_blocking      (opt_restart_blocking)
  , agility_decay         (opt_agility_decay)
  , lbd_restart_rate      (opt_lbd_restart_rate)
  , dec_restart_rate      (opt_dec_restart_rate)
  , blk_restart_rate      (opt_blk_restart_rate)
  , lbd_queue_size        (opt_lbd_queue_size)
  , dec_queue_size        (opt_dec_queue_size)
  , trl_queue_size        (opt_trl_queue_size)
  , blk_restart_weight    (opt_blk_restart_weight)
  , inc_rst_rate          (opt_inc_rst_rate)
  , inc_rst_rate_period   (opt_inc_rst_rate_period)
  , inc_rst_rate_confs    (opt_inc_rst_rate_period)
  , inc_lbd_rst_rate_base (0)
  , inc_dec_rst_rate_base (0)
  , inc_lbd_rst_rate_init (opt_inc_lbd_rst_rate_init)
  , inc_dec_rst_rate_init (opt_inc_dec_rst_rate_init)
  , inc_rst_rate_finished (true)
  , closed_lbd            (opt_closed_lbd)
  , closed_lbd_rate       (opt_closed_lbd_rate)
  , rm_simulate           (opt_rm_simulate)
  , rdb_eval              (opt_rdb_eval)
  , rdb_call              (opt_rdb_call)
  , rdb_ub                (opt_rdb_ub)
  , core_lbd_coverage     (opt_core_lbd_cvr)
  , supp_lbd_coverage     (opt_supp_lbd_cvr)
  , core_lbd_lb           (opt_core_lbd_lb)
  , supp_lbd_lb           (opt_supp_lbd_lb)
  , core_lbd_threshold    (opt_core_lbd_lb)
  , supp_lbd_threshold    (INT32_MAX)
  , core_lbd_period       (opt_core_lbd_prd)
  , supp_lbd_period       (opt_supp_lbd_prd)
  , othr_lbd_period       (opt_othr_lbd_prd)
  , inc_lrn_limit         (opt_inc_lrn_limit)
  , frozen_lbd            (opt_frozen_lbd)
  , simp_min_starts       (opt_simp_min_starts)
  , rm_low_act_learnts    (opt_rm_low_act_learnts)
  , lv0_reduce_db         (opt_lv0_reduce_db)
  , reduce_db_base        (opt_learnts_init)
  , reduce_db_inc	      (opt_learnts_inc)
  , stats_conf_size       (opt_stats_conf_size)
  , max_stats_size        (opt_max_stats_size)
  , use_minisat_param     (opt_minisat)
  , certified_output      (NULL)
  , certified_unsat       (opt_certified)
  , num_csp_vars          (0)

  , inst_type             (INS_UNDEF)
  , inst_check            (opt_inst_check)
  , small_block           (opt_small_block)
  , slow_restart_speed    (opt_slow_restart_speed)
  , slow_restart_strategy (opt_slow_restart_strategy)
  , slow_lbd_restart_rate (opt_slow_lbd_restart_rate)
  , slow_dec_restart_rate (opt_slow_dec_restart_rate)
  , slow_lbd_queue_size   (opt_slow_lbd_queue_size)
  , slow_var_decay_mode   (opt_slow_var_decay_mode)
  , slow_var_decay        (opt_slow_var_decay)
  , slow_glue_threshold   (opt_slow_glue_threshold)
  , slow_phase_saving     (opt_slow_phase_saving)
  , fast_restart_speed    (opt_fast_restart_speed)
  , fast_restart_strategy (opt_fast_restart_strategy)
  , fast_lbd_restart_rate (opt_fast_lbd_restart_rate)
  , fast_dec_restart_rate (opt_fast_dec_restart_rate)
  , fast_lbd_queue_size   (opt_fast_lbd_queue_size)
  , fast_var_decay_mode   (opt_fast_var_decay_mode)
  , fast_var_decay        (opt_fast_var_decay)
  , fast_glue_threshold   (opt_fast_glue_threshold)
  , fast_phase_saving     (opt_fast_phase_saving)

  // State data added by nabesima
  , lbd_comps             (0)
  , touch_comps           (0)
  , next_conflicts        (opt_learnts_init)
  , conflict_probing      (false)
  , pr_last_starts        (0)

  , rewrited_vars         (0)
  , rw_last_starts        (0)
  , simp_last_starts      (0)
  , elim_dec_vars         (0)
  , max_trails            (0)
  , num_progress_report   (0)
  , progress_report_base  (100)
  , progress_report_inc   (1.2)
  , next_progress_report  (progress_report_base)


    // Resource constraints:
    //
  , conflict_budget    (opt_conf_limit) // (-1)  modified by nabesima
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{
    // added by nabesima
    stat_DLVs   .init(stats_conf_size);
    stat_trails .init(stats_conf_size);
    local_LBDs  .init(lbd_queue_size);
    local_trails.init(trl_queue_size);

    if (use_minisat_param)
        setMiniSat22Params();

    if(certified_unsat) {
      if(!strcmp(opt_certified_file,"NULL")) {
        vbyte            = false;  // Cannot write binary to stdout
        certified_output = fopen("/dev/stdout", "wb");
      } else {
        certified_output = fopen(opt_certified_file, "wb");
      }

      lazy_eqv_probing = false;    // Currently, the unsat proof does not support equivalent literal detection.
    }

    lazy_simp = lazy_fld_probing || lazy_pol_probing || lazy_nec_probing || lazy_eqv_probing || lazy_cla_probing || lazy_lrn_min || lazy_uw_lit_elim || lazy_pr_lit_elim || lazy_bin_add || probed_lit_chain;
    if (use_lazy_simp) {
        lazy_simp = true;
    } else {
        lazy_simp = lazy_fld_probing = lazy_pol_probing = lazy_nec_probing
                = lazy_eqv_probing = lazy_cla_probing = lazy_lrn_min
                = lazy_uw_lit_elim = lazy_pr_lit_elim
                = lazy_bin_add = probed_lit_chain = false;
        amo     = AMO_NONE;
        amo_grp = false;
    }
    num_probed_lits.growTo(PRB_NUM_TYPES);
    num_proped_lits.growTo(PRB_NUM_TYPES);
    eq_lits.push();    // [0] is a dummy

    learnts_len       .init(max_stats_size);
    learnts_lbd       .init(max_stats_size);
    lit_blk_sizes     .init(max_stats_size);
    eq_vars_sizes     .init(max_stats_size);
    amo_sizes         .init(max_stats_size);

    // Normal strategy parameters.
    nrml_restart_strategy = restart_strategy;
    nrml_lbd_restart_rate = lbd_restart_rate;
    nrml_dec_restart_rate = dec_restart_rate;
    nrml_lbd_queue_size   = lbd_queue_size;
    nrml_var_decay_mode   = var_decay_mode;
    nrml_var_decay        = var_decay;
    nrml_glue_threshold   = core_lbd_threshold;
    nrml_phase_saving     = phase_saving;
}

Solver::~Solver()
{
}

// added by nabesima
void Solver::setMiniSat22Params() {
    // Original parameters
    var_decay       = 0.95;
    clause_decay    = 0.999;
    random_var_freq = 0;
    random_seed     = 91648253;
    luby_restart    = true;
    ccmin_mode      = 2;
    phase_saving    = 2;
    rnd_pol         = false;
    rnd_init_act    = false;
    garbage_frac    = 0.20;
    restart_first   = 100;
    restart_inc     = 2;

    // Options added by nabesima
    partial_model      = false;
    bin_propagation    = false;
    lazy_fld_probing   = false;
    lazy_pol_probing   = false;
    lazy_nec_probing   = false;
    lazy_eqv_probing   = false;
    lazy_cla_probing   = false;
    lazy_lrn_min       = false;
    lazy_uw_lit_elim   = false;
    lazy_pr_lit_elim   = false;
    lazy_bin_add       = ODA_NONE;
    probed_lit_chain   = false;
    rand_attach        = false;
    dec_elim           = false;
    amo                = AMO_NONE;
    amo_grp            = false;
    inc_var_decay      = false;
    sloped_var_decay   = false;
    uip_bumping        = false;
    lbd_act_bumping    = false;
    restart_strategy   = RST_MINISAT;
    restart_blocking   = RBK_NONE;
    inc_rst_rate       = false;
    agility_decay      = 0;
    rdb_eval           = RDB_LRU;
    rdb_ub             = 0.5;
    core_lbd_threshold     = 2;
    inc_lrn_limit      = 0;
    frozen_lbd         = 0;
    simp_min_starts    = 0;
    rm_low_act_learnts = true;
    rdb_call           = RDB_CALL_MINISAT;
    lv0_reduce_db      = false;
    inst_check         = 0;
}

// added by nabesima
void Solver::printOptions() const {
    // Original parameters
    printf("c Options:\n");
    printf("c CORE\n");
    printf("c  var_decay             = %.3f\n", var_decay);
    printf("c  clause_decay          = %.3f\n", clause_decay);
    printf("c  random_var_freq       = %.3f\n", random_var_freq);
    printf("c  random_seed           = %.3f\n", random_seed);
    printf("c  luby_restart          = %d\n",   luby_restart);
    printf("c  ccmin_mode            = %d\n",   ccmin_mode);
    printf("c  phase_saving          = %d\n",   phase_saving);
    printf("c  rnd_pol               = %d\n",   rnd_pol);
    printf("c  rnd_init_act          = %d\n",   rnd_init_act);
    printf("c  garbage_frac          = %.3f\n", garbage_frac);
    printf("c  restart_first         = %d\n",   restart_first);
    printf("c  restart_inc           = %.3f\n", restart_inc);

    // Options added by nabesima
    printf("c MODEL\n");
    printf("c  partial_model         = %d\n",   partial_model);
    printf("c PROPAGATION\n");
    printf("c  bin_propagation       = %d\n",   bin_propagation);
    printf("c SIMPLIFICATION\n");
    printf("c  lrn_min_size          = %d\n",   lrn_max_size);
    printf("c  lazy_simp             = %d\n",   lazy_simp);
    printf("c  lazy_interval         = %d\n",   lazy_interval);
    printf("c  lazy_fld_probing      = %d\n",   lazy_fld_probing);
    printf("c  lazy_pol_probing      = %d\n",   lazy_pol_probing);
    printf("c  lazy_nec_probing      = %d\n",   lazy_nec_probing);
    printf("c  lazy_eqv_probing      = %d\n",   lazy_eqv_probing);
    printf("c  lazy_cla_probing      = %d\n",   lazy_cla_probing);
    printf("c  lazy_lrn_min          = %d\n",   lazy_lrn_min);
    printf("c  lazy_uw_lit_elim      = %d\n",   lazy_uw_lit_elim);
    printf("c  lazy_pr_lit_elim      = %d\n",   lazy_pr_lit_elim);
    printf("c  lazy_bin_add          = %d\n",   lazy_bin_add);
    printf("c  probed_lit_chain      = %d\n",   probed_lit_chain);
    printf("c  pr_min_lits           = %.5f\n", pr_min_lits);
    printf("c  pr_min_starts         = %d\n",   pr_min_starts);
    printf("c  rw_min_lits           = %.3f\n", rw_min_lits);
    printf("c  rw_min_starts         = %d\n",   rw_min_starts);
    printf("c  rand_attach           = %d\n",   rand_attach);
    printf("c  dec_elim              = %d\n",   dec_elim);
    printf("c  dec_elim_lim          = %d\n",   dec_elim_lim);
    printf("c  dec_elim_len          = %d\n",   dec_elim_len);
    printf("c  amo                   = %d\n",   amo);
    printf("c  amo_grp               = %d\n",   amo_grp);
    printf("c  amo_max_bins          = %d\n",   amo_max_bins);
    printf("c  amo_starts            = %d\n",   amo_starts);
    printf("c  mace_cmd              = %s\n",   mace_cmd);
    printf("c DECISION\n");
    printf("c  rand_rebuild          = %d\n",   rand_rebuild);
    printf("c  rand_rebuild_confs    = %d\n",   rand_rebuild_confs);
    printf("c  inc_var_decay         = %d\n",   inc_var_decay);
    printf("c  inc_var_decay_period  = %d\n",   inc_var_decay_period);
    printf("c  inc_var_decay_init    = %.3f\n", inc_var_decay_init);
    printf("c  var_decay_mode        = %d\n",   var_decay_mode);
    printf("c  var_decay_gain        = %.f\n",  var_decay_gain);
    printf("c  sloped_var_decay      = %d\n",   sloped_var_decay);
    printf("c  max_var_decay         = %.3f\n", max_var_decay);
    printf("c  min_var_decay         = %.3f\n", min_var_decay);
    printf("c  min_var_decay_vars    = %d\n",   min_var_decay_vars);
    printf("c  max_var_decay_vars    = %d\n",   max_var_decay_vars);
    printf("c  uip_bumping           = %d\n",   uip_bumping);
    printf("c  lbd_act_bumping       = %d\n",   lbd_act_bumping);
    printf("c  rand_tiebreak         = %d\n",   rand_tiebreak);
    printf("c  simp_rebuild          = %d\n",   simp_rebuild);
    printf("c RESTART\n");
    printf("c  restart_strategy      = %d\n",   restart_strategy);
    printf("c  restart_blocking      = %d\n",   restart_blocking);
    printf("c  agility_decay         = %.5f\n", agility_decay);
    printf("c  lbd_restart_rate      = %.3f\n", lbd_restart_rate);
    printf("c  dec_restart_rate      = %.3f\n", dec_restart_rate);
    printf("c  blk_restart_rate      = %.3f\n", blk_restart_rate);
    printf("c  lbd_queue_size        = %d\n",   lbd_queue_size);
    printf("c  dec_queue_size        = %d\n",   dec_queue_size);
    printf("c  trl_queue_size        = %d\n",   trl_queue_size);
    printf("c  blk_restart_weight    = %.3f\n", blk_restart_weight);
    printf("c  inc_rst_rate          = %d\n",   inc_rst_rate);
    printf("c  inc_rst_rate_period   = %d\n",   inc_rst_rate_period);
    printf("c  inc_lbd_rst_rate_init = %.3f\n", inc_lbd_rst_rate_init);
    printf("c  inc_dec_rst_rate_init = %.3f\n", inc_dec_rst_rate_init);
    printf("c REDUCTION\n");
    printf("c  closed_lbd            = %d\n",   closed_lbd);
    printf("c  closed_lbd_rate       = %.3f\n", closed_lbd_rate);
    printf("c  rm_simulate           = %d\n",   rm_simulate);
    printf("c  rdb_eval              = %d\n",   rdb_eval);
    printf("c  rdb_call              = %d\n",   rdb_call);
    printf("c  rdb_ub                = %.3f\n", rdb_ub);
    printf("c  core_lbd_cvr          = %.3f\n", core_lbd_coverage);
    printf("c  supp_lbd_cvr          = %.3f\n", supp_lbd_coverage);
    printf("c  core_lbd_lb           = %d\n",   core_lbd_lb);
    printf("c  supp_lbd_lb           = %d\n",   supp_lbd_lb);
    printf("c  core_lbd_prd          = %d\n",   core_lbd_period);
    printf("c  supp_lbd_prd          = %d\n",   supp_lbd_period);
    printf("c  othr_lbd_prd          = %d\n",   othr_lbd_period);
    printf("c  inc_lrn_limit         = %d\n",   inc_lrn_limit);
    printf("c  frozen_lbd            = %d\n",   frozen_lbd);
    printf("c  simp_min_starts       = %d\n",   simp_min_starts);
    printf("c  rm_low_act_learnts    = %d\n",   rm_low_act_learnts);
    printf("c  lv0_reduce_db         = %d\n",   lv0_reduce_db);
    printf("c  reduce_db_base        = %d\n",   reduce_db_base);
    printf("c  reduce_db_inc         = %d\n",   reduce_db_inc);
    printf("c HARD\n");
    printf("c  inst_check            = %d\n",   inst_check);
    printf("c  small_block           = %.3f\n", small_block);
    printf("c  slow_restart_speed    = %.3f\n", slow_restart_speed);
    printf("c  slow_restart_strategy = %d\n",   slow_restart_strategy);
    printf("c  slow_lbd_restart_rate = %.3f\n", slow_lbd_restart_rate);
    printf("c  slow_dec_restart_rate = %.3f\n", slow_dec_restart_rate);
    printf("c  slow_lbd_queue_size   = %d\n",   slow_lbd_queue_size);
    printf("c  slow_var_decay        = %.3f\n", slow_var_decay);
    printf("c  slow_glue_threshold   = %d\n",   slow_glue_threshold);
    printf("c  slow_phase_saving     = %d\n",   slow_phase_saving);
    printf("c  fast_restart_speed    = %.3f\n", fast_restart_speed);
    printf("c  fast_restart_strategy = %d\n",   fast_restart_strategy);
    printf("c  fast_lbd_restart_rate = %.3f\n", fast_lbd_restart_rate);
    printf("c  fast_dec_restart_rate = %.3f\n", fast_dec_restart_rate);
    printf("c  fast_lbd_queue_size   = %d\n",   fast_lbd_queue_size);
    printf("c  fast_var_decay        = %.3f\n", fast_var_decay);
    printf("c  fast_glue_threshold   = %d\n",   fast_glue_threshold);
    printf("c  fast_phase_saving     = %d\n",   fast_phase_saving);
    printf("c STATS\n");
    printf("c  stats_conf_size       = %d\n",   stats_conf_size);
    printf("c  max_stats_size        = %d\n",   max_stats_size);
    printf("c SOLVER\n");
    printf("c  minisat               = %d\n",   use_minisat_param);
    fflush(stdout);
}
void Solver::printProblemStats() const {
    printf("c Problem: %d variables, %d clauses\n", nVars(), nClauses());
    fflush(stdout);
}
void Solver::printProblemStats(double parsed_time) const {
    printf("c Problem: %d variables, %d clauses, parsing %.2f s\n", nVars(), nClauses(), parsed_time);
    fflush(stdout);
}
void Solver::printStats() {
    printStats("");

    if (verbosity >= 2) {
        printf("c\n");
        printf("c [Statistics]\n");
        printf("c             learnts len        learnts lbd        lit blk size       eq vars size\n");
        printf("c  tot  %10" PRIu64 "         %10" PRIu64 "         %10" PRIu64 "         %10" PRIu64 "\n",
                learnts_len  .total(),
                learnts_lbd  .total(),
                lit_blk_sizes.total(),
                eq_vars_sizes.total());
        printf("c  avg  %10.3f         %10.3f         %10.3f         %10.3f\n",
                learnts_len  .avg(),
                learnts_lbd  .avg(),
                lit_blk_sizes.avg(),
                eq_vars_sizes.avg());
        for (int i=1; i <= max_stats_size; i++)
            printf("c  %2d   %10" PRIu64 " (%4.1f%%) %10" PRIu64 " (%4.1f%%) %10" PRIu64 " (%4.1f%%) %10" PRIu64 " (%4.1f%%)\n", i,
                    learnts_len  .get(i), learnts_len  .rate(i) * 100,
                    learnts_lbd  .get(i), learnts_lbd  .rate(i) * 100,
                    lit_blk_sizes.get(i), lit_blk_sizes.rate(i) * 100,
                    eq_vars_sizes.get(i), eq_vars_sizes.rate(i) * 100);
        printf("c\n");

        for (int i=0; i < learnts.size(); i++) {
            const Clause& c = ca[learnts[i]];
            if (c.used()) used_clause_lbd.inc(c.lbd());
            else          unused_clause_lbd.inc(c.lbd());
        }

        printf("c [LBD Statistics]\n");
        printf("c LBD          used lbd               used clause lbd         unused clause lbd\n");
        printf("c  tot   %10" PRIu64 "              %10" PRIu64 "              %10" PRIu64 "\n",
                used_lbd .total(),
                used_clause_lbd  .total(),
                unused_clause_lbd.total());
        printf("c  avg   %10.3f              %10.3f              %10.3f\n",
                used_lbd .avg(),
                used_clause_lbd  .avg(),
                unused_clause_lbd.avg());
        int max = used_lbd.size();
        max = std::max(max, used_clause_lbd.size());
        max = std::max(max, unused_clause_lbd.size());
        for (int i=1; i < max; i++)
            printf("c  %3d   %10" PRIu64 " (%4.1f/%4.1f%%) %10" PRIu64 " (%4.1f/%4.1f%%) %10" PRIu64 " (%4.1f/%4.1f%%)\n",
                    i,
                    used_lbd .get(i), used_lbd .rate(i), used_lbd .trate(i),
                    used_clause_lbd  .get(i), used_clause_lbd  .rate(i), used_clause_lbd  .trate(i),
                    unused_clause_lbd.get(i), unused_clause_lbd.rate(i), unused_clause_lbd.trate(i));
        printf("c\n");

        if (rm_simulate) {
            int used_learnts = 0;
            for (int i=0; i < learnts.size(); i++) {
                Clause &c = ca[learnts[i]];
                assert(c.removed() == false);
                if (c.used()) used_learnts++;
            }
            int used_rm_learnts = 0;
            for (int i=0; i < rm_learnts.size(); i++) {
                Clause &c = ca[rm_learnts[i]];
                assert(c.removed());
                if (c.rm_used()) used_rm_learnts++;
            }
            uint64_t used = propagations + conflicts;
            uint64_t used_by_holdings = propagations + conflicts - rm_propagations - rm_conflicts;

            printf("c [RDB Statistics]\n");
            printf("c rdb true pos   : %d\n", used_learnts);
            printf("c rdb false pos  : %d\n", learnts.size() - used_learnts);
            printf("c rdb true neg   : %d\n", rm_learnts.size() - used_rm_learnts);
            printf("c rdb false neg  : %d\n", used_rm_learnts);
            printf("c rdb precision  : %6.3f%% (%11d / %11d)\n", 100.0 * used_learnts / learnts.size(), used_learnts, learnts.size());
            printf("c rdb recall     : %6.3f%% (%11d / %11d)\n", 100.0 * used_learnts / (used_learnts + used_rm_learnts), used_learnts, used_learnts + used_rm_learnts);
            printf("c rdb neg pred   : %6.3f%% (%11d / %11d)\n", 100.0 * (rm_learnts.size() - used_rm_learnts) / (rm_learnts.size()), rm_learnts.size() - used_rm_learnts, rm_learnts.size());
            printf("c rdb coverage   : %6.3f%% (%11" PRIu64 " / %11" PRIu64 ")\n", 100.0 * used_by_holdings / used, used_by_holdings, used);
            printf("c rdb cvr props  : %6.3f%% (%11" PRIu64 " / %11" PRIu64 ")\n", 100.0 * (propagations - rm_propagations) / propagations, propagations - rm_propagations, propagations);
            printf("c rdb cvr confs  : %6.3f%% (%11" PRIu64 " / %11" PRIu64 ")\n", 100.0 * (conflicts    - rm_conflicts   ) / conflicts   , conflicts    - rm_conflicts   , conflicts   );
            printf("c props / lrnt   : %10.3f holding, %10.3f removed\n", (double)(propagations - rm_propagations) / learnts.size(), (double)rm_propagations / rm_learnts.size());
            printf("c confs / lrnt   : %10.3f holding, %10.3f removed\n", (double)(conflicts    - rm_conflicts   ) / learnts.size(), (double)rm_conflicts    / rm_learnts.size());
            printf("c props / u-lrnt : %10.3f holding, %10.3f removed\n", (double)(propagations - rm_propagations) / used_learnts  , (double)rm_propagations / used_rm_learnts);
            printf("c confs / u-lrnt : %10.3f holding, %10.3f removed\n", (double)(conflicts    - rm_conflicts   ) / used_learnts  , (double)rm_conflicts    / used_rm_learnts);
            printf("c\n");
        }
    }

    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    if (mem_used != 0)
        printf("c Memory used       : %.2f MB\n", mem_used);
    printf("c CPU time          : %.3f s\n", cpu_time);
    printf("c Real time         : %.3f s\n", realTime() - real_stime);
}
void Solver::printStats(const char *prefix) const {
    double cpu_time = cpuTime();

    uint32_t probed_vars = 0;
    uint32_t proped_vars = 0;
    for (int i=0; i < PRB_NUM_TYPES; i++) {
        probed_vars += num_probed_lits[i];
        proped_vars += num_proped_lits[i];
    }

    printf("c\n");
    printf("c%s variables         : %-11d (init %d, after simp %d, %d non-decs, %d csp)\n", prefix, nFreeVars(), init_vars, simp_vars, elim_dec_vars, num_csp_vars);
    printf("c%s clauses           : %-11d (init %d, after simp %d)\n", prefix, nClauses(), init_clauses, simp_clauses);
    printf("c%s restarts          : %-11" PRIu64 " (%.2f confs/res, %" PRIu64 "~%" PRIu64 " confs, %" PRIu64 " blks, %" PRIu64 " last)\n", prefix, starts - 1, (double)conflicts / starts, min_confs, max_confs, blocked_restarts, last_blocked);
    printf("c%s conflicts         : %-11" PRIu64 " (%.0f /sec, %4.2f%% dconfs, %4.2f%% supp, trail %.2fw x %.2fh, jmp %.2fh)\n", prefix, conflicts, conflicts / cpu_time, 100.0 * dec_confs / conflicts, 100.0 * supp_backjumps / conflicts, global_width / conflicts, (double)global_DLVs / conflicts, (double)backjump_dist / conflicts);
    printf("c%s decisions         : %-11" PRIu64 " (%.4f vdcy, %.0f /sec, %4.2f%% bin, rs %.3f s)\n", prefix, decisions, var_decay, decisions / cpu_time, 100.0 * bin_decisions / decisions, rescale_time);
    printf("c%s propagations      : %-11" PRIu64 " (%.0f /sec, %4.2f lits/dec, %4.2f%% o.a.)\n", prefix, propagations, propagations/cpu_time, (float)propagations / decisions, 100.0 * oa_propagations / propagations);
    printf("c%s conflict literals : %-11" PRIu64 " (%4.2f%% deleted; %4.2f%% by bin min, %.3f s)\n", prefix, tot_literals, (double)rec_rm_lrn_lits * 100 / tot_literals, (double)bin_rm_lrn_lits * 100 / tot_literals, bin_min_time);
    printf("c%s len               : %-11.3f (%4.2f for all, max %d, used %d)\n", prefix, (double)learnts_literals / nLearnts(), (double)global_lits / conflicts, max_len_learnt, max_len_used_learnt);
    printf("c%s lbd               : %-11.3f (%4.2f (%4.2f) for all, max %d, used %d, %4.3f stdev, %.3f blk)\n", prefix, (double)tot_lbds / nLearnts(), (double)global_LBDs / conflicts, (double)(global_LBDs - reduced_LBDs) / conflicts, max_lbd_learnt, max_lbd_used_learnt, used_lbd.stdev(), ((double)global_lits / conflicts) / ((double)global_LBDs / conflicts));
    printf("c%s amo               : %-11" PRIu64 " (%d max, %.3f avg, %.3f s)\n", prefix, amo_sizes.total(), amo_sizes.max(), amo_sizes.avg(), amo_time);
    //printf("c%s depth             : %-11d (%" PRIu64 " necks, %" PRIu64 " prsv)\n", prefix, max_lrn_depth, neck_cands, neck_preserved);
    printf("c%s simp dbs          : %-11d (%.3f s)\n", prefix, simp_dbs, simplify_time);
    printf("c%s reduce dbs        : %-11d (core-lbd %d, supp-lbd %d, %.3f s)\n", prefix, reduce_dbs, core_lbd_threshold, supp_lbd_threshold, reduce_time);
    printf("c%s learnts           : %-11d (%" PRIu64 " learnts removed, %4.2f%%)\n", prefix, learnts.size(), removed_learnts, removed_learnts * 100 / (double)conflicts);
    printf("c%s rewrite dbs       : %-11d (%d/%d vars, %" PRIu64 "+%" PRIu64 " taut, %" PRIu64 "+%" PRIu64 " unit, %.3f s)\n", prefix, rewrite_dbs, rewrited_vars, eq_vars, rw_taut_clauses, rw_taut_learnts, rw_unit_clauses, rw_unit_learnts, rewrite_time);
    printf("c%s assigned lits     : %-11d (%d/%d probed, %d remains)\n", prefix, assign_probed_lits, proped_vars, probed_vars, probed_lits_queue.size());
    printf("c%s premise updates   : %-11" PRIu64 " (%4.2f /lit)\n", prefix, premise_updates, (double)premise_updates / simp_vars / 2);
    printf("c%s probed variables  : %-11d (%d pr, %d eq, %d fld, %d pol, %d nec, %d cla, %d amo)\n", prefix, probed_vars, num_probed_lits[PRB_PREMISE_CHAIN], num_probed_lits[PRB_EQV_CHAIN], num_probed_lits[PRB_FAILED_LIT], num_probed_lits[PRB_POLALITY], num_probed_lits[PRB_NECESSARY], num_probed_lits[PRB_CLAUSE], num_probed_lits[PRB_AMO]);
    printf("c%s equiv variables   : %-11d (%" PRIu64 " bin, %" PRIu64 " trn, %" PRIu64 " quat, %" PRIu64 " quin, %" PRIu64 " othr; %d amo)\n", prefix, eq_vars, eq_vars_sizes.get(2), eq_vars_sizes.get(3), eq_vars_sizes.get(4),  eq_vars_sizes.get(5), eq_vars_sizes.total() - eq_vars_sizes.get(2) - eq_vars_sizes.get(3) - eq_vars_sizes.get(4) - eq_vars_sizes.get(5), eq_amo_vars);
    printf("c%s lazy added bins   : %-11d (%d prop + %d conf, %.3fs)\n", prefix, lazy_add_prop_bins + lazy_add_conf_bins, lazy_add_prop_bins, lazy_add_conf_bins, lazy_bin_add_time);
    printf("c%s unwatched lit elim: %-11" PRIu64 " (%4.2f+%4.2f%%, %" PRIu64 "+%" PRIu64 " of %" PRIu64 "+%" PRIu64 ")\n", prefix, lazy_rm_uw_cla_lits + lazy_rm_uw_lrn_lits, (double)lazy_rm_uw_cla_lits * 100 / simp_clauses_literals, (double)lazy_rm_uw_lrn_lits * 100 / tot_literals, lazy_rm_uw_cla_lits, lazy_rm_uw_lrn_lits, simp_clauses_literals, tot_literals);
    //printf("c%s probed lit elim   : %-11" PRIu64 " (%4.2f+%4.2f%%, %" PRIu64 "+%" PRIu64 " of %" PRIu64 "+%" PRIu64 ")\n", prefix, lazy_rm_pr_cla_lits + lazy_rm_pr_lrn_lits, (double)lazy_rm_pr_cla_lits * 100 / simp_clauses_literals, (double)lazy_rm_pr_lrn_lits * 100 / tot_literals, lazy_rm_pr_cla_lits, lazy_rm_pr_lrn_lits, simp_clauses_literals, tot_literals);
    //printf("c%s literal dropping  : %-11" PRIu64 " (%4.2f+%4.2f%%, %" PRIu64 "+%" PRIu64 " of %" PRIu64 "+%" PRIu64 ")\n", prefix, lazy_lit_droppings, (double)lazy_drp_cla_lits * 100 / simp_clauses_literals, (double)lazy_drp_lrn_lits * 100 / tot_literals, lazy_drp_cla_lits, lazy_drp_lrn_lits, simp_clauses_literals, tot_literals);
    //printf("c%s subsumed clauses  : %-11d (%4.2f + %4.2f%% of %d + %" PRIu64 ")\n", prefix, subsumed_clauses + subsumed_learnts, (double)subsumed_clauses * 100 / simp_clauses, (double)subsumed_learnts * 100 / conflicts, simp_clauses, conflicts);
    printf("c%s classified type   : %s\n", prefix, inst_types[inst_type]);
    printf("c%s progress          : %-6.3f%%\n", prefix, progressEstimate()*100);
    //printf("c%s partial model     : %-11d (%4.2f%%, %d removed)\n", prefix, init_vars - shrinked_assignments, (double)(init_vars - shrinked_assignments) * 100 / init_vars, shrinked_assignments);
}
void Solver::printProgressHeader() const {
    printf("c\n");
    printf("c        #Rstrts   #Confs   #Vars   #Clauses  #Learnts Lits/C LBD/C DLVs Trail\n");
    printf("c\n");
}
void Solver::printProgress(const char sign) {
    if (num_progress_report == 0) {
        if (starts > 0)
            printStats("  ");
        printProgressHeader();
    }
    if (++num_progress_report > 15 && verbosity >= 2) num_progress_report = 0;
    printf("c%5d %c %7d %9d %8d %8d %8d %6.1f %5.1f %5.1f %4.1f%%\n",
            (int)(realTime() - real_stime), sign,
            (int)starts, (int)conflicts, nFreeVars(), nClauses(), nLearnts(),
            (double)learnts_literals/nLearnts(), (double)tot_lbds/nLearnts(),
            stat_DLVs.average(), stat_trails.average() * 100 / nVars());
    fflush(stdout);
}
//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    // added by nabesima
    if (bin_propagation) {
        bin_watches.init(mkLit(v, false));
        bin_watches.init(mkLit(v, true ));
    }
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);

    // added by nabesima
    lbd_time.push(0);
    touch_time.push(0);
    touch_time.push(0);
    assigned_lits.push(0);
    assigned_lits.push(0);
    if (closed_lbd)
        min_lbd.push(0);
    white_nodes.push(0);
    if (lazy_lrn_min) {
        simp_seen.push(0);
        simp_seen.push(0);
        simp_reached.push(0);
        simp_reached.push(0);
    }
    if (lazy_simp) {
        premises.push(mkLit(v, false));
        premises.push(mkLit(v, true ));
        lit2eq_lits.push(NO_EQ_LITS);
        lit2eq_lits.push(NO_EQ_LITS);
        rewrited.push(false);
        if (certified_unsat) {
            bin_sets.push();
            bin_sets.push();
        }
    }
    if (amo) {
        amo_id.push(at_most_one.size());
        at_most_one.push();
        at_most_one.last().push(mkLit(v, false));
        amo_id.push(at_most_one.size());
        at_most_one.push();
        at_most_one.last().push(mkLit(v, true ));
    }
    probed_vals.push(l_Undef);
    probed_types.push(PRB_NONE);

    sat2csp.push(var_Undef);
    pos_oa .push(CRef_Undef);
    neg_oa .push(CRef_Undef);

    return v;
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // added by nabesima
    if (lazy_eqv_probing && eq_vars > 0) {
        for (int i=0; i < ps.size(); i++)
            if (rewrited[var(ps[i])])
                ps[i] = getDelegate(ps[i]);
    }

    // added by nabesima
    if (certified_unsat) tmp_lits.clear();

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++) {
        if (certified_unsat) tmp_lits.push(ps[i]);    // added by nabesima
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    }
    ps.shrink(i - j);

    // added by nabesima
    if (dec_elim) {
        int non_dec_vars = 0;
        for (int i=0; i < ps.size(); i++) {
            if (!decision[var(ps[i])]) {
                non_dec_vars++;
                if (non_dec_vars > 1) {
                    setDecisionVar(var(ps[i]), true);
                    elim_dec_vars--;
                }
            }
        }
    }
    // added by nabesima
    if (certified_unsat && tmp_lits.size() != ps.size()) {
        writeLits(ps);
        writeDeletedLits(tmp_lits);
    }

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        unit_clauses++;    // added by nabesima
        uncheckedEnqueue(ps[0]);

        if (verify_model) org_clauses.push(ca.alloc(ps, false));

        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);

        if (verify_model) org_clauses.push(ca.alloc(ps, false));
    }

    return true;
}

// added by nabesima
void Solver::addOrderAxiomDef(Var from, Var to) {
    csp_lb.push(from);
    csp_ub.push(to);
    num_csp_vars++;
}

bool Solver::generateOrderAxioms() {
    assert(decisionLevel() == 0);
    for (int i=0; i < num_csp_vars; i++) {
        int from = csp_lb[i];
        int to   = csp_ub[i];
        assert(from < to);
        while (value(from) == l_True && from <= to)
            from++;
        while (value(to) == l_False && to >= from)
            to--;
//        if (from != csp_lb[i] || to != csp_ub[i]) {
//            printf("CSP Var %d domain %d - %d (%d) => %d - %d (%d) \n", i, csp_lb[i], csp_ub[i], csp_ub[i] - csp_lb[i], from, to, to - from);
//        }
        csp_lb[i] = from;
        csp_ub[i] = to;
        if (from < to) {
            for (Var v = from; v <= to; v++)
                sat2csp[v] = i;
            for (Var v = from; v <  to; v++) {
                add_tmp.clear();
                add_tmp.push( mkLit(v  ));
                add_tmp.push(~mkLit(v+1));
                CRef cr = ca.alloc(add_tmp);
                ca[cr].order_axiom(true);

                assert(pos_oa[v] == CRef_Undef);
                assert(0 <= v && v < pos_oa.size());
                pos_oa[v] = cr;

                assert(neg_oa[v+1] == CRef_Undef);
                assert(0 <= v+1 && v+1 < neg_oa.size());
                neg_oa[v+1] = cr;
            }
        }
    }
    return true;
}

// added by nabesima
double Solver::varNthActivity(double rate) const {
    assert(0 <= rate && rate <= 1.0);
    vec<double> as(order_heap.size());
    int i = 0, j = 0;
    while (i < order_heap.size()) {
        double a = activity[order_heap[i++]];
        //if (a > 0)
            as[j++] = a;
    }
    as.shrink(i - j);

    return select(as, as.size() * rate, GreaterThan_default<double>());
}

void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    // modified by nabesima
    //watches[~c[0]].push(Watcher(cr, c[1]));
    //watches[~c[1]].push(Watcher(cr, c[0]));
    if(bin_propagation && c.size() == 2) {
        bin_watches[~c[0]].push(Watcher(cr, c[1]));
        bin_watches[~c[1]].push(Watcher(cr, c[0]));
    }
    else {
        watches[~c[0]].push(Watcher(cr, c[1]));
        watches[~c[1]].push(Watcher(cr, c[0]));
    }
    // modified by nabesima
    //if (c.learnt()) learnts_literals += c.size();
    //else            clauses_literals += c.size();
    if (c.learnt()) { learnts_literals += c.size(); tot_lbds += c.lbd(); }
    else            { clauses_literals += c.size(); }
}

// added by nabesima
void Solver::attachAllClauses() {
    if (rand_attach) {
        shuffle(clauses, random_seed);
        shuffle(learnts, random_seed);
        if (rm_simulate) shuffle(rm_learnts, random_seed);
    }
    for (int i=0; i < learnts.size(); i++)
        attachClause(learnts[i]);
    if (rm_simulate)
        for (int i=0; i < rm_learnts.size(); i++)
            attachClause(rm_learnts[i]);
    for (int i=0; i < clauses.size(); i++)
        attachClause(clauses[i]);
}

void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);

    // modified by nabesima
//    if (strict){
//        remove(watches[~c[0]], Watcher(cr, c[1]));
//        remove(watches[~c[1]], Watcher(cr, c[0]));
//    }else{
//        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
//        watches.smudge(~c[0]);
//        watches.smudge(~c[1]);
//    }
    if (bin_propagation && c.size() == 2) {
        if (strict){
            remove(bin_watches[~c[0]], Watcher(cr, c[1]));
            remove(bin_watches[~c[1]], Watcher(cr, c[0]));
        }else{
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            bin_watches.smudge(~c[0]);
            bin_watches.smudge(~c[1]);
        }
    }
    else {
        if (strict){
            remove(watches[~c[0]], Watcher(cr, c[1]));
            remove(watches[~c[1]], Watcher(cr, c[0]));
        }else{
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge(~c[0]);
            watches.smudge(~c[1]);
        }
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size();

    // added by nabesima
    if (c.learnt()) tot_lbds -= c.lbd();
}

// added by nabesima
void Solver::detachAllClauses() {
    for (int i=0; i < nVars(); i++) {
        if (bin_propagation) {
            bin_watches[mkLit(i, false)].clear();
            bin_watches[mkLit(i, true )].clear();
        }
        watches[mkLit(i, false)].clear();
        watches[mkLit(i, true )].clear();
    }
    learnts_literals = 0;
    clauses_literals = 0;
    tot_lbds = 0;
}

void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];

    assert(!c.order_axiom());

    // added by nabesima
    if (certified_unsat) writeDeletedClause(c);

    // added by nabesima
    if ((rdb_eval >= RDB_LBD_CVR || verbosity >= 2) && c.learnt()) {
        if (c.used()) used_clause_lbd.inc(c.lbd());
        else          unused_clause_lbd.inc(c.lbd());
    }

    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}
// added by nabesima
void Solver::removeClauseNoDetach(CRef cr) {
    Clause& c = ca[cr];

    // added by nabesima
    if (certified_unsat) writeDeletedClause(c);

    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}
bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level, bool restart) {
    bool do_lazy_simp = lazy_simp && (starts % lazy_interval == 0);
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            // modified by nabesima
            //Var      x  = var(trail[c]);
            Lit      p  = trail[c];
            Var      x  = var(p);
            assigns [x] = l_Undef;
            // modified by nabesima
            //if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
            //    polarity[x] = sign(trail[c]);
            if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last())) {
                char new_pol = (phase_saving == 3 && c >= trail_lim.last() && !restart) ? sign(~p) : sign(p);
                if (polarity[x] != new_pol) agility += (1 - agility_decay);
                polarity[x] = new_pol;
            }
            insertVarOrder(x);
            // added by nabesima
            if (do_lazy_simp) {
                Lit q = premise(x);
                if (p != q)
                    lazyProbing(q, p);
            }
            if (lazy_simp && !certified_unsat && premise(x) != p && premise(x) != premises[toInt(p)]) {  // The condition "!certified_unsat" is to reduce the proof size.
                assert(premise(x) != lit_Undef);
                premises[toInt(p)] = premise(x);
                if (certified_unsat) writeUniqBin(~premise(x), p);
            }
            // added by nabesima
            agility *= agility_decay;
            white_nodes[x] = 0;
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    }
}


//=================================================================================================
// Major methods:

Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // modified by nabesima
    if (!rand_tiebreak) {
        // Activity based decision:
        while (next == var_Undef || value(next) != l_Undef || !decision[next]) {
            if (order_heap.empty()){
                next = var_Undef;
                break;
            }else
                next = order_heap.removeMin();
        }
    }
    else {
        vec<Var> mins;
        while (true) {
            Var cand = var_Undef;
            while (cand == var_Undef || value(cand) != l_Undef || !decision[cand]) {
                if (order_heap.empty()){
                    cand = var_Undef;
                    break;
                }else
                    cand = order_heap.removeMin();
            }
            if (cand == var_Undef) break;
            mins.push(cand);
            if (order_heap.empty()) break;
            if (activity[cand] != activity[order_heap.min()]) break;
            if (drand(random_seed) < 0.5) break;
        }
        if (next == var_Undef && mins.size() > 0) {
            next = mins.last();
            mins.pop();
        }
        for (int i=0; i < mins.size(); i++)
            insertVarOrder(mins[i]);

    }

    // modified by nabesima
    //return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);

    // added by nabesima
    Lit selected = lit_Undef;
    if (next != var_Undef && probedValue(next) != l_Undef)
        selected = mkLit(next, probedValue(next) == l_True ? false : true);

    // added by nabesima
    if (next != var_Undef && selected == lit_Undef)
        selected = mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);

    // added by nabesima
    if (oa_bin_dec && next != var_Undef && sat2csp[next] != var_Undef) {
        Var csp_v  = sat2csp[next];
        Var sat_lb = csp_lb[csp_v];
        Var sat_ub = csp_ub[csp_v];
        if (oa_bin_dec_lb <= sat_ub - sat_lb + 1) {
            Var cur_lb = find_oa_lb(sat_lb, sat_ub);
            Var cur_ub = find_oa_ub(sat_lb, sat_ub);
            assert(sat_lb <= cur_lb && cur_lb <= cur_ub);
            assert(sat_lb <= cur_ub && cur_ub <= cur_ub);
            if (oa_bin_dec_lb <= cur_ub - cur_lb + 1) {
                Var med = (cur_ub + cur_lb) / 2;
                assert(value(med) == l_Undef);
                selected = mkLit(med, polarity[next]);
                //printf("selected %d instead of %d/%d\n", med - sat_lb, next - sat_lb, sat_ub - sat_lb + 1);
                bin_decisions++;
            }
        }
    }

    return selected;
}

int Solver::find_oa_lb(int lb, int ub) {
    int l = lb;
    int r = ub;
    while (l < r) {
        Var med = (l + r) / 2;
        if (value(med) == l_Undef && (med - 1 == lb || value(med-1) == l_True)) return med;
        else if (value(med) == l_True) l = med+1;
        else r = med-1;
    }
    return l;
}
int Solver::find_oa_ub(int lb, int ub) {
    int l = lb;
    int r = ub;
    while (l < r) {
        Var med = (l + r) / 2;
        if (value(med) == l_Undef && (med + 1 == ub || value(med+1) == l_False)) return med;
        else if (value(med) == l_False) r = med-1;
        else l = med+1;
    }
    return r;
}

/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
|        rest of literals. There may be others from the same level though.
|
|________________________________________________________________________________________________@*/
// modified by nabesima
//void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // added by nabesima
    int reason_nodes = 0;
    if (lbd_act_bumping) implied_by_learnts.clear();
    if (dec_elim) non_dec_vars.clear();

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    bool dec_learnt = false;

    //printf("-------------------------------------------------\n");

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

//        printf("pathC = %d, confl = ", pathC); printClause(c);
//        fflush(stdout);

        // The first literal must be true in binary clauses.
        if (bin_propagation && p != lit_Undef && c.size() == 2 && value(c[1]) == l_True) {
          assert(value(c[1]) == l_True);
          assert(p == c[1]);
          c[1] = c[0];
          c[0] = p;
        }
        assert(p == lit_Undef || value(c[0]) == l_True);

        if (c.learnt())
            claBumpActivity(c);

        // added by nabesima
        if (lazy_lit_dropping && c.size() > 2 && implies(~c[0], c[1])) {
            int n = c.size() - 2;
            c.shrink(n);
            c.learnt() ? lazy_drp_lrn_lits += n : lazy_drp_cla_lits += n;
            lazy_lit_droppings++;
        }

        // added by nabesima
        if (c.learnt() && c.lbd() > 2) {
            int lbd = getLBD(c);
            // Update?
            if (lbd <= c.lbd()) {
                tot_lbds = tot_lbds - c.lbd() + lbd;
                reduced_LBDs += c.lbd() - lbd;
                if (verbosity) {
                    learnts_lbd.dec(c.lbd());
                    learnts_lbd.inc(lbd);
                }
                if (rdb_eval == RDB_LBD) {
                    if (lbd <= frozen_lbd)
                        c.ttl(1);
                }
                else if (rdb_eval == RDB_LBD_CVR) {
                    if (core_lbd_period && lbd <= core_lbd_threshold && core_lbd_threshold < c.lbd())
                        c.ttl(core_lbd_period);
//                    else if (supp_lbd_period && lbd <= supp_lbd_threshold && supp_lbd_threshold < c.lbd())
//                        c.ttl(supp_lbd_period);
                }
                c.lbd(lbd);

                if (dec_elim && lbd == 2) {
                    for (int i=0; i < c.size(); i++) {
                        if (!decision[var(c[i])]) {
                            setDecisionVar(var(c[i]), true);
                            elim_dec_vars--;
                        }
                    }
                }
            }
        }
        if (closed_lbd && c.learnt() && p != lit_Undef) {
//            if (c.lbd() > min_lbd[var(c[0])]) {
//                int new_lbd = (int)((1.0 - closed_lbd_rate) * c.lbd() + closed_lbd_rate * min_lbd[var(c[0])]);
//                //printf("c lbd update (%d, %d) -> %d\n", c.lbd(), min_lbd[var(c[0])], new_lbd);
//                if (rdb_eval == RDB_LBD_CVR) {
//                    if (core_lbd_period && new_lbd <= core_lbd_threshold && core_lbd_threshold < c.lbd())
//                        c.ttl(core_lbd_period);
//                    else if (supp_lbd_period && new_lbd <= supp_lbd_threshold && supp_lbd_threshold < c.lbd())
//                        c.ttl(supp_lbd_period);
//                }
//                c.lbd(new_lbd);
//            }
            if (min_lbd[var(c[0])] <= core_lbd_threshold && c.ttl() == 0)
                c.ttl(1);
        }

        // added by nabesima
        Lit comm = lazy_simp ? ~premises[toInt(~c[0])] : lit_Error;
        Lit antr = lit_Error;
        int aidx = 0;
        int paid = amo ? amo_id[toInt(c[0])] : NO_AMO;    // positive amo id
        Lit nglt = lit_Undef;
        // modified by nabesima
        //for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); ) {
            Lit q = c[j];

            // added by nabesima
            if (lazy_uw_lit_elim && j > 1 && (implies(q, c[0]) || implies(q, c[1]))) {
                if (certified_unsat) c.copyTo(tmp_lits);
                c[j] = c.last();
                c.shrink(1);
                c.learnt() ? lazy_rm_uw_lrn_lits++ : lazy_rm_uw_cla_lits++;
                if (certified_unsat) { writeClause(c); writeDeletedLits(tmp_lits); }
                continue;
            }
            if (lazy_pr_lit_elim && j > 1 && probedValue(q) == l_False) {
                if (certified_unsat) c.copyTo(tmp_lits);
                c[j] = c.last();
                c.shrink(1);
                c.learnt() ? lazy_rm_pr_lrn_lits++ : lazy_rm_pr_cla_lits++;
                if (certified_unsat) { writeClause(c); writeDeletedLits(tmp_lits); }
                continue;
            }
            if (lazy_cla_probing && comm != lit_Error && probedValue(q) != l_False) {
                Lit r = ~getCommonPremise(~q, ~comm);
                if (r != lit_Error)
                    comm = r;
                else if (antr == lit_Error) {   // r == lit_Error
                    if (implies(q, ~comm))
                        antr = ~comm;
                    else
                        antr = ~premises[toInt(~q)];
                    aidx = j;
                }
                else
                    comm = antr = lit_Error;
            }
            if (amo && paid != NO_AMO) {
                if (amo_id[toInt(q)] != paid) {
                    if (amo_id[toInt(~q)] == paid && nglt == lit_Undef)
                        nglt = q;
                    else
                        paid = NO_AMO;
                }
            }

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;

                // modified by nabesima
                if (level(var(q)) >= decisionLevel()) {
                    pathC++;
                    // added by nabesima
                    reason_nodes++;
                    assert(white_nodes[var(q)] == 0);
                    white_nodes[var(q)] = 1;
                    if(lbd_act_bumping && reason(var(q)) != CRef_Undef && ca[reason(var(q))].learnt())
                        implied_by_learnts.push(q);
                }
                else {
                    out_learnt.push(q);
                    // added by nabesima
                    if (!decision[var(q)])
                        non_dec_vars.push(var(q));
                }
            }

            // added by nabesima
            if (closed_lbd && c.learnt()) {
                int min = std::min(min_lbd[var(q)], c.lbd());
                min_lbd[var(q)] = std::max(2, min);
            }

            // added by nabesima
            j++;
        }

        // added by nabesima
        if (lazy_cla_probing && comm != lit_Error && antr == lit_Error)
            addProbedLit(comm, PRB_CLAUSE);
        if (lazy_cla_probing && comm != lit_Error && antr != lit_Error) {
            if (comm == ~antr) {
                if (lazy_eqv_probing) {
                    putEquivLit(antr, c[aidx]);
                    if (c.size() == 2) {
                        assert(aidx == 1);
                        putEquivLit(~antr, c[0]);
                    }
                }
            }
        }
        if (amo && paid != NO_AMO) {
            if (nglt == lit_Undef && at_most_one[paid].size() > c.size()) {
                incTouchComps();
                for (int i=0; i < c.size(); i++)
                    touch_time[toInt(c[i])] = touch_comps;
                vec<Lit>& ps = at_most_one[paid];
                for (int i=0; i < ps.size(); i++)
                    if (touch_time[toInt(ps[i])] != touch_comps)
                        addProbedLit(~ps[i], PRB_AMO);
            }
            else if (nglt != lit_Undef)
                addProbedLit(nglt, PRB_AMO);
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    if (dec_learnt) {
        //printf("%" PRIu64 ": UIP = ", conflicts); printLit(p); printf(", lbd/len = %d/%d, blv = %d\n", getLBD(out_learnt), out_learnt.size(), getBacktrackLv(out_learnt));
        supp_backjumps++;
    }


    // added by nabesima
    if (uip_bumping) varBumpActivity(var(p));

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    tot_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    rec_rm_lrn_lits += i - j;

    // added by nabesima
    if (lazy_lrn_min)
        minimizeByPremises(out_learnt);

    // Find correct backtrack level:
    // modified by nabesima
    out_btlevel = getBacktrackLv(out_learnt);
//    if (out_learnt.size() == 1)
//        out_btlevel = 0;
//    else{
//        int max_i = 1;
//        // Find the first literal assigned at the next-highest level:
//        for (int i = 2; i < out_learnt.size(); i++)
//            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
//                max_i = i;
//        // Swap-in this literal at index 1:
//        Lit p             = out_learnt[max_i];
//        out_learnt[max_i] = out_learnt[1];
//        out_learnt[1]     = p;
//        out_btlevel       = level(var(p));
//    }

    // added by nabesima
    out_lbd = getLBD(out_learnt);
    if (lbd_act_bumping && implied_by_learnts.size() > 0) {
        for(int i=0; i < implied_by_learnts.size(); i++) {
            Var v = var(implied_by_learnts[i]);
            int v_lbd = ca[reason(v)].lbd();
            if (v_lbd < out_lbd)
                varBumpActivity(v, var_inc);
        }
        implied_by_learnts.clear();
    }
    if (dec_elim) {
        while (non_dec_vars.size() > 0) {
            Var v = non_dec_vars.last();
            non_dec_vars.pop();
            assert(reason(v) != CRef_Undef);
            Clause& c = ca[reason(v)];
            for (int i=1; i < c.size(); i++) {
                Var w = var(c[i]);
                if (decision[w])
                    varBumpActivity(w);
                else
                    non_dec_vars.push(w);
            }
        }
    }

    // Each learnt should have at most one non-decision variable. added by nabesima
    if (dec_elim) {
        int non_dec_vars = 0;
        for (int i=0; i < out_learnt.size(); i++) {
            if (!decision[var(out_learnt[i])]) {
                non_dec_vars++;
                if (non_dec_vars > 1) {
                    setDecisionVar(var(out_learnt[i]), true);
                    elim_dec_vars--;
                }
            }
        }
        //if (non_dec_vars > 1)
        //    printf("%d/%d\n", non_dec_vars, out_learnt.size());//printLits(out_learnt), printf("\n");
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

    // added by nabesima
    if (verbosity >= 2) {
        black_nodes.clear();
        for (int i=0; i < out_learnt.size(); i++) {
            Lit p  = out_learnt[i];
            int lv = level(var(p));
            if (black_nodes.size() <= lv)
                black_nodes.growTo(lv + 1);
            black_nodes[lv].push(p);
        }
        for (int i=0; i < black_nodes.size(); i++)
            if (black_nodes[i].size() > 0)
                lit_blk_sizes.inc(black_nodes[i].size());
        black_nodes.clear();
    }
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
// seen[v] == 1 if a var is contained in out_learnt and not uip. (added by nabesima)
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        // The first literal must be true in binary clauses.
        if (bin_propagation && c.size() == 2 && value(c[1]) == l_True) {
          Lit tmp = c[0];
          c[0] =  c[1], c[1] = tmp;
        }
        // added by nabesima
        if (lazy_lit_dropping && c.size() > 2 && implies(~c[0], c[1])) {
            int n = c.size() - 2;
            c.shrink(n);
            c.learnt() ? lazy_drp_lrn_lits += n : lazy_drp_cla_lits += n;
            lazy_lit_droppings++;
        }

        // added by nabesima
        Lit comm = lazy_simp ? ~premises[toInt(~c[0])] : lit_Error;
        Lit antr = lit_Error;
        int aidx = 0;
        int paid = amo ? amo_id[toInt(c[0])] : NO_AMO;    // positive amo id
        Lit nglt = lit_Undef;
        // modified by nabesima
        //for (int i = 1; i < c.size(); i++){
        for (int i = 1; i < c.size(); ){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){

                // The former means that if p is a decsion literal, then we can not trace it. (added by nabesima)
                // The latter means that if p is a literal at a level that does not appear in the learnt clause, then we can not propagate p from literals in the clause. (added by nabesima)
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    // added by nabesima
                    if (lazy_uw_lit_elim && i > 1 && (implies(p, c[0]) || implies(p, c[1]))) {
                        if (certified_unsat) c.copyTo(tmp_lits);
                        c[i] = c.last();
                        c.shrink(1);
                        c.learnt() ? lazy_rm_uw_lrn_lits++ : lazy_rm_uw_cla_lits++;
                        if (certified_unsat) { writeClause(c); writeDeletedLits(tmp_lits); }
                        continue;
                    }
                    if (lazy_pr_lit_elim && i > 1 && probedValue(p) == l_False) {
                        if (certified_unsat) c.copyTo(tmp_lits);
                        c[i] = c.last();
                        c.shrink(1);
                        c.learnt() ? lazy_rm_pr_lrn_lits++ : lazy_rm_pr_cla_lits++;
                        if (certified_unsat) { writeClause(c); writeDeletedLits(tmp_lits); }
                        continue;
                    }

                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
            // added by nabesima
            if (lazy_cla_probing && comm != lit_Error && probedValue(p) != l_False) {
                Lit r = ~getCommonPremise(~p, ~comm);
                if (r != lit_Error)
                    comm = r;
                else if (antr == lit_Error) {   // r == lit_Error
                    if (implies(p, ~comm))
                        antr = ~comm;
                    else
                        antr = ~premises[toInt(~p)];
                    aidx = i;
                }
                else
                    comm = antr = lit_Error;
            }
            if (amo && paid != NO_AMO) {
                if (amo_id[toInt(p)] != paid) {
                    if (amo_id[toInt(~p)] == paid && nglt == lit_Undef)
                        nglt = p;
                    else
                        paid = NO_AMO;
                }
            }
            // added by nabesima
            i++;
        }
        // added by nabesima
        if (lazy_cla_probing && comm != lit_Error && antr == lit_Error)
            addProbedLit(comm, PRB_CLAUSE);
        if (lazy_cla_probing && comm != lit_Error && antr != lit_Error) {
            if (comm == ~antr) {
                if (lazy_eqv_probing) {
                    putEquivLit(antr, c[aidx]);
                    if (c.size() == 2) {
                        assert(aidx == 1);
                        putEquivLit(~antr, c[0]);
                    }
                }
            }
        }
        if (amo && paid != NO_AMO) {
            if (nglt == lit_Undef && at_most_one[paid].size() > c.size()) {
                incTouchComps();
                for (int i=0; i < c.size(); i++)
                    touch_time[toInt(c[i])] = touch_comps;
                vec<Lit>& ps = at_most_one[paid];
                for (int j=0; j < ps.size(); j++)
                    if (touch_time[toInt(ps[j])] != touch_comps)
                        addProbedLit(~ps[j], PRB_AMO);
            }
            else if (nglt != lit_Undef)
                addProbedLit(nglt, PRB_AMO);
        }
    }
    return true;
}

// added by nabesima
void Solver::minimizeByPremises(vec<Lit>& ps) {
    if (ps.size() > lrn_max_size) return;
    double cpu_time = cpuTime();

    incTouchComps();
    for (int i=0; i < ps.size(); i++)
        touch_time[toInt(ps[i])] = touch_comps;
    assert(simp_reached_toclear.size() == 0);

    int i, j;
    for (i = j = 1; i < ps.size(); i++) {   // Skip the asserting literal
        Lit q = ~ps[i];
        if (simp_reached[toInt(q)]) {       // If q is required to remove other literals, then it remains.
            ps[j++] = ps[i];
            continue;
        }
        assert(simp_seen_toclear.size() == 0);
        bool redundant = false;
        while (true) {
            Lit p = premises[toInt(q)];     // p -> q
            if (value(p) != l_True) {     // Fail. there is no path to a literal in ps.
                if (value(p) == l_False && simp_seen[toInt(~p)]) {
                    // ~p should be true to prevent a conflict.
                    for (int k=0; k < simp_seen_toclear.size(); k++) {
                        Lit r = simp_seen_toclear[k];
                        simp_reached[toInt(r)] = 1;
                        simp_reached_toclear.push(r);
                        if (r == ~p) break;
                    }
                    redundant = true;
                    addProbedLit(~p, PRB_FAILED_LIT);
                }
                break;
            }
            if (p == ~ps[i]) {                // Self-loop to ps[i]
                if (lazy_eqv_probing && p != q) {
                    for (int k = 0; k < simp_seen_toclear.size(); k++)
                        putEquivLit(p, simp_seen_toclear[k]);
                }
                break;
            }
            if (simp_seen[toInt(p)]) {         // Loop to an intermediate node
                if (lazy_eqv_probing && p != q) {
                    int k = simp_seen_toclear.size() - 1;
                    while (simp_seen_toclear[k] != p) {
                        putEquivLit(p, simp_seen_toclear[k]);
                        k--;
                        assert(k >= 0);
                    }
                }
                break;
            }
            if (touch_time[toInt(~p)] == touch_comps || simp_reached[toInt(p)]) {
                for (int k=0; k < simp_seen_toclear.size(); k++) {
                    Lit r = simp_seen_toclear[k];
                    simp_reached[toInt(r)] = 1;
                    simp_reached_toclear.push(r);
                }
                redundant = true;
                if (!simp_reached[toInt(p)]) {
                    simp_reached[toInt(p)] = 1;      // to forbid removing the literal ~q in ps.
                    simp_reached_toclear.push(p);
                }
                break;
            }
            simp_seen[toInt(p)] = 1;
            simp_seen_toclear.push(p);
            q = p;
        }
        if (!redundant)
            ps[j++] = ps[i];
        for (int k=0; k < simp_seen_toclear.size(); k++)
            simp_seen[toInt(simp_seen_toclear[k])] = 0;
        simp_seen_toclear.clear();
    }

    ps.shrink(i - j);
    bin_rm_lrn_lits  += i - j;

    for (int k=0; k < simp_reached_toclear.size(); k++) {
        Lit p = simp_reached_toclear[k];
        simp_reached[toInt(p)] = 0;
    }
    simp_reached_toclear.clear();

    bin_min_time += cpuTime() - cpu_time;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                // added by nabesima
                if (bin_propagation && c.size() == 2 && value(c[0]) == l_False) {
                  assert(value(c[1]) == l_True);
                  Lit tmp = c[0];
                  c[0] =  c[1], c[1] = tmp;
                }
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}

// modified by nabesima
//void Solver::uncheckedEnqueue(Lit p, CRef from)
void Solver::uncheckedEnqueue(Lit p, CRef from, Lit pre, uint32_t info)
{
    assert(decisionLevel() == 0 || trail_lim.last() == trail.size() || from != CRef_Undef);
    assert(value(p) == l_Undef);
    assert(!lazy_simp || !rewrited[var(p)]);
    assigns[var(p)] = lbool(!sign(p));
    // modified by nabesima
    //vardata[var(p)] = mkVarData(from, decisionLevel());
    if (pre == lit_Undef) pre = p;
    vardata[var(p)] = mkVarData(from, decisionLevel(), pre, info);
    trail.push_(p);
    // added by nabesima
    enqueues++;
    if (probed_lit_chain && (decisionLevel() == 0 || probedValue(pre) == l_True))
        addProbedLit(p, PRB_PREMISE_CHAIN);
    // added by nabesima
    if (closed_lbd && from != CRef_Undef)
        min_lbd[var(p)] = ca[from].learnt() ? ca[from].lbd() : INT32_MAX;
    if (verbosity >= 2)
        assigned_lits[toInt(p)]++;
    if (from != CRef_Undef) {
        if (!rm_simulate || !ca[from].removed())
            ca[from].used(true);
        else
            ca[from].rm_used(true);
    }
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef  confl        = CRef_Undef;
    int   num_props    = 0;

    watches.cleanAll();
    // added by nabesima
    if (bin_propagation) bin_watches.cleanAll();
    if (lazy_bin_add) { imp_conf_cands.clear(); imp_prop_cands.clear(); eqv_conf_cands.clear(); eqv_prop_cands.clear(); }

REPROPAGATE:    // added by nabsima

    while (qhead < trail.size()){
        Lit p = trail[qhead++];     // 'p' is enqueued fact to propagate.

        num_props++;
        // added by nabesima
        if (rm_simulate && (varinfo(var(p)) & VINFO_RM_PROP))
            rm_propagations++;

        // added by nabesima
        Lit      far_dom = premise(var(p));

        // Propagate order axioms. added by nabesima
        if (native_oa && sat2csp[var(p)] != var_Undef) {
            Var v = var(p);
            if (sign(p) == false) {
                Var end = csp_lb[sat2csp[v]];
                // Now v is true, then check v-1
                v--;
                // assigns true from v to end
                while (v >= end) {
                    if (value(v) == l_True)
                        break;
                    if (value(v) == l_False) {
                        Clause &c = ca[pos_oa[v]];
                        assert(value(c[0]) == l_False && value(c[1]) == l_False);
                        qhead = trail.size();
                        confl = pos_oa[v];
                        break;
                    }
                    //if (value(v) == l_Undef)
                    assert(pos_oa[v] != CRef_Undef);
                    uncheckedEnqueue(mkLit(v), pos_oa[v], far_dom);
                    oa_propagations++;
                    v--;
                }
            } else {
                Var end = csp_ub[sat2csp[v]];
                // Now v is false, then check v+1
                v++;
                while (v <= end) {
                    if (value(v) == l_False)
                        break;
                    if (value(v) == l_True) {
                        Clause &c = ca[neg_oa[v]];
                        assert(value(c[0]) == l_False && value(c[1]) == l_False);
                        qhead = trail.size();
                        confl = neg_oa[v];
                        break;
                    }
                    //if (value(v) == l_Undef)
                    assert(neg_oa[v] != CRef_Undef);
                    uncheckedEnqueue(~mkLit(v), neg_oa[v], far_dom);
                    oa_propagations++;
                    v++;
                }
            }
            if (confl != CRef_Undef)
                break;
        }

        // added by nabesima
        // First, propagate binary clauses
        if (bin_propagation) {
            vec<Watcher>& ws = bin_watches[p];
            Watcher       *i, *end;
            for (i = (Watcher*)ws, end = i + ws.size();  i != end; i++) {
              Lit q = i->blocker;
              if (value(q) == l_True)
                  continue;
              if (value(q) == l_Undef)
                  uncheckedEnqueue(q, i->cref, far_dom, varinfo(var(p)));
              else {
                  // CONFLICT
                  bin_conflicts++;
                  confl = i->cref;
                  qhead = trail.size();
                  if (rm_simulate && (varinfo(var(p)) & VINFO_RM_PROP))
                      rm_conflicts++;
                  break;
              }
            }
            if (confl != CRef_Undef)
                break;
        }

        vec<Watcher>&  ws = watches[p];
        Watcher        *i, *j, *end;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;

            if (value(blocker) == l_True) {
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True) {
                *j++ = w; continue; }

            // Look for new watch:
            // modified by nabesima
            //for (int k = 2; k < c.size(); k++)
            //    if (value(c[k]) != l_False){
            //        c[1] = c[k]; c[k] = false_lit;
            //        watches[~c[1]].push(w);
            //        goto NextClause; }
            Lit      dom   = far_dom;
            uint32_t vinfo = VINFO_NONE;
            for (int k = 2; k < c.size(); ) {
                Lit ck = c[k];

                if (value(ck) != l_False) {
                    c[1] = ck; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause;
                }

                // added by nabesima
                // Checks whethereach falsified literal has the same dominator or not.
                // - "dom != lit_Undef" means to avoid checking the following conditions.
                // - "probedValue(ck) == l_False" means that we can ignore ck to compute a dominator.
                if (dom != lit_Undef && probedValue(ck) != l_False && dom != premise(var(ck)))
                    dom = lit_Undef;
                if (rm_simulate && (varinfo(var(ck)) & VINFO_RM_PROP))
                    vinfo |= VINFO_RM_PROP;
                k++;
            }

            // Did not find watch -- clause is unit under assignment:
            // modified by nabesima
            // *j++ = w;
            if (bin_propagation && c.size() == 2)
                bin_watches[p].push(w);
            else
                *j++ = w;

            if (rm_simulate && c.removed())
                vinfo |= VINFO_RM_PROP;

            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
                // added by nabesima
                if (rm_simulate && (vinfo & VINFO_RM_PROP))
                    rm_conflicts++;
            } else {
                uncheckedEnqueue(first, cr, dom, vinfo);
            }

            // added by nabesima
            if (c.learnt()) {
                if (rdb_eval >= RDB_LBD_CVR || verbosity >= 2) {
                    used_lbd.inc(c.lbd());
                    c.used(true);
                }
                if (rdb_eval == RDB_LBD_CVR) {
                    if (core_lbd_period && c.lbd() <= core_lbd_threshold)
                        c.ttl(core_lbd_period);
                    if (supp_lbd_period && core_lbd_threshold < c.lbd() && c.lbd() <= supp_lbd_threshold)
                        c.ttl(supp_lbd_period);
                    if (othr_lbd_period && supp_lbd_threshold < c.lbd())
                        c.ttl(othr_lbd_period);
                }
                max_len_used_learnt = std::max(max_len_used_learnt, (uint32_t)c.size());
                max_lbd_used_learnt = std::max(max_lbd_used_learnt, (uint32_t)c.lbd());
            }

        NextClause:;
        }
        ws.shrink(i - j);

        // added by nabesima
        if (lazy_bin_add && confl == CRef_Undef) {
            Lit q = ~premises[toInt(~p)];   // p -> q
            Lit r = getDelegate(p);
            if (lazy_bin_add & ODA_CONF) {
                if (value(q) == l_False && level(var(q)) == decisionLevel())
                    imp_conf_cands.push(p);
                if (value(r) == l_False && level(var(r)) == decisionLevel())
                    eqv_conf_cands.push(p);
            }
            if (lazy_bin_add & ODA_PROP) {
                if (value(premises[toInt(~p)]) == l_Undef)
                    imp_prop_cands.push(p);
                if (value(r) == l_Undef)
                    eqv_prop_cands.push(p);
            }
        }
    }
    propagations += num_props;
    simpDB_props -= num_props;

    // added by nabesima
    if (lazy_bin_add && confl == CRef_Undef) {
        confl = addBinsOnDemand();
        if (confl == CRef_Undef && qhead < trail.size())
            goto REPROPAGATE;
    }

    return confl;
}

// added by nabesima
// new_dom -> p
inline void Solver::lazyProbing(Lit new_dom, Lit p) {
    assert(new_dom != lit_Undef);

    // Use the representative one if it exists.
    //p       = getDelegate(p);
    //new_dom = getDelegate(new_dom);

    assert(!rewrited[var(new_dom)]);
    assert(!rewrited[var(p)]);

    Lit old_dom = premises[toInt(p)];
    if (old_dom == new_dom) {
        if (certified_unsat) return;    // to reduce the proof size.
        Lit q = new_dom;
        while (true) {
            if (value(q) != l_True) return;
            new_dom = premise(var(q));
            if (new_dom == q) return;
            if (certified_unsat) writeUniqBin(~new_dom, q);
            old_dom = premises[toInt(q)];
            if (new_dom != old_dom) break;
            q = new_dom;
        }
    }
    Lit opp_dom = premises[toInt(~p)];

    if (certified_unsat) writeUniqBin(~new_dom, p);

    if (lazy_fld_probing) {
        Lit common = lit_Undef;
        if ((common = getCommonPremise(opp_dom, new_dom)) != lit_Undef)
            addProbedLit(~common, PRB_FAILED_LIT);
        else if ((common = getCommonPremise(opp_dom, old_dom)) != lit_Undef)
            addProbedLit(~common, PRB_FAILED_LIT);
    }
    if (lazy_pol_probing && hasConfPremise(old_dom, new_dom))
        addProbedLit(p, PRB_POLALITY);
    else if (lazy_nec_probing && (implies(~p, new_dom) || implies(~p, old_dom))) {
        addProbedLit(p, PRB_NECESSARY);
    }
    if (lazy_nec_probing) {
        if (implies(p, ~new_dom))
            addProbedLit(~new_dom, PRB_NECESSARY);
        if (implies(p, ~old_dom))
            addProbedLit(~old_dom, PRB_NECESSARY);
        if (implies(~p, ~opp_dom))
            addProbedLit(~opp_dom, PRB_NECESSARY);
    }
    if (lazy_eqv_probing) {
        if (~new_dom == opp_dom)
            putEquivLit(p, new_dom);
        else if (premises[toInt(new_dom)] == ~opp_dom || premises[toInt(opp_dom)] == ~new_dom) {
            // p -> ~opp_dom -> new_dom -> p
            putEquivLit(p, new_dom);
            putEquivLit(p, ~opp_dom);
        }
        else if (premises[toInt(new_dom)] == ~premises[toInt(opp_dom)] ||
                 premises[toInt(premises[toInt(new_dom)])] == ~opp_dom) {
            // p -> ~opp_dom -> pre(new_dom) -> new_dom -> p
            putEquivLit(p, new_dom);
            putEquivLit(p, premises[toInt(new_dom)]);
            putEquivLit(p, ~opp_dom);
        }
        else if (premises[toInt(premises[toInt(opp_dom)])] == ~new_dom) {
            // p -> ~opp_dom -> ~pre(opp_dom) -> new_dom -> p
            putEquivLit(p, new_dom);
            putEquivLit(p, ~premises[toInt(opp_dom)]);
            putEquivLit(p, ~opp_dom);
        }
        if (~old_dom == opp_dom)
            putEquivLit(p, old_dom);
        else if (premises[toInt(old_dom)] == ~premises[toInt(opp_dom)] ||
                 premises[toInt(premises[toInt(old_dom)])] == ~opp_dom) {
            // p -> ~opp_dom -> pre(old_dom) -> old_dom -> p
            putEquivLit(p, old_dom);
            putEquivLit(p, premises[toInt(old_dom)]);
            putEquivLit(p, ~opp_dom);
        }
        else if (premises[toInt(premises[toInt(opp_dom)])] == ~old_dom) {
            // p -> ~opp_dom -> ~pre(opp_dom) -> old_dom -> p
            putEquivLit(p, old_dom);
            putEquivLit(p, ~premises[toInt(opp_dom)]);
            putEquivLit(p, ~opp_dom);
        }
    }

    if (amo) {
        if (new_dom != p && amo_id[toInt(new_dom)] == amo_id[toInt(p)])
            addProbedLit(~new_dom, PRB_AMO);
        if (old_dom != p && amo_id[toInt(old_dom)] == amo_id[toInt(p)])
            addProbedLit(~old_dom, PRB_AMO);
        if (lazy_eqv_probing && new_dom != p && amo_id[toInt(~new_dom)] == amo_id[toInt(p)])
            putEquivLit(new_dom, p, EQV_AMO);
        if (lazy_eqv_probing && old_dom != p && amo_id[toInt(~old_dom)] == amo_id[toInt(p)])
            putEquivLit(old_dom, p, EQV_AMO);
    }

    premises[toInt(p)] = new_dom;
    premise_updates++;
}

inline CRef Solver::addBinsOnDemand() {
    double cpu_time = cpuTime();
    CRef   confl    = CRef_Undef;

    // Conflict
    for (int i=0; i < imp_conf_cands.size(); i++) {
        Lit y = imp_conf_cands[i];
        Lit x = ~premises[toInt(~y)];    // ~x -> ~y = y -> x
        assert(value(y) == l_True);
        assert(value(x) == l_False);
        if (!rewrited[var(x)]) {
            // Make a learnt clause: y -> x
            CRef cr = addBinLearnt(x, ~y);
            lazy_add_conf_bins++;
            if (confl == CRef_Undef)
                confl = cr;
        }
    }
    for (int i=0; i < eqv_conf_cands.size(); i++) {
        Lit y = eqv_conf_cands[i];
        Lit x = getDelegate(y);
        assert(value(y) == l_True);
        assert(value(x) == l_False);
        CRef cr = addBinLearnt(~y, x);    // Make a learnt clause: y -> x = -y v x
        lazy_add_conf_bins++;
        if (confl == CRef_Undef)
            confl = cr;
    }

    // Propagation
    for (int i=0; i < imp_prop_cands.size(); i++) {
        Lit y = imp_prop_cands[i];
        Lit x = ~premises[toInt(~y)];    // ~x -> ~y = y -> x
        assert(value(y) == l_True);
        if (!rewrited[var(x)] && value(x) == l_Undef) {
            // Make a learnt clause: p -> q
            CRef cr = addBinLearnt(x, ~y);
            uncheckedEnqueue(x, cr, premise(var(y)));
            lazy_add_prop_bins++;
        }
    }
    for (int i=0; i < eqv_prop_cands.size(); i++) {
        Lit y = eqv_prop_cands[i];
        Lit x = getDelegate(y);    // x == y
        assert(value(y) == l_True);
        if (value(x) == l_Undef) {
            CRef cr = addBinLearnt(~y, x);    // Make a learnt clause: y -> x = -y v x
            uncheckedEnqueue(x, cr, premise(var(y)));
            lazy_add_prop_bins++;
        }
    }

    lazy_bin_add_time += cpuTime() - cpu_time;

    return CRef_Undef;
}

inline CRef Solver::addBinLearnt(Lit p, Lit q) {
    // Make a learnt clause p v q
    add_tmp.clear(); add_tmp.push(p); add_tmp.push(q);
    CRef cr = ca.alloc(add_tmp, true);
    learnts.push(cr);
    ca[cr].lbd(2);
    attachClause(cr);
    if (dec_elim) {
        if (!decision[var(p)] && !decision[var(q)]) {
            setDecisionVar(var(q), true);
            elim_dec_vars--;
        }
    }
    if (certified_unsat)
        writeBin(p, q);
    return cr;
}
// added by nabesima
inline void Solver::addProbedLit(Lit p, int type) {
    assert(p != lit_Undef);
    assert(p != lit_Error);
    if (rewrited[var(p)])
        return;
    if (probedValue(p) == l_True)
        return;
    if (probedValue(p) == l_False) {
        conflict_probing = true;
        return;
    }

    assert(probedValue(p) == l_Undef);
    probed_vals[var(p)] = lbool(!sign(p));
    probed_types[var(p)] = type;

    // Equivalent literals
    int id = lit2eq_lits[toInt(p)];
    if (id != NO_EQ_LITS) {
        EqLits& lits = eq_lits[abs(id)];
        for (int j=0; j < lits.size(); j++)
            addProbedLit(id > 0 ? lits[j] : ~lits[j], PRB_EQV_CHAIN);
    }

    if (amo && decisionLevel() == 0)
        propAMO(p);

    if (value(p) == l_True && level(var(p)) == 0)    // otherwise, conflict will occurs in propagation of probed literals.
        return;
    if (certified_unsat) writeUnit(p);
    num_probed_lits[type]++;
    probed_lits_queue.push(p);
    pr_last_starts = starts;
}
// added by nabesima
void Solver::putEquivLit(Lit p, Lit q, int type) {
    if (p == q) return;
    assert(p != ~q);

    // Avoid rewriting order encoded variables
    if (native_oa && (sat2csp[var(p)] != var_Undef || sat2csp[var(q)] != var_Undef))
        return;

    //printf("eq: "); printLit(p); printf(" = "); printLit(q); printf("\n");

    int p_id = lit2eq_lits[toInt(p)];
    int q_id = lit2eq_lits[toInt(q)];
    uint32_t old_eq_vars = eq_vars;

    if (p_id == NO_EQ_LITS && q_id == NO_EQ_LITS) {
        // Make a new equivalent literal set.
        uint32_t id = eq_lits.size();
        assert(id > 0);
        eq_lits.push();
        eq_lits.last().push(p);  // delegate
        eq_lits.last().push(q);
        lit2eq_lits[toInt( p)] = +id;
        lit2eq_lits[toInt( q)] = +id;
        lit2eq_lits[toInt(~p)] = -id;
        lit2eq_lits[toInt(~q)] = -id;
        eq_vars++;
        if (type == EQV_AMO) eq_amo_vars++;
        eq_vars_sizes.inc(2);
        assert(!rewrited[var(q)]);

//        if (certified_unsat) {
//            writeLits(~p, q);    //  p -> q
//            writeLits(p, ~q);    // ~p -> ~q
//        }

        if (probedValue(p) != probedValue(q)) {
            if (probedValue(p) == l_Undef) {
                assert(probedValue(q) != l_Undef);
                addProbedLit(probedValue(q) == l_True ? p : ~p, PRB_PREMISE_CHAIN);
            }
            else if (probedValue(q) == l_Undef) {
                assert(probedValue(p) != l_Undef);
                addProbedLit(probedValue(p) == l_True ? q : ~q, PRB_PREMISE_CHAIN);
            }
            else
                conflict_probing = true;
        }
    }
    else if (p_id == NO_EQ_LITS) {  // q_id != NO_EQ_LITS
        if (q_id < 0) { q_id = -q_id; p = ~p; q = ~q; }
        EqLits& q_set = eq_lits[q_id];
        assert(q_set.size() > 0);
        q_set.push(p);
        lit2eq_lits[toInt( p)] = +q_id;
        lit2eq_lits[toInt(~p)] = -q_id;
        eq_vars++;
        if (type == EQV_AMO) eq_amo_vars++;
        eq_vars_sizes.inc(q_set.size());
        eq_vars_sizes.dec(q_set.size() - 1);
        assert(!rewrited[var(p)]);

//        if (certified_unsat) {
//            writeLits(~p, q_set.delegate());    //  p -> q
//            writeLits(p, ~q_set.delegate());    // ~p -> ~q
//        }

        if (probedValue(p) != probedValue(q)) {
            if (probedValue(p) == l_Undef) {
                assert(probedValue(q) != l_Undef);
                addProbedLit(probedValue(q) == l_True ? p : ~p, PRB_PREMISE_CHAIN);
            }
            else if (probedValue(q) == l_Undef) {
                assert(probedValue(p) != l_Undef);
                for (int i=0; i < q_set.size(); i++)
                    addProbedLit(probedValue(p) == l_True ? q_set[i] : ~q_set[i], PRB_PREMISE_CHAIN);
            }
            else
                conflict_probing = true;
        }
    }
    else if (q_id == NO_EQ_LITS) {  // p_id != NO_EQ_LITS
        if (p_id < 0) { p_id = -p_id; p = ~p; q = ~q; }
        EqLits& p_set = eq_lits[p_id];
        assert(p_set.size() > 0);
        p_set.push(q);
        lit2eq_lits[toInt( q)] = +p_id;
        lit2eq_lits[toInt(~q)] = -p_id;
        eq_vars++;
        if (type == EQV_AMO) eq_amo_vars++;
        eq_vars_sizes.inc(p_set.size());
        eq_vars_sizes.dec(p_set.size() - 1);
        assert(!rewrited[var(q)]);

//        if (certified_unsat) {
//            writeLits(~q, p_set.delegate());    //  q -> p
//            writeLits(q, ~p_set.delegate());    // ~q -> ~p
//        }

        if (probedValue(p) != probedValue(q)) {
            if (probedValue(p) == l_Undef) {
                assert(probedValue(q) != l_Undef);
                for (int i=0; i < p_set.size(); i++)
                    addProbedLit(probedValue(q) == l_True ? p_set[i] : ~p_set[i], PRB_PREMISE_CHAIN);
            }
            else if (probedValue(q) == l_Undef) {
                assert(probedValue(p) != l_Undef);
                addProbedLit(probedValue(p) == l_True ? q : ~q, PRB_PREMISE_CHAIN);
            }
            else
                conflict_probing = true;
        }
    }
    else if (p_id == -q_id) {  // Has conflicts?
        conflict_probing = true;
    }
    else if (p_id != q_id) {  // merges two equivalent literal sets.
        if (p_id < 0) { p_id = -p_id; q_id = -q_id; p = ~p; q = ~q; }
        if (q_id > 0) {
            EqLits& p_set = eq_lits[p_id];
            EqLits& q_set = eq_lits[q_id];
            eq_vars_sizes.dec(p_set.size());
            eq_vars_sizes.dec(q_set.size());
            // p_set += q_set
            for (int i=0; i < q_set.size(); i++) {
                lit2eq_lits[toInt( q_set[i])] = +p_id;
                lit2eq_lits[toInt(~q_set[i])] = -p_id;
                p_set.push(q_set[i]);
            }
            assert(!rewrited[var(q_set.delegate())]);

//            if (certified_unsat) {
//                writeLits(~q_set.delegate(), p_set.delegate());    //  q -> p
//                writeLits(q_set.delegate(), ~p_set.delegate());    // ~q -> ~p
//            }

            q_set.eliminate();
            eq_vars_sizes.inc(p_set.size());

            if (probedValue(p) != probedValue(q)) {
                if (probedValue(p) == l_Undef) {
                    assert(probedValue(q) != l_Undef);
                    for (int i=0; i < p_set.size(); i++)
                        addProbedLit(probedValue(q) == l_True ? p_set[i] : ~p_set[i], PRB_PREMISE_CHAIN);
                }
                else if (probedValue(q) == l_Undef) {
                    assert(probedValue(p) != l_Undef);
                    for (int i=0; i < p_set.size(); i++)
                        addProbedLit(probedValue(p) == l_True ? p_set[i] : ~p_set[i], PRB_PREMISE_CHAIN);
                }
                else
                    conflict_probing = true;
            }
        }
        else {
            EqLits& p_set = eq_lits[p_id];
            EqLits& q_set = eq_lits[-q_id];
            eq_vars_sizes.dec(p_set.size());
            eq_vars_sizes.dec(q_set.size());
            // q_set += p_set
            for (int i=0; i < q_set.size(); i++) {
                lit2eq_lits[toInt( q_set[i])] = -p_id;
                lit2eq_lits[toInt(~q_set[i])] = +p_id;
                p_set.push(~q_set[i]);
            }
            assert(!rewrited[var(q_set.delegate())]);

//            if (certified_unsat) {
//                writeLits(~p_set.delegate(), q_set.delegate());    //  p -> q
//                writeLits(p_set.delegate(), ~q_set.delegate());    // ~p -> ~q
//            }

            q_set.eliminate();
            eq_vars_sizes.inc(p_set.size());

            if (probedValue(p) != probedValue(q)) {
                if (probedValue(p) == l_Undef) {
                    assert(probedValue(q) != l_Undef);
                    for (int i=0; i < p_set.size(); i++)
                        addProbedLit(probedValue(q) == l_True ? p_set[i] : ~p_set[i], PRB_PREMISE_CHAIN);
                }
                else if (probedValue(q) == l_Undef) {
                    assert(probedValue(p) != l_Undef);
                    for (int i=0; i < p_set.size(); i++)
                        addProbedLit(probedValue(p) == l_True ? p_set[i] : ~p_set[i], PRB_PREMISE_CHAIN);
                }
                else
                    conflict_probing = true;
            }
        }
        eq_vars++;
        if (type == EQV_AMO) eq_amo_vars++;
    }
    else
        return;  // already registered.

    if (amo) {
        int id = lit2eq_lits[toInt(p)];
        assert(id != NO_EQ_LITS);
        EqLits& lits = eq_lits[abs(id)];
        for (int i=0; i < lits.size(); i++) {
            int p1id = amo_id[toInt( lits[i])];
            int n1id = amo_id[toInt(~lits[i])];
            for (int j=i+1; j < lits.size(); j++) {
                int p2id = amo_id[toInt( lits[j])];
                int n2id = amo_id[toInt(~lits[j])];
                if (p1id == p2id) {
                    addProbedLit(~lits[i], PRB_AMO);
                    addProbedLit(~lits[j], PRB_AMO);
                }
                else if (n1id == n2id) {
                    addProbedLit(lits[i], PRB_AMO);
                    addProbedLit(lits[j], PRB_AMO);
                }
                else if (p1id == n2id && at_most_one[p1id].size() > 2) {
                    for (int k=0; k < at_most_one[p1id].size(); k++) {
                        Lit l = at_most_one[p1id][k];
                        if (l == lits[i] || l == ~lits[j]) continue;
                        addProbedLit(~l, PRB_AMO);
                    }
                }
                else if (n1id == p2id && at_most_one[p2id].size() > 2) {
                    for (int k=0; k < at_most_one[p2id].size(); k++) {
                        Lit l = at_most_one[p2id][k];
                        if (l == ~lits[i] || l == lits[j]) continue;
                        addProbedLit(~l, PRB_AMO);
                    }
                }
            }
        }
    }

    if (old_eq_vars < eq_vars)
        rw_last_starts = starts;
}

/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt {
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); }
};
// added by nabesima
struct reduceDB_lt_by_lbd {
    ClauseAllocator& ca;
    reduceDB_lt_by_lbd(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {
        // Subsumption criteria
        if (ca[x].subsumed() && !ca[y].subsumed()) return true;
        if (ca[y].subsumed() && !ca[x].subsumed()) return false;
        // First criteria
        if (ca[x].size() >  2 && ca[y].size() == 2) return true;
        if (ca[y].size() >  2 && ca[x].size() == 2) return false;
        if (ca[x].size() == 2 && ca[y].size() == 2) return false;
        // Second one
        if (ca[x].lbd() > ca[y].lbd()) return true;
        if (ca[x].lbd() < ca[y].lbd()) return false;
        // Last one
        return ca[x].activity() < ca[y].activity();
    }
};
void Solver::reduceDB()
{
    double cpu_time = cpuTime();
    int     i = 0, j = 0;

    // added by nabesima
    reduce_dbs++;
    int removed = 0;

    // modified by nabesima
    if (rdb_eval == RDB_LRU) {    // minisat version
        double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

        if (!rm_low_act_learnts) extra_lim = 0; // added by nabesima

        sort(learnts, reduceDB_lt(ca));

        int limit = learnts.size() * (1 - rdb_ub);

        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        for (i = j = 0; i < learnts.size(); i++){
            Clause& c = ca[learnts[i]];

            if (c.size() > 2 && !locked(c) && (i < limit || c.activity() < extra_lim || c.subsumed())) {
                if (!rm_simulate)
                    removeClause(learnts[i]);
                else {
                    c.removed(true);
                    rm_learnts.push(learnts[i]);
                }
                removed++;
                if (c.subsumed())
                    c.learnt() ? subsumed_learnts++ : subsumed_clauses++;
            }
            else
                learnts[j++] = learnts[i];
        }
        learnts.shrink(i - j);
    }
    else if (rdb_eval == RDB_LBD) {    // lbd version

        sort(learnts, reduceDB_lt_by_lbd(ca));

        // When a lot of "good" clauses exist, hold some of them (glucose 3.0)
        if (ca[learnts[learnts.size() * rdb_ub]].lbd() <= 3)
            max_learnts += inc_lrn_limit;

        int limit = learnts.size() * (1 - rdb_ub);

        int num_locked   = 0;
        int num_subsumed = 0;
        int num_kept_lbd = 0;
        int num_kept_ub  = 0;
        int num_kept_ttl = 0;
        int num_lost_ttl = 0;

        for (i = j = 0; i < learnts.size(); i++) {
            Clause& c = ca[learnts[i]];

            bool remove = true;
            if (locked(c)) {
                remove = false;
                num_locked++;
            }
            else if (c.subsumed()) {
                num_subsumed++;
                subsumed_learnts++;
            }
            else if (c.lbd() <= core_lbd_threshold || c.size() <= 2) {
                remove = false;
                num_kept_lbd++;
            }
            else if (i >= limit) {
                remove = false;
                num_kept_ub++;
            }
            else if (c.ttl() > 0) {
                remove = false;
                num_kept_ttl++;
            }
            else
                num_lost_ttl++;

            if (remove) {
                if (!rm_simulate)
                    removeClause(learnts[i]);
                else {
                    c.removed(true);
                    rm_learnts.push(learnts[i]);
                }
                removed++;
            }
            else {
                if (c.ttl() > 0) {
                    c.dec_ttl();
                    limit++;    //we keep c, so we can delete an other clause (glucose 3.0)
                }
                learnts[j++] = learnts[i];
            }
        }
        learnts.shrink(i - j);

        if (verbosity >= 3) {
            printf("c R [RDB Statistics #%d]\n", reduce_dbs);
            printf("c R kept: lbd      = %7d (%4.1f/%4.1f%%)\n", num_kept_lbd, 100.0 * num_kept_lbd / nLearnts(), 100.0 * num_kept_lbd / nLearnts());
            printf("c R kept: ttl      = %7d (%4.1f/%4.1f%%)\n", num_kept_ttl, 100.0 * num_kept_ttl / nLearnts(), 100.0 * (num_kept_lbd + num_kept_ttl) / nLearnts());
            printf("c R kept: ub       = %7d (%4.1f/%4.1f%%)\n", num_kept_ub,  100.0 * num_kept_ub  / nLearnts(), 100.0 * (num_kept_lbd + num_kept_ttl + num_kept_ub) / nLearnts());
            printf("c R kept: locked   = %7d (%4.1f/%4.1f%%)\n", num_locked,   100.0 * num_locked   / nLearnts(), 100.0 * (num_kept_lbd + num_kept_ttl + num_kept_ub + num_locked) / nLearnts());
            printf("c R lost: ttl      = %7d (%4.1f/%4.1f%%)\n", num_lost_ttl, 100.0 * num_lost_ttl / nLearnts(), 100.0 * (num_lost_ttl) / nLearnts());
            printf("c R lost: subsumed = %7d (%4.1f/%4.1f%%)\n", num_subsumed, 100.0 * num_subsumed / nLearnts(), 100.0 * (num_lost_ttl + num_subsumed) / nLearnts());
            printf("c\n");
        }
    }
    else if (rdb_eval == RDB_LBD_CVR) {    // lbd-coverage version

        updateRDBThreshold();

        int num_locked   = 0;
        int num_subsumed = 0;
        int num_kept_lbd = 0;
        int num_lost_lbd = 0;
        int num_kept_ttl = 0;
        int num_lost_ttl = 0;

        for (i = j = 0; i < learnts.size(); i++) {
            Clause& c = ca[learnts[i]];

            bool remove = true;
            if (locked(c)) {
                remove = false;
                num_locked++;
            }
            else if (c.subsumed()) {
                num_subsumed++;
                subsumed_learnts++;
            }
            else if (c.size() <= 2 || c.lbd() <= 1) {
                remove = false;
                num_kept_lbd++;
            }
            else if (c.lbd() <= core_lbd_threshold) {
                if (!core_lbd_period || c.ttl() > 0) {
                    remove = false;
                    num_kept_lbd++;
                }
                else
                    num_lost_lbd++;
            }
            else if (c.ttl() > 0) {
                remove = false;
                num_kept_ttl++;
            }
            else
                num_lost_ttl++;

            if (remove) {
                if (!rm_simulate)
                    removeClause(learnts[i]);
                else {
                    c.removed(true);
                    rm_learnts.push(learnts[i]);
                }
                removed++;
            }
            else {
                c.dec_ttl();
                learnts[j++] = learnts[i];
            }
        }

        if (verbosity >= 3) {
            printf("c R [RDB Statistics #%d]\n", reduce_dbs);
            printf("c R kept: lbd      = %7d (%4.1f/%4.1f%%)\n", num_kept_lbd, 100.0 * num_kept_lbd / nLearnts(), 100.0 * num_kept_lbd / nLearnts());
            printf("c R kept: ttl      = %7d (%4.1f/%4.1f%%)\n", num_kept_ttl, 100.0 * num_kept_ttl / nLearnts(), 100.0 * (num_kept_lbd + num_kept_ttl) / nLearnts());
            printf("c R kept: locked   = %7d (%4.1f/%4.1f%%)\n", num_locked,   100.0 * num_locked   / nLearnts(), 100.0 * (num_kept_lbd + num_kept_ttl + num_locked) / nLearnts());
            printf("c R lost: lbd      = %7d (%4.1f/%4.1f%%)\n", num_lost_lbd, 100.0 * num_lost_lbd / nLearnts(), 100.0 * num_lost_lbd / nLearnts());
            printf("c R lost: ttl      = %7d (%4.1f/%4.1f%%)\n", num_lost_ttl, 100.0 * num_lost_ttl / nLearnts(), 100.0 * (num_lost_lbd + num_lost_ttl) / nLearnts());
            printf("c R lost: subsumed = %7d (%4.1f/%4.1f%%)\n", num_subsumed, 100.0 * num_subsumed / nLearnts(), 100.0 * (num_lost_lbd + num_lost_ttl + num_subsumed) / nLearnts());
            printf("c\n");
        }
        learnts.shrink(i - j);
    }
    else
        assert(false);

    checkGarbage();
    reduce_time += cpuTime() - cpu_time;
    removed_learnts += removed;
}

void Solver::updateRDBThreshold()
{
    //
    // LBD
    //
    DynFreqDist holding_lbd;
    for (int i=0; i < learnts.size(); i++)
        holding_lbd.inc(ca[learnts[i]].lbd());

    if (verbosity >= 3) {
        printf("c\n");
        printf("c R [LBD Statistics #%d]\n", reduce_dbs);
        printf("c R LBD         used lbd               used clause lbd\n");
        printf("c R  tot  %10" PRIu64 "              %10" PRIu64 "\n",
                used_lbd.total(),
                holding_lbd.total());
        printf("c R  avg  %10.3f              %10.3f\n",
                used_lbd.avg(),
                holding_lbd.avg());
    }

    int old_core_lbd_threshold = core_lbd_threshold;
    core_lbd_threshold  = 0;

    double covered  = 0.0;
    double selected = 0.0;

    while (covered / used_lbd.total() < core_lbd_coverage || core_lbd_threshold < core_lbd_lb) {
        core_lbd_threshold++;
        covered += used_lbd.get(core_lbd_threshold);
        selected += holding_lbd.get(core_lbd_threshold);

        if (verbosity >= 3)
            printf("c R  %2d   %10" PRIu64 " (%4.1f/%4.1f%%) %10" PRIu64 " (%4.1f/%4.1f%%)\n",
                    core_lbd_threshold,
                    used_lbd.get   (core_lbd_threshold), used_lbd.rate   (core_lbd_threshold), used_lbd.trate   (core_lbd_threshold),
                    holding_lbd.get(core_lbd_threshold), holding_lbd.rate(core_lbd_threshold), holding_lbd.trate(core_lbd_threshold));
        if (selected / nLearnts() >= rdb_ub)
            break;
    }

    int old_supp_lbd_threshold = supp_lbd_threshold;
    supp_lbd_threshold = core_lbd_threshold;

    while (covered / used_lbd.total() < supp_lbd_coverage || supp_lbd_threshold < supp_lbd_lb) {
        supp_lbd_threshold++;
        covered += used_lbd.get(supp_lbd_threshold);
//        if (verbosity >= 3)
//            printf("c R  %2d   %10" PRIu64 " (%4.1f/%4.1f%%) %10" PRIu64 " (%4.1f/%4.1f%%)\n",
//                    supp_threshold,
//                    total_used_lbd.get(supp_threshold), total_used_lbd.rate(supp_threshold), total_used_lbd.trate(supp_threshold),
//                    holding_lbd   .get(supp_threshold), holding_lbd   .rate(supp_threshold), holding_lbd   .trate(supp_threshold));
    }

    if (verbosity >= 3) {
        printf("c R\n");
        printf("c R core_lbd_threshold = %d\n", core_lbd_threshold);
        printf("c R supp_lbd_threshold = %d\n", supp_lbd_threshold);
        printf("c R\n");
    }

    if (rdb_eval == RDB_LBD_CVR && (old_core_lbd_threshold < core_lbd_threshold || old_supp_lbd_threshold < supp_lbd_threshold)) {
        for (int i=0; i < learnts.size(); i++) {
            Clause &c = ca[learnts[i]];
            if (core_lbd_period && old_core_lbd_threshold < c.lbd() && c.lbd() <= core_lbd_threshold)
                c.ttl(core_lbd_period);
            if (supp_lbd_period && old_supp_lbd_threshold < c.lbd() && c.lbd() <= supp_lbd_threshold)
                c.ttl(supp_lbd_period);
        }
    }
}

void Solver::removeSatisfied(vec<CRef>& cs)
{
    // modified by nabesima
//    int i, j;
//    for (i = j = 0; i < cs.size(); i++){
//        Clause& c = ca[cs[i]];
//        // modified by nabesima
//        if (satisfied(c))
//            removeClause(cs[i]);
//        else
//            cs[j++] = cs[i];
//    }
//    cs.shrink(i - j);

    // added by nabesima
    assert(decisionLevel() == 0);
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.subsumed()) {
            c.learnt() ? subsumed_learnts++ : subsumed_clauses++;
            removeClause(cs[i]);
            continue;
        }

        Lit comm = lazy_simp ? ~premises[toInt(~c[0])] : lit_Error;
        Lit antr = lit_Error;
        int aidx = 0;
        int paid = amo ? amo_id[toInt(c[0])] : NO_AMO;    // positive amo id
        Lit nglt = lit_Undef;
        if (certified_unsat) tmp_lits.clear();
        int k, l;
        for (k = l = 0; k < c.size(); k++) {
            Lit ck = c[k];
            if (certified_unsat) tmp_lits.push(ck);
            if (value(ck) == l_True)
                break;
            // Lazy unwatched literal elimination
            if (lazy_uw_lit_elim && l > 1 && (implies(ck, c[0]) || implies(ck, c[1]))) {
                c.learnt() ? lazy_rm_uw_lrn_lits++ : lazy_rm_uw_cla_lits++;
                continue;
            }
            // Lazy clause probing
            if (lazy_cla_probing && comm != lit_Error && probedValue(ck) != l_False) {
                Lit r = ~getCommonPremise(~ck, ~comm);
                if (r != lit_Error)
                    comm = r;
                else if (antr == lit_Error) {   // r == lit_Error
                    if (implies(ck, ~comm))
                        antr = ~comm;
                    else
                        antr = ~premises[toInt(~ck)];
                    aidx = l;
                }
                else
                    comm = antr = lit_Error;
            }
            if (amo && paid != NO_AMO) {
                if (amo_id[toInt(ck)] != paid) {
                    if (amo_id[toInt(~ck)] == paid && nglt == lit_Undef)
                        nglt = ck;
                    else
                        paid = NO_AMO;
                }
            }
            c[l++] = ck;
        }
        if (k < c.size()) {
            if (certified_unsat) {  // restore the clause
                while (++k < c.size())
                    tmp_lits.push(c[k]);
                for (int m=0; m < tmp_lits.size(); m++)
                    c[m] = tmp_lits[m];
            }
            removeClause(cs[i]);
        }
        else {
            c.shrink(k - l);
            cs[j++] = cs[i];

            // Apply the result of lazy clause probing
            if (lazy_cla_probing && comm != lit_Error && antr == lit_Error)
                addProbedLit(comm, PRB_CLAUSE);
            if (lazy_cla_probing && comm != lit_Error && antr != lit_Error) {
                if (comm == ~antr) {
                    if (lazy_eqv_probing) {
                        putEquivLit(antr, c[aidx]);
                        if (c.size() == 2) {
                            assert(aidx == 1);
                            putEquivLit(~antr, c[0]);
                        }
                    }
                }
            }
            if (amo && paid != NO_AMO) {
                if (nglt == lit_Undef && at_most_one[paid].size() > c.size()) {
                    incTouchComps();
                    for (int i=0; i < c.size(); i++)
                        touch_time[toInt(c[i])] = touch_comps;
                    vec<Lit>& ps = at_most_one[paid];
                    for (int i=0; i < ps.size(); i++)
                        if (touch_time[toInt(ps[i])] != touch_comps)
                            addProbedLit(~ps[i], PRB_AMO);
                }
                else if (nglt != lit_Undef)
                    addProbedLit(nglt, PRB_AMO);
            }

            if (certified_unsat && k > l) {
                writeClause(c);
                writeDeletedLits(tmp_lits);
            }
        }
    }
    cs.shrink(i - j);
}

// added by nabesima
bool Solver::rewriteEqLits() {
    assert(lazy_eqv_probing);
    assert(decisionLevel() == 0);

    if (eq_vars == rewrited_vars ||
            (eq_vars - rewrited_vars < nFreeVars() * rw_min_lits && (rw_min_starts == 0 || starts <= rw_last_starts + rw_min_starts)))
        return true;

    double cpu_time = cpuTime();

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    vec<vec<Lit> > elim_clauses;    // for certified-unsat
    bool no_conf = true;
    detachAllClauses();
    no_conf &= rewriteEqLits(clauses, rw_clause_lits, rw_taut_clauses, rw_unit_clauses, elim_clauses);
    no_conf &= rewriteEqLits(learnts, rw_learnt_lits, rw_taut_learnts, rw_unit_learnts, elim_clauses);
    if (rm_simulate)
        no_conf &= rewriteEqLits(rm_learnts, rw_learnt_lits, rw_taut_learnts, rw_unit_learnts, elim_clauses);
    attachAllClauses();

    // After rewriting, delete original clauses.
    if (certified_unsat)
        for (int i=0; i < elim_clauses.size(); i++)
            if (elim_clauses.size() > 2)
                writeDeletedLits(elim_clauses[i]);

    // Inactivate equivalent variables except for representative ones.
    for (int i=0; i < eq_lits.size(); i++) {
        EqLits& lits = eq_lits[i];
        if (lits.size() == 0) continue;
        Lit p = lits.delegate();
        vec<Lit> pos, neg, undef;
        for (int j=0; j < lits.size(); j++) {
            if (lits[j] != p) {
                setDecisionVar(var(lits[j]), false);
                rewrited[var(lits[j])] = true;
            }
            if (value(lits[j]) == l_True) pos.push(lits[j]);
            else if (value(lits[j]) == l_False) neg.push(lits[j]);
            else undef.push(lits[j]);
        }
        if (!decision[var(p)]) {
            setDecisionVar(var(p), true);
            elim_dec_vars--;
        }
        if (pos.size() > 0 && neg.size() > 0)
            ok = no_conf = false;
    }

    if (!ok || propagate() != CRef_Undef)
        ok = no_conf = false;

    checkGarbage();
    rebuildOrderHeap();

    rewrite_dbs++;
    rewrited_vars = eq_vars;
    rw_last_starts = starts;
    if (verbosity) printProgress('e');
    rewrite_time += cpuTime() - cpu_time;
    return no_conf;
}
bool Solver::rewriteEqLits(vec<CRef>& cs, uint64_t& rw_lits, uint64_t& tauts, uint64_t& units, vec<vec<Lit> >& elim_clauses)
{
    assert(lazy_eqv_probing);

    int i, j;
    for (i = j = 0; i < cs.size(); i++) {
        Clause& c = ca[cs[i]];

        // Locked clauses are used as reasons for propagated literals at DLV 0.
        if (locked(c)) { cs[j++] = cs[i]; continue; }

        incTouchComps();
        Lit  comm = lazy_simp ? ~premises[toInt(~c[0])] : lit_Error;
        int  paid = amo ? amo_id[toInt(c[0])] : NO_AMO;    // positive amo id
        Lit  nglt = lit_Undef;
        bool modified = false;
        if (certified_unsat) tmp_lits.clear();
        int  k, l;
        for (k = l = 0; k < c.size(); k++) {
            Lit from = c[k];
            Lit to   = getDelegate(from);
            if (certified_unsat) tmp_lits.push(from);
            assert(to != lit_Undef);

            // Lazy unwatched literal elimination
            if (lazy_uw_lit_elim && l > 1 && (implies(to, c[0]) || implies(to, c[1]))) {
                c.learnt() ? lazy_rm_uw_lrn_lits++ : lazy_rm_uw_cla_lits++;
                continue;
            }
            // duplicated literals.
            if (touch_time[toInt(to)] == touch_comps)
                continue;
            // tautological clause.
            if (touch_time[toInt(~to)] == touch_comps) {
                tauts++;
                break;
            }

            if (from != to) {
                rw_lits++;
                modified = true;
            }

            c[l++] = to;
            touch_time[toInt(to)] = touch_comps;

            // Lazy clause probing
            if (lazy_cla_probing && comm != lit_Error && probedValue(to) != l_False)
                comm = ~getCommonPremise(~to, ~comm);
            if (amo && paid != NO_AMO) {
                if (amo_id[toInt(to)] != paid) {
                    if (amo_id[toInt(~to)] == paid && nglt == lit_Undef)
                        nglt = to;
                    else
                        paid = NO_AMO;
                }
            }
        }

        if (k < c.size()) {
            if (certified_unsat) {  // restore the clause
                while (++k < c.size())
                    tmp_lits.push(c[k]);
                for (int m=0; m < tmp_lits.size(); m++)
                    c[m] = tmp_lits[m];
            }
            removeClauseNoDetach(cs[i]);
        }
        else {
            c.shrink(k - l);

            if (certified_unsat && (k > l || modified)) {
                writeClause(c);
                elim_clauses.push();
                tmp_lits.copyTo(elim_clauses.last());
            }

            if (c.size() > 1)
                cs[j++] = cs[i];
            else if (c.size() == 0)
                ok = false;
            else {
                assert(c.size() == 1);
                if (value(c[0]) == l_False)
                    ok = false;
                else if (value(c[0]) == l_Undef) {
                    assert(!rewrited[var(c[0])]);
                    uncheckedEnqueue(c[0]);
                    units++;
                }
                removeClauseNoDetach(cs[i]);
            }
            // Apply the result of lazy clause probing
            if (lazy_cla_probing && comm != lit_Error)
                addProbedLit(comm, PRB_CLAUSE);
            if (amo && paid != NO_AMO) {
                if (nglt == lit_Undef && at_most_one[paid].size() > c.size()) {
                    incTouchComps();
                    for (int i=0; i < c.size(); i++)
                        touch_time[toInt(c[i])] = touch_comps;
                    vec<Lit>& ps = at_most_one[paid];
                    for (int i=0; i < ps.size(); i++)
                        if (touch_time[toInt(ps[i])] != touch_comps)
                            addProbedLit(~ps[i], PRB_AMO);
                }
                else if (nglt != lit_Undef)
                    addProbedLit(nglt, PRB_AMO);
            }
        }
    }
    cs.shrink(i - j);

    return ok;
}

void Solver::rebuildOrderHeap(bool rand)
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    if (rand) shuffle(vs, random_seed);    // added by nabesima
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify(bool rebuild)
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;
    // added by nabesima
    if (0 < starts && simp_last_starts + simp_min_starts > starts)
        return true;

    double cpu_time = cpuTime();

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();

    // modified by nabesima
    //rebuildOrderHeap();
    if (rebuild)
        rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)
    // added by nabesima
    simp_last_starts = starts;
    simp_dbs++;
    simplify_time += cpuTime() - cpu_time;

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts.
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int       backtrack_level;
    bool      asserted = false;                        // added by nabesima
    int	      lbd;                                     // added by nabesima
    int       conflictC = 0;
    int       decisionC = 0;                           // added by nabesima
    int64_t	  old_propC = 0;                           // added by nabesima
    int64_t	  cur_propC = 0;                           // added by nabesima
    int       dec_restart_limit = dec_queue_size;      // added by nabesima
    vec<Lit>  learnt_clause;
    starts++;

    // added by nabesima
    if (inc_var_decay_finished && inc_rst_rate_finished && inst_check && inst_type == INS_UNDEF && conflicts >= (uint64_t)inst_check) {
        double blk_size   = ((double)global_lits / conflicts) / ((double)global_LBDs / conflicts);
        if (blk_size < small_block) {
            double restart_speed = (double)conflicts / starts;
            if (restart_speed > slow_restart_speed) {
                inst_type        = INS_HARD_SLOW;
                restart_strategy = slow_restart_strategy;
                lbd_restart_rate = slow_lbd_restart_rate;
                dec_restart_rate = slow_dec_restart_rate;
                lbd_queue_size   = slow_lbd_queue_size;
                var_decay_mode   = slow_var_decay_mode;
                var_decay        = slow_var_decay;
                core_lbd_threshold    = slow_glue_threshold;
                phase_saving     = slow_phase_saving;
                if (verbosity) printProgress('S');
            }
            else if (restart_speed < fast_restart_speed) {
                inst_type        = INS_HARD_FAST;
                restart_strategy = fast_restart_strategy;
                lbd_restart_rate = fast_lbd_restart_rate;
                dec_restart_rate = fast_dec_restart_rate;
                lbd_queue_size   = fast_lbd_queue_size;
                var_decay_mode   = fast_var_decay_mode;
                var_decay        = fast_var_decay;
                core_lbd_threshold    = fast_glue_threshold;
                phase_saving     = fast_phase_saving;
                if (verbosity) printProgress('F');
            }
        }
        if (inst_type == INS_UNDEF) {
            inst_type        = INS_NORMAL;
            restart_strategy = nrml_restart_strategy;
            lbd_restart_rate = nrml_lbd_restart_rate;
            dec_restart_rate = nrml_dec_restart_rate;
            lbd_queue_size   = nrml_lbd_queue_size;
            var_decay_mode   = nrml_var_decay_mode;
            var_decay        = nrml_var_decay;
            core_lbd_threshold    = nrml_glue_threshold;
            phase_saving     = nrml_phase_saving;
            if (verbosity) printProgress('N');
        }
        local_LBDs.init(lbd_queue_size);
        if (verbosity) {
            printStats(" I");
            printProgressHeader();
        }
    }

    // added by nabesima
    local_LBDs.clear();

    // added by nabesima
    if (lazy_simp)
        if (!assignProbedLits() || conflict_probing)
            return l_False;

    // added by nabesima
    if (lazy_eqv_probing)
        if (!rewriteEqLits())
            return l_False;


    if (amo && starts % amo_starts == 0)
        detectAMO();

    for (;;){

        old_propC  = propagations;                // added by nabesima
        CRef confl = propagate();
        cur_propC += propagations - old_propC;    // added by nabesima

        if (confl != CRef_Undef){

            // CONFLICT
            conflicts++; conflictC++;

            // glucose3's heuristics. Effective for SAT!
            if (!inc_var_decay_finished) {
                if (conflicts % inc_var_decay_base == 0)
                    var_decay += 0.01;
                if (inc_var_decay_confs <= conflicts) {
                    inc_var_decay_finished = true;
                    nrml_var_decay = var_decay;
                    if (verbosity) printProgress('f');
                }
            }

            // added by nabesima
            if (!inc_rst_rate_finished) {
                if (inc_lbd_rst_rate_base > 0 && conflicts % inc_lbd_rst_rate_base == 0)
                    lbd_restart_rate += 0.01;
                if (inc_dec_rst_rate_base > 0 && conflicts % inc_dec_rst_rate_base == 0)
                    dec_restart_rate += 0.01;
                if (inc_rst_rate_confs <= conflicts) {
                    inc_rst_rate_finished = true;
                    nrml_lbd_restart_rate = lbd_restart_rate;
                    nrml_dec_restart_rate = dec_restart_rate;
                    if (verbosity) printProgress('F');
                }
            }

            // added by nabesima
            if (!rm_simulate || !ca[confl].removed())
                ca[confl].used(true);
            else
                ca[confl].rm_used(true);

            // added by nabesima
            if (!asserted) dec_confs++;

            // added by nabesima
            stat_DLVs.push(decisionLevel());
            stat_trails.push(trail.size());
            local_trails.push(trail.size());
            max_trails = std::max(max_trails, trail.size());
            // added by nabesima
            if (local_LBDs.ready()) {
                bool blocked = false;
                if (restart_blocking == RBK_TRAIL && local_trails.ready() && trail.size() * blk_restart_rate > local_trails.average())
                    blocked = true;
                else if (restart_blocking == RBK_PROPS_CONF && (double)cur_propC / conflictC * blk_restart_rate > (double)propagations / conflicts)
                    blocked = true;
                else if (restart_blocking == RBK_AGILITY && agility >= blk_restart_rate)
                    blocked = true;
                else if (restart_blocking == RBK_MAX_TRAIL && trail.size() >= max_trails * blk_restart_rate)
                    blocked = true;
                else if (restart_blocking == RBK_PROPS_MAX_TRAIL &&
                        (double)cur_propC / conflictC * 0.5 > (double)propagations / conflicts &&
                        trail.size() >= max_trails * blk_restart_rate)
                    blocked = true;

                if (blocked) {
                    local_LBDs.wait((int)(lbd_queue_size * blk_restart_weight));
                    dec_restart_limit = conflictC + dec_queue_size;
                    blocked_restarts++;
                    last_blocked = starts;
                }
            }

            if (decisionLevel() == 0)
                return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level, lbd);

            //printLits(learnt_clause);

            // added by nabesima
            max_len_learnt = std::max(max_len_learnt, (uint32_t)learnt_clause.size());
            max_lbd_learnt = std::max(max_lbd_learnt, (uint32_t)lbd);
            global_DLVs   += decisionLevel();
            global_width  += (double)(trail.size() - trail_lim[0]) / decisionLevel();
            global_lits   += learnt_clause.size();
            global_LBDs   += lbd;
            backjump_dist += decisionLevel() - backtrack_level;
            local_LBDs.push(lbd);
            //has_glue |= (lbd <= glue_threshold);
            //has_glue = (lbd <= glue_threshold);
            //printf("%" PRIu64 ": local_glues = %f\n", starts, local_glues.average());
            learnts_len.inc(learnt_clause.size());
            learnts_lbd.inc(lbd);

            cancelUntil(backtrack_level);

            // added by nabesima
            if (certified_unsat) writeLits(learnt_clause);

            // added by nabesima
            if (conflict_probing) return l_False;

            if (learnt_clause.size() == 1) {
                assert(value(learnt_clause[0]) == l_Undef && backtrack_level == 0);
                assert(!lazy_simp || !rewrited[var(learnt_clause[0])]);
                uncheckedEnqueue(learnt_clause[0]);
            } else {
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);

                // added by nabesima
                Clause &c = ca[cr];
                assert(lbd > 0);
                c.lbd(lbd);
                if (rdb_eval == RDB_LBD_CVR) {
                    if (core_lbd_period && c.lbd() <= core_lbd_threshold)
                        c.ttl(core_lbd_period);
                    if (supp_lbd_period && core_lbd_threshold < c.lbd() && c.lbd() <= supp_lbd_threshold)
                        c.ttl(supp_lbd_period);
                    if (othr_lbd_period && supp_lbd_threshold < c.lbd())
                        c.ttl(othr_lbd_period);
                }

                attachClause(cr);
                claBumpActivity(c);

                // added by nabesima
                Lit p = premise(var(learnt_clause[1]));
                if (lazy_simp) {
                    for (int i=2; i < learnt_clause.size(); i++)
                        if (p != premise(var(learnt_clause[i]))) {
                            p = lit_Undef;
                            break;
                        }
                }

                assert(value(learnt_clause[0]) == l_Undef);
                assert(!lazy_simp || !rewrited[var(learnt_clause[0])]);
                uncheckedEnqueue(learnt_clause[0], cr, p);

                // reset the "used" flag of the first propagation
                c.used(false);
            }

            // modified by nabesima
            varDecayActivity();
            claDecayActivity();

            // added by nabesima
            asserted = true;

            // modified by nabesima
            //if (--learntsize_adjust_cnt == 0){
            if (rdb_call == RDB_CALL_MINISAT && --learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;
                // modified by nabesima
//                if (verbosity >= 1) {
//                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
//                           (int)conflicts,
//                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
//                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
//                }
            }

            // added by nabesima
            if (rand_rebuild && conflicts % rand_rebuild_confs == 0)
                rebuildOrderHeap(true);

            if (conflicts >= next_progress_report) {
                if (verbosity) printProgress();
                progress_report_base *= progress_report_inc;
                next_progress_report += progress_report_base;
            }

        }else{
            // NO CONFLICT

            // modified by nabesima
            bool restart = false;
            switch (restart_strategy) {
            case RST_NONE:
                break;
            case RST_MINISAT: {  // Minisat version
                if (nof_conflicts >= 0 && conflictC >= nof_conflicts)
                    restart = true;
                break;
            }
            // Glucose version
            case RST_LBD: {
                if (local_LBDs.ready() && local_LBDs.average() * lbd_restart_rate > (double)global_LBDs / conflicts)
                    restart = true;
                break;
            }
            case RST_DEC: {
                if (conflictC >= dec_restart_limit && (double)decisionC / conflictC * dec_restart_rate > (double)decisions / conflicts)
                    restart = true;
                break;
            }
            case RST_LBD_DEC: {
                if (local_LBDs.ready() && local_LBDs.average() * lbd_restart_rate > (double)global_LBDs / conflicts)
                    restart = true;
                else if (conflictC >= dec_restart_limit && (double)decisionC / conflictC * dec_restart_rate > (double)decisions / conflicts)
                    restart = true;
                break;
            }
            default:
                assert(false);
                /* no break */
            }

            if (restart || !withinBudget()) {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0, true);
                return l_Undef; }

            // Simplify the set of problem clauses:
            // modified by nabesima
            //if (decisionLevel() == 0 && !simplify())
            if (decisionLevel() == 0 && !simplify(simp_rebuild))
                return l_False;

            // modified by nabesima
            switch (rdb_call) {
            case RDB_CALL_NONE: break;
            case RDB_CALL_MINISAT:
                if (learnts.size() - nAssigns() >= max_learnts && (!lv0_reduce_db || decisionLevel() == 0)) { // Minisat version
                    if (verbosity) printProgress('r');    // added by nabesima
                    reduceDB();    // Reduce the set of learnt clauses:
                    if (verbosity) printProgress('R');    // added by nabesima
                }
                break;
            case RDB_CALL_AGGRESSIVE:
                if (nLearnts() >= max_learnts && (!lv0_reduce_db || decisionLevel() == 0)) {  // glucose 1.0 version
                    if (verbosity) printProgress('r');    // added by nabesima
                    max_learnts = nLearnts() * rdb_ub + reduce_db_base + reduce_db_inc * reduce_dbs;
                    reduceDB();    // Reduce the set of learnt clauses:
                    if (verbosity) printProgress('R');    // added by nabesima
                }
                break;
            case RDB_CALL_QUADRATIC:
                if (conflicts >= next_conflicts && (!lv0_reduce_db || decisionLevel() == 0)) {  // glucose 1.0 version
                    if (verbosity) printProgress('r');    // added by nabesima
                    reduceDB();
                    next_conflicts += reduce_db_base + reduce_db_inc * reduce_dbs;
                    if (verbosity) printProgress('R');    // added by nabesima
                }
                break;
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                decisionC++;    // added by nabesima
                next = pickBranchLit();

                if (next == lit_Undef) {
                    //printDecisionStack();
                    // Model found:
                    return l_True;
                }
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            assert(!lazy_simp || !rewrited[var(next)]);
            uncheckedEnqueue(next);

            // added by nabesima
            asserted = false;
        }
    }
    // added by nabesima to supress warning message.
    assert(false);
    return l_Undef;
}

// added by nabesima
inline bool Solver::assignProbedLits() {
    assert(decisionLevel() == 0);
    if (conflict_probing)
        return false;
    if (probed_lits_queue.size() == 0 ||
            (probed_lits_queue.size() < nFreeVars() * pr_min_lits && (pr_min_starts == 0 || starts <= pr_last_starts + pr_min_starts)))
        return true;
    assign_probed_lits++;

    for (int i=0; i < probed_lits_queue.size() && !conflict_probing; i++) {
        Lit p = probed_lits_queue[i];
        Var v = var(p);
        if (rewrited[v]) continue;
        if (value(p) == l_Undef) {
            uncheckedEnqueue(p);
            num_proped_lits[probed_types[v]]++;
            if (propagate() != CRef_Undef)
                conflict_probing = true;
        }
        else if (value(p) == l_False)
            conflict_probing = true;

        if (conflict_probing) break;
        if (!lazy_simp) continue;

        // Premise chain
        Lit q = premises[toInt(~p)];
        if (value(q) == l_Undef)
            addProbedLit(~q, PRB_PREMISE_CHAIN);
        else if (value(q) == l_True)
            conflict_probing = true;

        // Equivalent literals
        int id = lit2eq_lits[toInt(p)];
        if (id != NO_EQ_LITS) {
            EqLits& lits = eq_lits[abs(id)];
            for (int j=0; j < lits.size(); j++)
                addProbedLit(id > 0 ? lits[j] : ~lits[j], PRB_EQV_CHAIN);
        }
    }
    probed_lits_queue.clear();

    if (!conflict_probing)
        conflict_probing = !simplify(simp_rebuild);

    pr_last_starts = starts;
    if (verbosity) printProgress('p');

    return true;
}

double Solver::progressEstimate() const
{
    double  progress = 0;
    // modified by nabesima
    //double  F = 1.0 / nVars();
    double  F = 1.0 / dec_vars;

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    // modified by nabesima
    //return progress / nVars();
    return progress / dec_vars;
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    // added by nabesima
    if (bc_constraints.size() > 0)
        encodeBCConstraints();
    // added by nabesima
    if (init_vars == 0 && init_clauses == 0) {
        init_vars    = simp_vars    = nVars();
        init_clauses = simp_clauses = nClauses();
        simp_clauses_literals = clauses_literals;
    }

    if (sloped_var_decay) {
        if (nFreeVars() < max_var_decay_vars)
            var_decay = max_var_decay;
        else if (nFreeVars() > min_var_decay_vars)
            var_decay = min_var_decay;
        else {
            double a = (max_var_decay - min_var_decay) / (max_var_decay_vars - min_var_decay_vars);
            double b = max_var_decay - max_var_decay_vars * a;
            var_decay = a * nFreeVars() + b;
        }
        //nrml_var_decay = var_decay;
    }

    if (inc_var_decay) {
        inc_var_decay_base = inc_var_decay_period / ((var_decay - inc_var_decay_init) / 0.01);
        inc_var_decay_finished = false;
        var_decay = inc_var_decay_init;
    }

    if (inc_rst_rate) {
        switch (restart_strategy) {
        case RST_NONE:
        case RST_MINISAT:
            inc_rst_rate = false;
            break;
        case RST_LBD:
            inc_lbd_rst_rate_base = inc_rst_rate_period / ((lbd_restart_rate - inc_lbd_rst_rate_init) / 0.01);
            inc_rst_rate_finished = false;
            lbd_restart_rate = inc_lbd_rst_rate_init;
            break;
        case RST_DEC:
            inc_dec_rst_rate_base = inc_rst_rate_period / ((dec_restart_rate - inc_dec_rst_rate_init) / 0.01);
            inc_rst_rate_finished = false;
            dec_restart_rate = inc_dec_rst_rate_init;
            break;
        case RST_LBD_DEC:
            inc_lbd_rst_rate_base = inc_rst_rate_period / ((lbd_restart_rate - inc_lbd_rst_rate_init) / 0.01);
            inc_dec_rst_rate_base = inc_rst_rate_period / ((dec_restart_rate - inc_dec_rst_rate_init) / 0.01);
            inc_rst_rate_finished = false;
            lbd_restart_rate = inc_lbd_rst_rate_init;
            dec_restart_rate = inc_dec_rst_rate_init;
            break;
        default:
            assert(false);
        }
    }

    if (rand_attach) {
        detachAllClauses();
        attachAllClauses();
    }

    if (amo == AMO_DYNAMIC_STATIC)
        extractAMO();

    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;

    // added by nabesima
    if (max_learnts < reduce_db_base) {
        reduce_db_base = (uint64_t)((max_learnts/2 < 5000) ? 5000 : max_learnts/2);
        reduce_db_inc  /= 2;
    }
    if (rdb_call)
        max_learnts = reduce_db_base;


    if (verbosity >= 1){
        // modified by nabesima
//        printf("c     ================================[ Search Statistics ]================================\n");
//        printf("c     | Conflicts |     ORIGINAL     |          LEARNT          | Conf    Trail  Progress |\n");
//        printf("c     |           |    Vars  Clauses |    Limit  Clauses Lit/Cl |   DLVs    Size          |\n");
//        printf("c     =====================================================================================\n");
        printProgress();  // added by nabesima
    }

    // Search:
    lbool status        = l_Undef;
    int   curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        uint64_t prev_conflicts = conflicts;    // added by nabesima
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;

        // added by nabesima
        uint64_t confs = conflicts - prev_conflicts;
        min_confs = std::min(min_confs, confs);
        max_confs = std::max(max_confs, confs);
    }

    if (verbosity >= 1) {
        printProgress();  // added by nabesima
        // modified by nabesima
        //printf("c     =====================================================================================\n");
        printf("c\n");
    }

    if (status == l_True){
        // added by nabesima
        if (partial_model) makePartialModel();
        // Extend & copy model:
        model.growTo(nVars());

        // modified by nabesima
        //for (int i = 0; i < nVars(); i++) model[i] = value(i);
        if (!lazy_eqv_probing)
            for (int i = 0; i < nVars(); i++) model[i] = value(i);
        else {
            for (int i = 0; i < nVars(); i++) {
                Lit p = mkLit(i, false);
                Lit q = getDelegate(p);
                if (p == q || !rewrited[var(p)])
                  model[i] = value(p);
                else
                  model[i] = value(q);
            }
        }
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0, true);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;

    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    // added by nabesima
    // Unit clauses are added
    assert(decisionLevel() == 0);
    cnt += trail.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    // added by nabesima
    // Unit clauses are added
    for (int i = 0; i < trail.size(); i++){
        assert(value(trail[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(trail[i]) ? "-" : "", mapVar(var(trail[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    // added by nabesima
    if (bin_propagation) bin_watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            // added by nabesima
            if (bin_propagation) {
                vec<Watcher>& ws = bin_watches[p];
                for (int j = 0; j < ws.size(); j++)
                    ca.reloc(ws[j].cref, to);
            }
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);
        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // added by nabesima
    if (rm_simulate)
        for (int i = 0; i < rm_learnts.size(); i++)
            ca.reloc(rm_learnts[i], to);

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);

    // All order axioms. added by nabesima
    for (int i = 0; i < pos_oa.size(); i++) {
        if (pos_oa[i] != CRef_Undef) ca.reloc(pos_oa[i], to);
        if (neg_oa[i] != CRef_Undef) ca.reloc(neg_oa[i], to);
    }
    // added by nabesima
    if (verify_model)
        for (int i = 0; i < org_clauses.size(); i++)
            ca.reloc(org_clauses[i], to);

}

void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    //if (verbosity >= 2)  // modified by nabesima
    if (verbosity >= 5)
        printf("c     |  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

// added by nabesima
void Solver::makePartialModel() {
    //if (decisionLevel() == 0) return;
    for (int k=trail.size() - 1; k >= 0; k--) { // trail_lim[0]; k--) {
        Lit p = trail[k];

        // Since unit clauses are not added to database.
        if (level(var(p)) == 0 && reason(var(p)) == CRef_Undef)
            continue;

        lbool          old = assigns[var(p)];
        assigns[var(p)] = l_Undef;

        vec<Watcher>&  ws = watches[~p];
        Watcher        *i, *j, *end;
        bool            undef = false;
        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;) {
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True) { *j++ = *i++; continue; }

            CRef     cr = i->cref;
            Clause&  c  = ca[cr];

            if (c.learnt()) { *j++ = *i++; continue; }

            // Make sure the undef literal is data[1]:
            Lit undef_lit = p;
            if (c[0] == undef_lit)
                c[0] = c[1], c[1] = undef_lit;
            assert(c[1] == undef_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            if (first != blocker && value(first) == l_True) {
                *j++ = Watcher(cr, first); continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) == l_True) {
                    c[1] = c[k]; c[k] = undef_lit;
                    watches[~c[1]].push(Watcher(cr, c[k]));
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = Watcher(cr, first);
            // Copy the remaining watches:
            while (i < end)
                *j++ = *i++;
            undef = true;

        NextClause:;
        }
        ws.shrink(i - j);

        if (undef)
            assigns[var(p)] = old;
        else {
            shrinked_assignments++;
            //printf("**** shrinked "); printLit(p); printf(" *****\n");
        }
    }
}
void Solver::resetActivity(bool rand) {
    for (int i=0; i < nVars(); i++)
        activity[i] = rand ? drand(random_seed) * 0.00001 : 0;
    var_inc = 1;
    rebuildOrderHeap();
}

//=================================================================================================
// added by nabesima
struct CliqueGreaterThan {
    bool operator () (vec<Lit>* x, vec<Lit>* y) { return x->size() > y->size(); }
};
void Solver::extractAMO() {

    double cpu_time = cpuTime();

    // Collects binary clauses
    int num_bins = 0;
    vec<vec<int> > bins(nVars() * 2);
    for (int i=0; i < clauses.size(); i++) {
        Clause& c = ca[clauses[i]];
        if (c.size() != 2) continue;
        if (value(c[0]) == l_True || value(c[1]) == l_True) continue;
        int l1 = std::min(toInt(c[0]), toInt(c[1]));
        int l2 = std::max(toInt(c[0]), toInt(c[1]));
        bins[l1].push(l2);
        num_bins++;
    }
    if (num_bins > amo_max_bins) {
        if (verbosity) printf("c Skip extraction of cliques since %d bins exists (limit %d)\n", num_bins, amo_max_bins);
        return;
    }
    if (verbosity)
        printf("c Extracting maximal cliques from %d bins\n", num_bins);

    // Make input file to mace
    char bin_name[L_tmpnam];
    tmpnam(bin_name);
    FILE *fp = fopen(bin_name, "w");
    if (fp == NULL) {
        printf("c Error: can not open the temporary file '%s'.\n", bin_name);
        return;
    }
    for (int i=0; i < bins.size(); i++) {
        for (int j=0; j < bins[i].size(); j++)
            fprintf(fp, "%d ", bins[i][j]);
        fprintf(fp, "\n");
    }
    fclose(fp);

    // Execute mace to extract cliques
    char out_name[L_tmpnam];
    tmpnam(out_name);
    std::string cmd = std::string(mace_cmd) + " M -l 3 -, , " + std::string(bin_name) + " " + std::string(out_name) + " 2>&1";
    if (verbosity) printf("c  executing: %s\n", cmd.c_str());

    fp = popen(cmd.c_str(), "r");
    char log[128];
    while(fgets(log, 128, fp) != NULL)   // log
        if (verbosity) printf("c  > %s", log);
    pclose(fp);

    // Parse the results
    vec<vec<Lit> > cliques;
    std::ifstream fin(out_name);
    std::string line;
    while(fin >> line) {
        cliques.push();
        vec<Lit>& clique = cliques.last();
        std::stringstream ss(line);
        std::string item;
        while (std::getline(ss, item, ',')) {
            int num = std::atoi(item.c_str());
            clique.push(~toLit(num));
        }
    }

    std::remove(bin_name);
    std::remove(out_name);

    // Sort the results
    vec<vec<Lit>*> sorted_cliques;
    for (int i=0; i < cliques.size(); i++)
        sorted_cliques.push(&cliques[i]);
    sort(sorted_cliques, CliqueGreaterThan());

    // Select non-overlapped cliques
    at_most_one.clear();
    amo_sizes.clear();
    int num_selected = 0;
    vec<bool> covered(nVars() * 2);
    for (int i=0; i < sorted_cliques.size(); i++) {
        vec<Lit>& clique = *sorted_cliques[i];
        vec<Lit>  new_clique;
        for (int j=0; j < clique.size(); j++) {
            if (covered[toInt(clique[j])])
                continue;
            new_clique.push(clique[j]);
        }
        if (new_clique.size() < 3) continue;
        int id = at_most_one.size();
        for (int j=0; j < new_clique.size(); j++) {
            covered[toInt(new_clique[j])] = true;
            amo_id[toInt(new_clique[j])] = id;
        }
        num_selected++;
        amo_sizes.inc(new_clique.size());
        at_most_one.push();
        new_clique.moveTo(at_most_one.last());
    }
    for (int i=0; i < covered.size(); i++) {
        if (covered[i]) continue;
        Lit p = toLit(i);
        amo_id[toInt(p)] = at_most_one.size();
        at_most_one.push();
        at_most_one.last().push(p);
    }

    mace_time += cpuTime() - cpu_time;
    if (verbosity) printf("c  extracted %d/%d (%.3f %%) cliques (%d max/%.2f avg) using %.3f s\n", num_selected, cliques.size(), 100.0 * num_selected / cliques.size(), amo_sizes.max(), amo_sizes.avg(), mace_time);
}
void Solver::detectAMO() {
    assert(decisionLevel() == 0);
    double cpu_time = cpuTime();

    for (int i=0; i < at_most_one.size(); i++) {
        vec<Lit>& ps = at_most_one[i];

        // Remove falsified elements.
        if (ps.size() > 1) {
            int j, k;
            for (j = k = 0; j < ps.size(); j++) {
                if (value(ps[j]) == l_False) {
                    int new_aid = at_most_one.size();
                    at_most_one.push();
                    at_most_one.last().push(ps[j]);
                    amo_id[toInt(ps[j])] = new_aid;
                    continue;
                }
                else
                    ps[k++] = ps[j];
            }
            ps.shrink(j - k);
        }
        if (ps.size() == 0) continue;

        // Finds a common ancestor literal of ps.
        Lit p    = ps[0];
        Lit pp   = getDelegate(p);
        Lit comm = premises[toInt(~ps[0])];
        if (comm == ~ps[0] || at_most_one[amo_id[toInt(comm)]].size() >= 3)
            comm = lit_Undef;
        for (int j=1; j < ps.size(); j++) {
            if (comm != lit_Undef) {
                comm = getCommonPremise(~ps[j], comm);
                if (comm != lit_Undef && at_most_one[amo_id[toInt(comm)]].size() >= 3)
                    comm = lit_Undef;
            }
            Lit q  = ps[j];
            Lit qq = getDelegate(q);
            if (implies( p, q)) addProbedLit(~p, PRB_AMO);
            if (lazy_eqv_probing && implies(~p, q)) putEquivLit(~p, q, EQV_AMO);
            if (pp == qq) { addProbedLit(~pp,  PRB_AMO); addProbedLit(~qq, PRB_AMO); }
            else if (pp == ~qq)
                for (int k=1; k < ps.size(); k++)    // except for p
                    if (k != j)
                        addProbedLit(~ps[k], PRB_AMO);
        }

        // If it finds, move comm to ps.
        if (comm != lit_Undef && i != amo_id[toInt(comm)]) {
            vec<Lit>& qs = at_most_one[amo_id[toInt(comm)]];
            int j, k;
            for (j = k = 0; j < qs.size(); j++)
                if (qs[j] == comm)
                    continue;
                else
                    qs[k++] = qs[j];
            assert(j - k == 1);
            qs.shrink(j - k);
            amo_id [toInt(comm)] = i;
            ps.push(comm);

            if (lazy_eqv_probing) {
                Lit p  = comm;
                Lit pp = getDelegate(p);
                for (int j=0; j < ps.size() - 1; j++) {    // except for comm
                    Lit q  = ps[j];
                    Lit qq = getDelegate(q);
                    if (implies( p, q)) addProbedLit(~p, PRB_AMO);
                    if (lazy_eqv_probing && implies(~p, q)) putEquivLit(~p, q, EQV_AMO);
                    if (pp == qq) { addProbedLit(~pp,  PRB_AMO); addProbedLit(~qq, PRB_AMO); }
                    else if (pp == ~qq)
                        for (int k=0; k < ps.size() - 1; k++) // except for comm
                            if (k != j)
                                addProbedLit(~ps[k], PRB_AMO);
                }
            }
        }

        if (ps.size() < 3) continue;

        if (!amo_grp) continue;

        // Finds the merge target of ps.
        Lit source_lit = lit_Undef;
        Lit target_lit = lit_Undef;
        int target_aid = -1;
        int max_size   = INT32_MIN;
        for (int j=0; j < ps.size(); j++) {
            Lit p = ~premises[toInt(ps[j])];
            if (amo_id[toInt(ps[j])] == amo_id[toInt(p)]) continue;
            vec<Lit>& qs = at_most_one[amo_id[toInt(p)]];
            if (qs.size() < 3) continue;

            if (qs.size() > max_size) {
                source_lit = ps[j];
                target_lit = p;
                target_aid = amo_id[toInt(p)];
                max_size   = qs.size();
            }
        }

        if (target_aid == -1) continue;

        int new_aid = at_most_one.size();
        at_most_one.push();
        vec<Lit>& new_amo = at_most_one.last();
        for (int j=0; j < ps.size(); j++) {
            if (source_lit != ps[j]) {
                new_amo.push(ps[j]);
                amo_id[toInt(ps[j])] = new_aid;
            }
        }
        ps.clear();
        ps.push(source_lit);
        int qs_begin = new_amo.size();
        vec<Lit>& qs = at_most_one[amo_id[toInt(target_lit)]];
        for (int j=0; j < qs.size(); j++) {
            if (target_lit != qs[j]) {
                new_amo.push(qs[j]);
                amo_id[toInt(qs[j])] = new_aid;
            }
        }
        qs.clear();
        qs.push(target_lit);

        if (lazy_eqv_probing) {
            for (int j=0; j < qs_begin; j++) {
                Lit p  = new_amo[j];
                Lit pp = getDelegate(p);
                for (int k=qs_begin; k < new_amo.size(); k++) {
                    Lit q  = new_amo[k];
                    Lit qq = getDelegate(q);
                    if (implies( p, q)) addProbedLit(~p, PRB_AMO);
                    if (lazy_eqv_probing && implies(~p, q)) putEquivLit(~p, q, EQV_AMO);
                    if (pp == qq) { addProbedLit(~pp,  PRB_AMO); addProbedLit(~qq, PRB_AMO); }
                    else if (pp == ~qq) {
                        for (int l=0; l < new_amo.size(); l++)
                            if (l != j && l != k)
                                addProbedLit(~new_amo[l], PRB_AMO);
                        j = qs_begin;
                        break;
                    }
                }
            }
        }
    }

    // Remove empty elements
    int i, j;
    amo_sizes.clear();
    for (i=j=0; i < at_most_one.size(); i++) {
        uint32_t size = at_most_one[i].size();
        if (size == 0) continue;
        if (3 <= size) amo_sizes.inc(size);
        if (i != j) {
            vec<Lit>& src = at_most_one[i];
            vec<Lit>& dst = at_most_one[j];
            src.moveTo(dst);
            for (int k=0; k < dst.size(); k++)
                amo_id[toInt(dst[k])] = j;
        }
        j++;
    }
    at_most_one.shrink(i - j);

    // DEBUG
//        for (int i=0; i < at_most_one.size(); i++) {
//            if (at_most_one[i].size() <= 4) continue;
//            printf("amo %d: ", i); printLits(at_most_one[i]); printf("\n");
//        }

    amo_time += cpuTime() - cpu_time;
}
void Solver::propAMO(Lit p) {
    vec<Lit>& ps = at_most_one[amo_id[toInt(p)]];
    assert(ps.size() > 0);
    if (ps.size() == 1) return;
    int true_lits  = 0;
    int undef_lits = 0;
    tmp_lits.clear();
    for (int i=0; i < ps.size(); i++) {
        if (probedValue(ps[i]) == l_True)
            true_lits++;
        else if (probedValue(ps[i]) == l_Undef) {
            undef_lits++;
            tmp_lits.push(ps[i]);
        }
    }
    if (true_lits >= 2) { conflict_probing = true; return; }
    if (true_lits == 1) {
        if (undef_lits == 0) return;
        for (int i=0; i < tmp_lits.size(); i++)
            addProbedLit(~tmp_lits[i], PRB_AMO);
        return;
    }
}

int Solver::getAMOSize(const IntSet &item) const {
    int len = 0;
    for (int i=0; i < item.bucket_count(); i++) {
        for (int j=0; j < item.bucket(i).size(); j++) {
            int id = item.bucket(i)[j];
            len += at_most_one[id].size();
        }
    }
    return len;
}
int Solver::getMinAMOSize(const IntSet &item) const {
    int len = INT_MAX;
    for (int i=0; i < item.bucket_count(); i++) {
        for (int j=0; j < item.bucket(i).size(); j++) {
            int id = item.bucket(i)[j];
            if (at_most_one[id].size() < len)
                len = at_most_one[id].size();
        }
    }
    return len;
}

//=================================================================================================
// added by nabesima
void Solver::encodeBCConstraints() {
    for (int i=0; i < bc_constraints.size(); i++)
        encodeBCConstraint(bc_constraints[i]);
    bc_constraints.clear();
}
void Solver::encodeBCConstraint(BCConstraint& bcc) {
    //printf("encodeBCConstraint("); printLits(bcc.lits); printf(",%d,%d)\n", bcc.lb, bcc.ub);
    vec<Lit> output;
    encodeTotalizer(bcc.lits, output);
    for (int i=1; i <= bcc.lb; i++)
        addClause( output[i]);
    for (int i=bcc.ub + 1; i < output.size(); i++)
        addClause(~output[i]);
}
void Solver::encodeTotalizer(vec<Lit>& input, vec<Lit>& output) {
    if (input.size() == 1) {
        Lit head = mkLit(newVar(), false);
        Lit tail = mkLit(newVar(), false);
        addClause( head);
        addClause(~tail);
        assert(output.size() == 0);
        output.push(head);
        output.push(input[0]);
        output.push(tail);
        //printf("encodeTotalizer("); printLits(input); printf(") = "); printLits(output); printf("\n");
        return;
    }
    vec<Lit> l_input,  r_input;
    vec<Lit> l_output, r_output;
    int i;
    for (i=0; i < input.size() / 2; i++)
        l_input.push(input[i]);
    for (; i < input.size(); i++)
        r_input.push(input[i]);
    encodeTotalizer(l_input, l_output);
    encodeTotalizer(r_input, r_output);
    encodeUnaryAdder(l_output, r_output, output);
    //printf("encodeTotalizer("); printLits(input); printf(") = "); printLits(output); printf("\n");
}
void Solver::encodeUnaryAdder(vec<Lit>& as, vec<Lit>& bs, vec<Lit>& cs) {
    int num = as.size() + bs.size() - 4 + 2;    // -4 means aux lits for as and bs. +2 means new aux lits for cs.
    for (int i=0; i < num; i++)
        cs.push(mkLit(newVar(), false));
    addClause( cs[0]);
    addClause(~cs.last());
    for (int i=0; i < as.size() - 1; i++)
        for (int j=0; j < bs.size() - 1; j++) {
            addClause(~as[i  ], ~bs[j  ],  cs[i+j  ]);
            addClause( as[i+1],  bs[j+1], ~cs[i+j+1]);
        }
    //printf("encodeUnaryAdder("); printLits(as); printf(","); printLits(bs);  printf(") = "); printLits(cs); printf("\n");
}


//=================================================================================================
// Printing methods (added by nabesima):
void Solver::printLit(Lit l, bool detail) const {
    if      (l.x == lit_Undef.x) printf("undef");
    else if (l.x == lit_Error.x) printf("error");
    else if (detail) {
        printf("%s%d:%c(%c)%c", sign(l) ? "-" : "", var(l)+1,
                value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'),
                probedValue(l) == l_True ? '1' : (probedValue(l) == l_False ? '0' : 'X'),
                decision[var(l)] ? 'd' : 'n');
        if (value(l) != l_Undef) printf("@%d", level(var(l)));
    }
    else {
        printf("%s%d", sign(l) ? "-" : "", var(l)+1);
    }
}
void Solver::printLits(vec<Lit>& lits) const {
    for (int i=0; i < lits.size(); i++) {
        printLit(lits[i]);
        printf(" ");
    }
}
void Solver::printClause(const Clause& c) const {
    printf("{ ");
    for (int i=0; i < c.size(); i++) {
        printLit(c[i]);
        printf(" ");
    }
    printf("} ");
    if (c.learnt()) printf("lbd=%d ", c.lbd());
    if (c.has_extra()) printf("act=%f", c.activity());
    printf("\n");
}
void Solver::printSortedClause(const Clause& c) const {
    vec<Lit> lits;
    for (int i=0; i < c.size(); i++)
        lits.push(c[i]);
    sort(lits);
    printf("{ ");
    for (int i=0; i < lits.size(); i++) {
        printLit(lits[i]);
        printf(" ");
    }
    printf("} ");
    if (c.has_extra()) printf("act=%f", c.activity());
    printf("\n");
}
void Solver::printDecisionStack(int from) const {
    int idx = (from == 0) ? 0 : trail_lim[from-1];
    for (int i=from; i < decisionLevel(); i++) {
        printf("DLV%3d: ", i);
        for (; idx < trail_lim[i]; idx++) {
            printLit(trail[idx], false);
            printf(" ");
        }
        printf("\n");
    }
    printf("DLV%3d: ", decisionLevel());
    for (; idx < trail.size(); idx++) {
        printLit(trail[idx], false);
        printf(" ");
    }
    printf("\n");
}
void Solver::writeChar(unsigned char ch) const {
  if (putc_unlocked ((int) ch, certified_output) == EOF)
    exit(1);
}
void Solver::writeLit(Lit p) const {
    if (vbyte) {
        int n = 2*(var(p)+1) + sign(p);
        for (; n > 127; n >>= 7)
            writeChar(128 | (n & 127));
        writeChar(n);
    } else {
        int n = (var(p) + 1) * (-2 * sign(p) + 1);
        fprintf(certified_output, "%i ", n);
    }
}
void Solver::writeDelimiter() const {
    if (vbyte)
        writeChar(0);
    else
        fprintf(certified_output, "0\n");
}
void Solver::writeLits(vec<Lit>& lits) const {
    if (vbyte) writeChar('a');
    for (int i=0; i < lits.size(); i++)
        writeLit(lits[i]);
    writeDelimiter();
}
void Solver::writeUnit(Lit p) const {
    if (vbyte) writeChar('a');
    writeLit(p);
    writeDelimiter();
}
void Solver::writeBin(Lit p, Lit q) const {
    if (vbyte) writeChar('a');
    writeLit(p);
    writeLit(q);
    writeDelimiter();
}
void Solver::writeUniqBin(Lit p, Lit q) {
    int x = toInt(p);
    int y = toInt(q);
    if (x > y) { int tmp = x; x = y; y = tmp; }
    if (!bin_sets[x].has(y)) {
        bin_sets[x].add(y);
        writeBin(p, q);
    }
}
void Solver::writeClause(Clause& c) const {
    if (vbyte) writeChar('a');
    for (int i=0; i < c.size(); i++)
        writeLit(c[i]);
    writeDelimiter();
}
void Solver::writeDeletedLits(vec<Lit>& lits) const {
    if (vbyte) writeChar('d'); else fprintf(certified_output, "d ");
    for (int i=0; i < lits.size(); i++)
        writeLit(lits[i]);
    writeDelimiter();
}
void Solver::writeDeletedClause(Clause& c) const {
    if (vbyte) writeChar('d'); else fprintf(certified_output, "d ");
    for (int i=0; i < c.size(); i++)
        writeLit(c[i]);
    writeDelimiter();

}

