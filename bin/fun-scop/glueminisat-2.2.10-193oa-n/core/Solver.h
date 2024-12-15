/****************************************************************************************[Solver.h]
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

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "mtl/Queue.h"           // added by nabesima
#include "mtl/Select.h"          // added by nabesima
#include "mtl/IntSet.h"          // added by nabesima
#include "utils/Options.h"
#include "core/SolverTypes.h"

// added by nabesima
#ifndef __STDC_LIMIT_MACROS
#define __STDC_LIMIT_MACROS      // for INT32_MAX, ...
#endif
#ifndef __STDC_FORMAT_MACROS
#define __STDC_FORMAT_MACROS     // for PRIu64, ...
#endif
#include <stdint.h>              // for INT32_MAX, ...
#include <inttypes.h>            // for PRIu64, ...
#include <sys/time.h>
#include "core/FreqCounter.h"
#include "core/LocalVals.h"

namespace GlueMiniSat {

// The special ID for an empty equivalent literal set.
#define NO_EQ_LITS  0
// The type of detected equivalent literals
#define EQV_LAZY_SIMP        0
#define EQV_AMO              1

// Variable decaying strategy
#define DCY_FIXED            0
#define DCY_DEPTH            1

// Variable infomation
#define VINFO_NONE           0
#define VINFO_RM_PROP        1

//=================================================================================================
// Solver -- the main class:

class Solver {
public:

    // Constructor/Destructor:
    //
    Solver();
    virtual ~Solver();

    // Problem specification:
    // "virtual" is added by nabesima
    virtual Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

    virtual bool    addClause (const vec<Lit>& ps);                     // Add a clause to the solver.
    virtual bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    virtual bool    addClause (Lit p);                                  // Add a unit clause to the solver.
    virtual bool    addClause (Lit p, Lit q);                           // Add a binary clause to the solver.
    virtual bool    addClause (Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver.
    virtual bool    addClause_(      vec<Lit>& ps);                     // Add a clause to the solver without making superflous internal copy. Will
                                                                        // change the passed vector 'ps'.
    void addOrderAxiomDef(Var from, Var to);                            // Add a definition of order axioms. added by nabesima
    bool generateOrderAxioms();                                         // Generate order axioms from added definitions. added by nabesima


    // added by nabesima
    struct BCConstraint {
        vec<Lit> lits;
        int      lb, ub;
    };
    void    addBCConstraint(vec<Lit>& ps, int lb, int ub);

    // Solving:
    //
    //bool    simplify     ();                        // Removes already satisfied clauses.
    bool    simplify     (bool rebuild = true);     // Removes already satisfied clauses. modified by nabesima
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
    bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
    bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);

    // Variable mode:
    //
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value        (Var x)  const;       // The current value of a variable.
    lbool   value        (Lit p)  const;       // The current value of a literal.
    lbool   probedValue  (Var x)  const;       // The probed value of a literal. added by nabesima
    lbool   probedValue  (Lit p)  const;       // The probed value of a literal. added by nabesima
    lbool   modelValue   (Var x)  const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool   modelValue   (Lit p)  const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns     ()       const;       // The current number of assigned literals.
    int     nClauses     ()       const;       // The current number of original clauses.
    int     nLearnts     ()       const;       // The current number of learnt clauses.
    int     nVars        ()       const;       // The current number of variables.
    int     nFreeVars    ()       const;

    // Resource contraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // added by nabesima for gpw's interface.
    bool&    getOK            ()              { return ok;           }
    lbool    getAssign        (Var v  ) const { return assigns[v];   }
    Lit      getTrail         (int idx) const { return trail[idx];   }
    int      getTrailSize     ()        const { return trail.size(); }

    // added by nabesima
    void    setMiniSat22Params  ();
    void    setPartialModel     (bool b) { partial_model = b; }
    void    printOptions        ()                   const;
    void    printProblemStats   ()                   const;
    void    printProblemStats   (double parsed_time) const;
    void    printStats          ();
    void    printStats          (const char *prefix) const;
    void    printProgressHeader ()                   const;
    void    printProgress       (const char sign = ' ');

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    bool      parsing;            // True in parsing. added by nabesima
    int       verbosity;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      luby_restart;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.
    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    bool      native_oa;          // Native propagation for order axioms. added by nabesima

    // Statistics: (read-only member variable)
    //
    // modified by nabesima
    //uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t solves, starts, decisions, rnd_decisions, bin_decisions, propagations, oa_propagations, rm_propagations, conflicts, bin_conflicts, rm_conflicts;
    //uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;
    uint64_t dec_vars, clauses_literals, learnts_literals, tot_literals;

    // added by nabesima
    struct FreqDist {
        vec<uint64_t> freq;
        int           max_;
        uint64_t      sum;
        uint64_t      wsum;
        FreqDist(int sz=0) : max_(0), sum(0), wsum(0) { freq.growTo(sz + 1); }
        void     init (int sz){ freq.growTo(sz + 1); }
        void     clear()      { max_ = sum = wsum = 0; for (int i=0; i < freq.size(); i++) freq[i] = 0; }
        void     inc  (int n) { sum++; wsum += n; max_ = max_< n ? n : max_; n = n < freq.size() ? n : freq.size() - 1; freq[n]++; }
        void     dec  (int n) { sum--; wsum -= n; n = n < freq.size() ? n : freq.size() - 1; freq[n]--; }
        uint64_t get  (int n) const { n = n < freq.size() ? n : freq.size() - 1; return freq[n]; }
        double   rate (int n) const { return (double)get(n) / total(); }
        int      size ()      const { return freq.size(); }
        int      max  ()      const { return max_; }
        uint64_t total()      const { return sum; }
        double   avg  ()      const { return (double)wsum / sum; }
    };
    struct DynFreqDist {
        vec<uint64_t> freq;
        int           max_;
        uint64_t      sum;
        uint64_t      wsum;
        DynFreqDist() : max_(0), sum(0), wsum(0) {}
        void     clear()      { max_ = sum = wsum = 0; freq.clear(); }
        void     inc  (int n) { sum++; wsum += n; max_ = max_< n ? n : max_; freq.growTo(n+1); freq[n]++; }
        void     dec  (int n) { if (freq.size() <= n) return; sum--; wsum -= n; freq[n]--; }
        uint64_t get  (int n) const { return n < freq.size() ? freq[n] : 0; }
        double   rate (int n) const { return (double)get(n) / total() * 100.0; }
        double   trate(int n) const { return (double)total(n) / total() * 100.0; }
        int      size ()      const { return freq.size(); }
        int      max  ()      const { return max_; }
        uint64_t total()      const { return sum; }
        uint64_t total(int n) const { uint64_t t = 0; for (int i=0; i <= n; i++) t += get(i); return t; }
        double   avg  ()      const { return (double)wsum / sum; }
        double   stdev()      const { return sqrt(var()); }
        double   var  ()      const {
            double v = 0;
            for (int i=0; i < freq.size(); i++) v += freq[i] * i * i;
            return v / sum - avg() * avg();
        }
    };

    // statistics information added by nabesima
    double    real_stime;
    uint32_t  init_vars, simp_vars, unit_clauses, init_clauses, simp_clauses;
    uint64_t  simp_clauses_literals;
    uint64_t  max_confs, min_confs;
    uint64_t  blocked_restarts, last_blocked, supp_backjumps;
    uint64_t  enqueues;                // The number of enqueued literals
    uint64_t  dec_confs;               // The number of conflicts caused by a decision.
    uint64_t  tot_lbds;                // The total of LBDs of survived learnts.
    uint64_t  reduced_LBDs;            // The total of reduced LBDs.
    uint64_t  global_LBDs;             // The total of LBDs of every learnts (contains removed ones).
    uint64_t  global_lits;             // The total of literals of every learnts (contains removed ones).
    double    global_width;            // The total of average train width at every conflicts.
    uint64_t  global_DLVs;             // The total of decision level at every conflict.
    uint64_t  backjump_dist;           // The total of backjump distance.
    double    agility;                 // The agility of search process.
    uint32_t  max_len_learnt;          // The maximum length of a learnt.
    uint32_t  max_len_used_learnt;     // The maximum length of a used learnt for a propagation.
    uint32_t  max_lbd_learnt;          // The maximum LBD of a learnt.
    uint32_t  max_lbd_used_learnt;     // The maximum LBD of a used learnt for a propagation.
    uint64_t  rnd_polarities;          // The number of random polarity assignments.
    uint64_t  premise_updates;         // The number of changes of values in the premise array.
    uint64_t  rec_rm_lrn_lits;         // The number of removed literals by recursive minimization.
    uint64_t  bin_rm_lrn_lits;         // The number of removed literals by binary minimization.
    vec<uint32_t> num_probed_lits;     // The number of literals probed by each technique.
    vec<uint32_t> num_proped_lits;     // The number of propagated literals probed by each technique.
    uint64_t  lazy_rm_uw_cla_lits;     // The number of removed literals in clauses by unwatched literal elimination.
    uint64_t  lazy_rm_uw_lrn_lits;     // The number of removed literals in learnts by unwatched literal elimination.
    uint64_t  lazy_rm_pr_cla_lits;     // The number of removed literals in clauses by probed literal elimination.
    uint64_t  lazy_rm_pr_lrn_lits;     // The number of removed literals in learnts by probed literal elimination.
    uint64_t  lazy_lit_droppings;      // The number of success of literal dropping.
    uint64_t  lazy_drp_cla_lits;       // The number of dropped literals in clauses by literal dropping.
    uint64_t  lazy_drp_lrn_lits;       // The number of dropped literals in learnts by literal dropping.
    uint32_t  lazy_add_prop_bins;      // The number of added binary resolvents to produce new propagations.
    uint32_t  lazy_add_conf_bins;      // The number of added binary resolvents to produce new conflicts..
    uint32_t  assign_probed_lits;      // The number of assigning proped literals.
    double    lazy_bin_add_time;       // The cpu time of on-demand addition of binary resolvent.
    uint32_t  eq_vars;                 // The number of equivalent literals.
    uint32_t  eq_amo_vars;             // The number of equivalent literals detected from amo.
    uint32_t  rewrite_dbs;             // The number of rewriting clause database.
    uint64_t  rw_clause_lits;          // The number of rewrited literals in clauess.
    uint64_t  rw_learnt_lits;          // The number of rewrited literals in learnts.
    uint64_t  rw_taut_clauses;         // The number of rewrited tautological clauses.
    uint64_t  rw_taut_learnts;         // The number of rewrited tautological learnts.
    uint64_t  rw_unit_clauses;         // The number of unit clauses generated by rewriting.
    uint64_t  rw_unit_learnts;         // The number of unit learnts generated by rewriting.
    uint32_t  subsumed_clauses;        // The number of subsumed clauses.
    uint32_t  subsumed_learnts;        // The number of subsumed learnts.
    uint64_t  neck_cands;              // The number of bottleneck candidates.
    uint64_t  neck_preserved;          // The number of learnts preserved by neck-holding.
    uint32_t  simp_dbs;                // The number of calls for simplifing database.
    uint32_t  reduce_dbs;              // The number of calls for reducing database.
    FreqDist  learnts_len;             // The frequency distribution of length of learnt clauses.
    FreqDist  learnts_lbd;             // The frequency distribution of lbd of learnt clauses.
    FreqDist  lit_blk_sizes;           // The frequency distribution of literal block sizes.
    FreqDist  eq_vars_sizes;           // The frequency distribution of equivalent variable sets.
    FreqDist  amo_sizes;               // The frequency distribution of at-most-one constraints.
    DynFreqDist used_lbd;              // The frequency distribution of used LBDs.
    DynFreqDist used_clause_lbd;       // The frequency distribution of used clauses' LBDs.
    DynFreqDist unused_clause_lbd;     // The frequency distribution of unused clauses' LBDs.
    uint64_t  removed_learnts;         // The number of removed learnts.
    int       shrinked_assignments;    // The number of shrinked literals from a model.
    LocalVals<uint32_t> stat_DLVs;     // The bounded queue for storing local conflicting DLVs.
    LocalVals<uint32_t> stat_trails;   // The bounded queue for storing local trail sizes.
    double    simplify_time;           // The cpu time of simplifying clause database.
    double    rescale_time;            // The cpu time of variable activity rescaling.
    double    reduce_time;             // The cpu time of reducing clause database.
    double    rewrite_time;            // The cpu time of rewriting clause database.
    double    bin_min_time;            // The cpu time of binary minimization for learned clauses.
    double    mace_time;               // The cpu time of at-most-one constraints detection.
    double    amo_time;                // The cpu time of at-most-one constraints detection.
    double    php_time;                // The cpu time of pigeon hole principle application.

protected:

    // Helper structures:
    //
    // modified by nabesima
    //struct VarData { CRef reason; int level; };
    //static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }
    struct VarData {
        CRef      reason;
        int       level;
        Lit       premise;
        uint32_t  info;
    };
    static inline VarData mkVarData(CRef cr, int lv, Lit p = lit_Undef, uint32_t i = 0){ VarData d = {cr, lv, p, i}; return d; }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    // modified by nabesima
    //struct VarOrderLt {
    //    const vec<double>&  activity;
    //    bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
    //    VarOrderLt(const vec<double>&  act) : activity(act) { }
    //};
    struct VarOrderLt {
        const vec<double>&  activity;
        bool                allow_tie;
        bool operator () (Var x, Var y) const {
            if (allow_tie) return activity[x] > activity[y];
            if (activity[x] >  activity[y]) return true;
            if (activity[x] == activity[y] && x < y) return true;
            return false;
        }
        VarOrderLt(const vec<double>&  act, bool tie = true) : activity(act), allow_tie(tie) { }
    };

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    bool                solving;          // Whether the solver is solving or not. added by nabesima.
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           org_clauses;      // List of problem clauses for verification of the found model.
    vec<CRef>           learnts;          // List of learnt clauses.
    vec<CRef>           rm_learnts;       // List of removed learnt clauses for simulation of removal clauses.
    vec<BCConstraint>   bc_constraints;   // List of boolean cardinality constraints. added by nabesima
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
                        watches,          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
                        bin_watches;      // Watch lists for binary clauses. added by nabesima
    vec<lbool>          assigns;          // The current assignments.
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    ClauseAllocator     ca;

    // Options added by nabesima
    bool                partial_model;          // Generate a partial model if possible.
    bool                verify_model;           // Verify the found model.
    bool                bin_propagation;        // Propagations by binary clauses are preferred to longer clauses.
    int                 lrn_max_size;           // The maximum size required to minimize a learnt clause.
    bool                use_lazy_simp;          // Use lazy simplification techniques.
    int                 lazy_interval;          // The interval of lazy simplification.
    bool                lazy_fld_probing;       // Apply lazy failed-literal probing.
    bool                lazy_pol_probing;       // Apply lazy polarity probing.
    bool                lazy_nec_probing;       // Apply lazy necessary assignment probing.
    bool                lazy_eqv_probing;       // Apply lazy equivalent literal probing.
    bool                lazy_cla_probing;       // Apply lazy clause probing.
    int                 lazy_lrn_min;           // Apply learnt clause minimization by binary clauses or resolvents
    bool                lazy_uw_lit_elim;       // Apply lazy unwatched literal elimination.
    bool                lazy_pr_lit_elim;       // Apply lazy probed literal elimination.
    bool                lazy_lit_dropping;      // Apply lazy literal dropping.
    int                 lazy_bin_add;           // On-demand addition of binary resolvents.
    bool                probed_lit_chain;       // Identify values of literals propaated by probed ones.
    bool                lazy_simp;              // Use lazy simplification methods.
    double              pr_min_lits;            // The minimum rate of newly probed literals for propagation.
    int                 pr_min_starts;          // The minimum number of restarts for propagation of probed literals.
    double              rw_min_lits;            // The minimum rate of newly probed equivalent literals for rewriting.
    int                 rw_min_starts;          // The minimum number of restarts for rewriting.
    bool                rand_attach;            // Attach clauses by randomized order.
    bool                dec_elim;               // Perform decision variable elimination.
    int                 dec_elim_lim;           // Do not perform decision variable elimination if the estimeted number of resolvents > this value.
    int                 dec_elim_len;           // Do not perform decision variable elimination if the estimeted length of resolvents > this value.
    int                 amo;                    // Detect at-most-one constraints.
    bool                amo_grp;                // Apply grouping of at-most-one constraints.
    int                 amo_max_bins;           // Apply mace if the number of bins <= this value.
    int                 amo_starts;             // The restart period for detecting at-most-one constraints.
    const char*         mace_cmd;               // The path to mace.
    bool                allow_var_act_tie;      // Allow a tie of variable order.
    bool                rand_rebuild;           // Periodically rebuild variable order heap randomly.
    int                 rand_rebuild_confs;     // The inteval of random rebuild.
    bool                inc_var_decay;          // Increase variable decay factor in the initial search.
    uint32_t            inc_var_decay_period;   // The incremental var decay period in the number of conflicts.
    uint64_t            inc_var_decay_confs;    // The number of conflicts at which the annealing ends.
    int                 inc_var_decay_base;     // Base interval in annealing.
    double              inc_var_decay_init;     // Initial activity decay factor for incremental var decay
    bool                inc_var_decay_finished; // Whether the annealing period is finished.
    int                 var_decay_mode;         // Variable decaying strategy.
    double              var_decay_gain;         // The gain of sigmoid function for variable decaying strategy with depth.
    bool                sloped_var_decay;       // Variable decaying factor is based on the number of variables.
    double              max_var_decay;          // The maximum value of sloped var-decay.
    double              min_var_decay;          // The minimum value of sloped var-decay.
    int                 max_var_decay_vars;     // The number of variables in which the maximum var-decay is used.
    int                 min_var_decay_vars;     // The number of variables in which the minimum var-decay is used.
    bool                uip_bumping;            // Bump the uip for each conflict.
    bool                lbd_act_bumping;        // Bump variable activity implied from low-lbd learnts in conflict analysis.
    bool                rand_tiebreak;          // Randomly select a variable from top ranked ones.
    bool                simp_rebuild;           // Rebuild variable ordering heap in simplify.
    bool                oa_bin_dec;             // Apply binary search strategy for order encoded variables.
    int                 oa_bin_dec_lb;          // Lower-bound to apply binary search strategy for order encoded variables
    int                 restart_strategy;       // The restart strategy.
    int                 restart_blocking;       // Block the restart if local propagations per conflict exceeds global one.
    double              agility_decay;          // The agility decaying factor.
    double              lbd_restart_rate;       // Restart if local LBD average * this val < threashold.
    double              dec_restart_rate;       // Restart if local decisions/conflict average * this val < threashold.
    double              blk_restart_rate;       // Block if local trail average * this val > global one.
    int                 lbd_queue_size;         // The window size of local average for LBDs.
    int                 dec_queue_size;         // The window size of local average for decisions/conflict.
    int                 trl_queue_size;         // The window size of local trails.
    double              blk_restart_weight;     // The scale of wait time when restart is blocked.
    bool                inc_rst_rate;           // Increase restart-rate factor in the initial search.
    uint32_t            inc_rst_rate_period;    // The incremental restart-rate period in the number of conflicts.
    uint64_t            inc_rst_rate_confs;     // The number of conflicts at which the incremental restart-rate ends.
    int                 inc_lbd_rst_rate_base;  // Base interval in incremental LBD restart-rate.
    int                 inc_dec_rst_rate_base;  // Base interval in incremental DEC restart-rate.
    double              inc_lbd_rst_rate_init;  // Initial LBD restart-rate factor for incremental restart rate
    double              inc_dec_rst_rate_init;  // Initial DEC restart-rate factor for incremental restart rate
    bool                inc_rst_rate_finished;  // Whether the restart-rate incremental period is finished.
    bool                closed_lbd;             // Use closed-lbd for evaluation criteria of learnts.
    double              closed_lbd_rate;        // Decreasing rate of closed-lbd.
    bool                rm_simulate;            // Simulate removal of learnt clauses.
    int                 rdb_eval;               // The evaluation criteria of reduction strategy.
    int                 rdb_call;               // The call strategy of reduction.
    double              rdb_ub;                 // The upper-bound rate of reduction.
    double              core_lbd_coverage;      // The use-coverage of core learnt clauses.
    double              supp_lbd_coverage;      // The use-coverage of supplemental learnt clauses.
    int                 core_lbd_lb;            // The lower-bound of core LBD.
    int                 supp_lbd_lb;            // The lower-bound of support LBD.
    int                 core_lbd_threshold;     // Learnts whose LBD <= the threshold are survived.
    int                 supp_lbd_threshold;     // Learnts whose LBD <= the threshold are survived for the specified period.
    int                 core_lbd_period;        // The holding period of used corelearnt clauses.
    int                 supp_lbd_period;        // The holding period of used supplemental learnt clauses.
    int                 othr_lbd_period;        // The holding period of used other learnt clauses.
    int                 inc_lrn_limit;          // Increment the limit of learnt clauses if many better clauses exist.
    int                 frozen_lbd;             // Protect clauses if their LBD decrease and is lower than this threashold.
    int                 simp_min_starts;        // The minimum number of restarts for simplifying clause database.
    bool                rm_low_act_learnts;     // Remove learnt clauses whose activity is low.
    bool	            lv0_reduce_db;          // The reduce db is applied at DLV 0.
    int                 reduce_db_base;         // The initial reduce-DB limit.
    int                 reduce_db_inc;          // The factor with which the reduce-DB limit is added to the limit.
    int                 stats_conf_size;        // The base number of conflicts for statistics infomation.
    int                 max_stats_size;         // The size of statistics infomation.
    bool                use_minisat_param;      // Behaves as MiniSat 2.2.0.
    FILE*               certified_output;
    bool                certified_unsat;
    bool                vbyte;

    int                 num_csp_vars;           // The number of order encoded CSP variables.
    vec<Var>            sat2csp;                // Mapping from SAT variables to CSP variables.
    vec<CRef>           pos_oa;                 // Order axioms for positive propagation.
    vec<CRef>           neg_oa;                 // Order axioms for negative propagation.
    vec<Var>            csp_lb;                 // Lower-bound of csp variables
    vec<Var>            csp_ub;                 // Upper-bound of csp variables

    int                 inst_type;
    int                 inst_check;             // Check a given instance is hard when the specified number of conflicts occurs.
    double              small_block;            // The threashold of small block instances.
    // Restart strategy for slow instances.
    double              slow_restart_speed;
    int                 slow_restart_strategy;
    double              slow_lbd_restart_rate;
    double              slow_dec_restart_rate;
    int                 slow_lbd_queue_size;
    int                 slow_var_decay_mode;
    double              slow_var_decay;
    int                 slow_glue_threshold;
    int                 slow_phase_saving;
    // Restart strategy for fast instances.
    double              fast_restart_speed;
    int                 fast_restart_strategy;
    double              fast_lbd_restart_rate;
    double              fast_dec_restart_rate;
    int                 fast_lbd_queue_size;
    int                 fast_var_decay_mode;
    double              fast_var_decay;
    int                 fast_glue_threshold;
    int                 fast_phase_saving;
    // Restart strategy for normal instances.
    int                 nrml_restart_strategy;
    double              nrml_lbd_restart_rate;
    double              nrml_dec_restart_rate;
    int                 nrml_lbd_queue_size;
    int                 nrml_var_decay_mode;
    double              nrml_var_decay;
    int                 nrml_glue_threshold;
    int                 nrml_phase_saving;

    // added by nabesima
    struct EqLits {
        vec<Lit>   lits;
        Lit        delegate_;
        EqLits() : delegate_(lit_Undef) {}
        Lit        delegate    ()               const { assert(delegate_ != lit_Undef); return delegate_; }
        int        size        (void)           const { return lits.size(); }
        void       push        (const Lit& p)         { lits.push(p); if (lits.size() == 1) delegate_ = p; }
        void       eliminate   ()                     { lits.clear(true); delegate_ = lit_Undef; }
        const Lit& operator [] (int index)      const { return lits[index]; }
        Lit&       operator [] (int index)            { return lits[index]; }
    };

    // State data added by nabesima
    uint32_t            lbd_comps;              // The number of LBD computation.
    vec<uint32_t>       lbd_time;               // The counter to compute LBD score.
    vec<Lit>            implied_by_learnts;     // A set of literals implied by learnts.
    vec<Var>            non_dec_vars;           // A set of non decision variables.
    uint32_t            touch_comps;            // The number of touches.
    vec<uint32_t>       touch_time;             // The counter to identify touched literal.
    vec<int>            min_lbd;                // Min lbd for updating closed LBD.
    vec<uint64_t>       assigned_lits;          // The number of assignments for each literal.
    uint64_t            next_conflicts;         // The conflict threshold for reduction learnt clauses.
    bool                conflict_probing;       // True if a conflict occurs in probing.
    vec<lbool>          probed_vals;            // The set of probed truth values for each variable.
    vec<uint8_t>        probed_types;           // The set of probed types for each variable.
    vec<Lit>            probed_lits_queue;      // A set of newly probed literals.
    uint64_t            pr_last_starts;         // The number of restarts at when the last probed literals are found.
    vec<Lit>            premises;               // Premise literals for each literal in binary resolvents.
    vec<IntSet>         bin_sets;               // Sets of binary clauses for certified unsat.
    vec<Lit>            imp_conf_cands;         // A set of literals may invoke a new conflict from binary implications.
    vec<Lit>            eqv_conf_cands;         // A set of literals may invoke a new conflict from equivalent literals.
    vec<Lit>            imp_prop_cands;         // A set of literals may invoke new binary propagations on binary implications.
    vec<Lit>            eqv_prop_cands;         // A set of literals may invoke new binary propagations on equivalent literals.
    vec<int>            lit2eq_lits;            // The mapping from literals to the equivalent literal sets.
    vec<EqLits>         eq_lits;                // The mapping from literals to the equivalent literal sets.
    vec<char>           rewrited;               // Whether a variable is rewrited or not.
    uint32_t            rewrited_vars;          // The number of rewrited variables.
    uint64_t            rw_last_starts;         // The number of restarts at when last equivalent literals are found.
    uint64_t            simp_last_starts;       // The number of restarts at when last simplifying clause database is applied.
    uint32_t            elim_dec_vars;          // The number of eliminated decision variables.
    vec<Var>            eliminated_dec_vars;    // A set of eliminated decision variables.
    vec<vec<Lit> >      at_most_one;            // A set of at-most-one constraints.
    vec<vec<int> >      amo_groups;             // A set of groups of at-most-one constraints.
    vec<int>            amo_id;                 // The mapping from literals to at-most-one constraint IDs.
    vec<char>           white_nodes;            // A set of reason nodes.
    vec<vec<Lit> >      black_nodes;            // A set of literals for each decision level in a learned clause.
    LocalVals<uint32_t> local_LBDs;             // The bounded queue for storing local learnt's LBDs.
    LocalVals<uint32_t> local_trails;           // The bounded queue for storing local trail size.
    int                 max_trails;             // The maximum trail size.
    int                 num_progress_report;    // The number of progress printing.
    double              progress_report_base;   // The initial number of conflicts to report progress.
    double              progress_report_inc;    // The limit for reporting progress is multiplied with this factor.
    uint64_t            next_progress_report;   // The number of conflicts to report progress.

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // added by nabesima
    vec<char>           simp_seen;
    vec<Lit>            simp_seen_toclear;
    vec<char>           simp_reached;
    vec<Lit>            simp_reached_toclear;
    vec<Lit>            tmp_lits;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder     (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit      ();                                                      // Return the next decision variable.
    int      find_oa_lb         (int lb, int ub);                                        // Return the lower-bound of the specified range.
    int      find_oa_ub         (int lb, int ub);                                        // Return the upper-bound of the specified range.
    void     newDecisionLevel   ();                                                      // Begins a new decision level.
    Lit      decisionLit        (int lv) const;                                          // Return the decision literal at the level. added by nabesima
    Lit      lastDecisionLit    () const;                                                // Return the last decision literal. added by nabesima
    //void     uncheckedEnqueue   (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    void     uncheckedEnqueue   (Lit p, CRef from = CRef_Undef, Lit pre = lit_Undef, uint32_t info = 0);    // Enqueue a literal. Assumes value of literal is undefined.  modified by nabesima
    bool     enqueue            (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate          ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    bool     assignProbedLits   ();                                                      // Assigns probed literals.                                     added by nabesima
    void     lazyProbing        (Lit new_dom, Lit p);                                    // Apply lazy probing techniques.                               added by nabesima
    CRef     addBinsOnDemand    ();                                                      // Adds binary clauses on-demand.                               added by nabesima
    CRef     addBinLearnt       (Lit p, Lit q);                                          // Adds binary learnt clause p v q.                             added by nabesima
    void     addProbedLit       (Lit p, int type);                                       // Adds a probed literal to the probed literal cache.           added by nabesima
    void     putEquivLit        (Lit p, Lit q, int type = EQV_LAZY_SIMP);                // Put two equivalent literals in the table.                    added by nabesima
    // modified by nabesima
    //void     cancelUntil        (int level);                                             // Backtrack until a certain level.
    void     cancelUntil        (int level, bool restart = false);                       // Backtrack until a certain level.
    // modified by nabesima
    //void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel);    // (bt = backtrack)
    void     analyze            (CRef confl, vec<Lit>& out_learnt, int& out_btlevel, int& out_lbd);    // (bt = backtrack)
    void     analyzeFinal       (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant       (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    void     minimizeByPremises (vec<Lit>& ps);                                          // Minimize a learnt by binary self-subsumption checking.       added by nabesima
    lbool    search             (int nof_conflicts);                                     // Search for a given number of conflicts.
    lbool    solve_             ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB           ();                                                      // Reduce the set of learnt clauses.
    void     updateRDBThreshold ();                                                      // Updates threshold for reduction. added by nabesima.
    void     removeSatisfied    (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    bool     rewriteEqLits      ();                                                      // Rewrite equivalent literals in clauses into a representative one. added by nabesima
    bool     rewriteEqLits      (vec<CRef>& cs, uint64_t& rw_lits, uint64_t& taut_clas, uint64_t& fixed_vars, vec<vec<Lit> >& elim_clauses);
    // modified by nabesima
    //void     rebuildOrderHeap   ();
    void     rebuildOrderHeap   (bool rand=false);

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity   ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity    (Var v, double inc);     // Increase a variable with the current 'bump' value.
    void     varBumpActivity    (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity   ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity    (Clause& c);             // Increase a clause with the current 'bump' value.
    double   varMaxActivity     () const { return order_heap.size() > 0 ? activity[order_heap[0]] : 0.0; }  // added by nabesima
    double   varNthActivity     (double rate) const;     // Returns nth activity for free variables.  added by nabesima

    // Operations on clauses:
    //
    void     attachClause        (CRef cr);               // Attach a clause to watcher lists.
    void     attachAllClauses    ();                      // Attach all clauses and learnts. added by nabesima
    void     detachClause        (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     detachAllClauses    ();                      // Detach all clauses and learnts. added by nabesima
    void     removeClause        (CRef cr);               // Detach and free a clause.
    void     removeClauseNoDetach(CRef cr);               // Free a clause without detach. added by nabesima
    bool     locked              (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied           (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll            (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    int      level            (Var x) const;
    Lit      premise          (Var x) const; // added by nabesima
    int      varinfo          (Var x) const; // added by nabesima
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;

    // added by nabesima
    bool     implies            (Lit p, Lit q);
    Lit      getCommonPremise   (Lit x, Lit y);
    bool     hasConfPremise     (Lit x, Lit y);
    Lit      getDelegate        (Lit p)                   const;
    int      getLBD             (const Lit* ps, int size);
    int      getLBD             (vec<Lit>& ps)                  { return getLBD((Lit*)ps, ps.size());     }
    int      getLBD             (const Clause& c)               { return getLBD((const Lit*)c, c.size()); }
    int      getBacktrackLv     (Lit* ps, int size);
    int      getBacktrackLv     (vec<Lit>& ps)                  { return getBacktrackLv((Lit*)ps, ps.size()); }
    double   getSATPossibility  (Lit p)                   const;
    double   getSATPossibility  (const Clause& c)         const;
    void     incTouchComps      (int n = 1);
    void     makePartialModel   ();
    void     resetActivity      (bool rand);
    void     extractAMO         ();
    void     detectAMO          ();
    void     propAMO            (Lit p);
    int      getAMOSize         (const IntSet &item)      const;
    int      getMinAMOSize      (const IntSet &item)      const;
    void     encodeBCConstraints();
    void     encodeBCConstraint (BCConstraint& bcc);
    void     encodeTotalizer    (vec<Lit>& input, vec<Lit>& output);
    void     encodeUnaryAdder   (vec<Lit>& as, vec<Lit>& bs, vec<Lit>& cs);
    void     printLit           (Lit l, bool detail=true) const;
    void     printLits          (vec<Lit>& lits)          const;
    void     printClause        (const Clause& c)         const;
    void     printSortedClause  (const Clause& c)         const;
    void     printDecisionStack (int from=0)              const;
    void     writeChar          (unsigned char c)         const;
    //void     writeLit           (int n)                   const;
    void     writeLit           (Lit p)                   const;
    void     writeDelimiter     ()                        const;
    void     writeLits          (vec<Lit>& lits)          const;
    void     writeUnit          (Lit p)                   const;
    void     writeBin           (Lit p, Lit q)            const;
    void     writeUniqBin       (Lit p, Lit q);
    void     writeClause        (Clause& c)               const;
    void     writeDeletedLits   (vec<Lit>& lits)          const;
    void     writeDeletedClause (Clause& c)               const;



    // Static helpers:
    //

    // added by nabesima
    template<class T>
    inline static void shuffle(vec<T>& array, double seed) {
        // Fisher–Yates shuffle
        T tmp;
        for (int i = array.size() - 1; i > 0; i--) {
            int idx = irand(seed, i + 1);
            tmp = array[idx]; array[idx] = array[i]; array[i] = tmp;
        }
    }

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }
};


//=================================================================================================
// Implementation of inline methods:

inline CRef Solver::reason (Var x) const { return vardata[x].reason;  }
inline int  Solver::level  (Var x) const { return vardata[x].level;   }
// added by nabesima
inline Lit  Solver::premise(Var x) const { return vardata[x].premise; }
inline int  Solver::varinfo(Var x) const { return vardata[x].info;    }

inline void Solver::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() {
    // added by nabesima
    if (var_decay_mode == DCY_DEPTH) {
        double scale = (1.0 - nrml_var_decay) * 2.0;
        var_decay = 1.0 - scale + scale / (1 + exp(-decisionLevel() * var_decay_gain));
        if (var_decay > 0.9999)
            var_decay = 0.9999;
    }
    var_inc *= (1 / var_decay);
}
inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }
inline void Solver::varBumpActivity(Var v, double inc) {
    if ( (activity[v] += inc) > 1e100 ) {
        // Rescale:
        double cpu_time = cpuTime();
        // modified by nabesima
        //for (int i = 0; i < nVars(); i++)
        //   activity[i] *= 1e-100;
        for (int i = 0; i < nVars(); i++) {
            activity[i] *= 1e-100;
            if (!allow_var_act_tie && order_heap.inHeap(i))
                order_heap.update(i);
        }
        var_inc *= 1e-100;
        rescale_time += cpuTime() - cpu_time;
    }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v);
}

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts.size(); i++)
                ca[learnts[i]].activity() *= 1e-20;
            cla_inc *= 1e-20; } }
inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
// added by nabesima
inline void     Solver::addBCConstraint (vec<Lit>& ps, int lb, int ub) {
    bc_constraints.push();
    BCConstraint& bcc = bc_constraints.last();
    ps.copyTo(bcc.lits);
    bcc.lb = lb;
    bcc.ub = ub;
}

// modified by nabesima
//inline bool     Solver::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c; }
inline bool     Solver::locked          (const Clause& c) const {
    if (bin_propagation && c.size() == 2) {
        return (value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c) ||
               (value(c[1]) == l_True && reason(var(c[1])) != CRef_Undef && ca.lea(reason(var(c[1]))) == &c);
    }
    return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c;
}
inline void     Solver::newDecisionLevel()             { trail_lim.push(trail.size()); }
inline Lit      Solver::decisionLit     (int lv) const { assert(lv > 0); return trail[trail_lim[lv - 1]]; }
inline Lit      Solver::lastDecisionLit ()       const { return trail_lim.size() > 0 ? trail[trail_lim.last()] : lit_Undef; }

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    Solver::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver::probedValue   (Var x) const   { return probed_vals[x]; }
inline lbool    Solver::probedValue   (Lit p) const   { return probed_vals[var(p)] ^ sign(p); }
inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
// modified by nabesima
//inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size() + unit_clauses; }
inline int      Solver::nLearnts      ()      const   { return learnts.size(); }
inline int      Solver::nVars         ()      const   { return vardata.size(); }
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     Solver::setDecisionVar(Var v, bool b)
{
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}
inline void     Solver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver::interrupt(){ asynch_interrupt = true; }
inline void     Solver::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     Solver::withinBudget() const {
    return !asynch_interrupt &&
           (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     Solver::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     Solver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    Solver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

inline void     Solver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }

// added by nabesima
// Checks whether p implies q or not.
inline bool Solver::implies(Lit x, Lit y) {
    //p = getDelegate(p);
    //q = getDelegate(q);
    if (x == y) return true;  // x -> x
    Lit py = premises[toInt(y)];
    if (x == py) return true;  // x -> y
    Lit pnx = premises[toInt(~x)];
    if (~y == pnx || ~py == pnx) return true;  // ~y -> ~x  or  (py -> y and x -> py)
    return x == premises[toInt(py)] || ~y == premises[toInt(pnx)];  // x -> ? -> y  or  ~y -> ? -> ~x
}
inline Lit Solver::getCommonPremise(Lit x, Lit y) {
    //x = getDelegate(x);
    //y = getDelegate(y);
    if (x == y) return x;
    Lit px  = premises[toInt( x)];
    if (y == px) return y;
    Lit pny = premises[toInt(~y)];
    if (~x == pny) return y;
    Lit py  = premises[toInt( y)];
    if (x == py) return x;
    if (px == py) return px;
    Lit pnx = premises[toInt(~x)];
    if (~y == pnx) return x;
    if (~y == premises[toInt(~px)]) return px;
    if (~x == premises[toInt(~py)]) return py;
    return lit_Undef;
}
inline bool Solver::hasConfPremise(Lit x, Lit y) {
    //x = getDelegate(x);
    //y = getDelegate(y);
    if (x == ~y) return true;
    Lit px  = premises[toInt(x)];
    if (y == ~px) return true;
    Lit py  = premises[toInt(y)];
    if (x == ~py) return true;
    if (px == ~py) return true;
    if (y == ~premises[toInt(px)]) return true;
    if (x == ~premises[toInt(py)]) return true;
    return false;
}
inline Lit Solver::getDelegate(Lit p) const {
    int id = lit2eq_lits[toInt(p)];
    if (id == NO_EQ_LITS) return p;
    return id > 0 ? eq_lits[id].delegate() : ~eq_lits[-id].delegate();
}
inline int Solver::getLBD(const Lit* ps, int size) {
    lbd_comps++;
    if (lbd_comps == 0)
        for (int i=0; i < lbd_time.size(); i++)
            lbd_time[i] = UINT32_MAX;
    int lbd = 0;
    for (int i=0; i < size; i++) {
        int lv = level(var(ps[i]));
        if (lbd_time[lv] != lbd_comps) {
            lbd_time[lv] = lbd_comps;
            lbd++;
        }
    }
    return lbd;
}
inline int Solver::getBacktrackLv(Lit* ps, int size) {
    assert(size > 0);
    if (size == 1)
        return 0;

    int max_i = 1;
    // Find the first literal assigned at the next-highest level:
    for (int i = 2; i < size; i++)
        if (level(var(ps[i])) > level(var(ps[max_i])))
            max_i = i;
    // Swap-in this literal at index 1:
    Lit p     = ps[max_i];
    ps[max_i] = ps[1];
    ps[1]     = p;
    return level(var(p));
}
inline double Solver::getSATPossibility(Lit p) const {
    return (double)assigned_lits[toInt(p)] / (assigned_lits[toInt(p)] + assigned_lits[toInt(~p)]);
}
inline double Solver::getSATPossibility(const Clause& c) const {
    double p1st = getSATPossibility(c[0]);
    double p2nd = getSATPossibility(c[1]);
    if (p1st < p2nd) { double tmp = p1st; p1st = p2nd; p2nd = tmp; }
    for (int i=2; i < c.size(); i++) {
        double p = getSATPossibility(c[i]);
        if (p > p1st) {
            p2nd = p1st;
            p1st = p;
        }
        else if (p > p2nd)
            p2nd = p;
    }
    return p1st * p2nd;
}
inline void Solver::incTouchComps(int n) {
    if (touch_comps + n < touch_comps) {    // when overflow occurs
        for (int i=0; i < touch_time.size(); i++)
            touch_time[i] = 0;
        touch_comps = 0;
    }
    touch_comps += n;
}

//=================================================================================================
// Debug etc:


//=================================================================================================
}

#endif
