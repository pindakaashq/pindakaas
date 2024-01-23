#ifndef _ccadical_up_h_INCLUDED
#define _ccadical_up_h_INCLUDED

/*------------------------------------------------------------------------*/
#ifdef __cplusplus
extern "C" {
#endif
/*------------------------------------------------------------------------*/

#include "../vendor/cadical/src/ccadical.h"

#include <stddef.h>
#include <stdint.h>

// C wrapper for CaDiCaL's C++ API following IPASIR-UP.

typedef struct CCaDiCaLPropagator CCaDiCaLPropagator;

void ccadical_connect_external_propagator(CCaDiCaL *, CCaDiCaLPropagator *);
void ccadical_disconnect_external_propagator(CCaDiCaL *);

void ccadical_add_observed_var(CCaDiCaL *, int var);
void ccadical_remove_observed_var(CCaDiCaL *, int var);
void ccadical_reset_observed_vars(CCaDiCaL *);
bool ccadical_is_decision(CCaDiCaL *, int lit);

CCaDiCaLPropagator *ccadical_prop_init(void *state);
void ccadical_prop_release(CCaDiCaLPropagator *);
void ccadical_prop_lazy(CCaDiCaLPropagator *, bool is_lazy);

void ccadical_prop_set_notify_assignment(
    CCaDiCaLPropagator *,
    void (*notify_assignment)(void *state, int lit, bool is_fixed));
void ccadical_prop_set_notify_new_decision_level(
    CCaDiCaLPropagator *, void (*notify_new_decision_level)(void *state));
void ccadical_prop_set_notify_backtrack(
    CCaDiCaLPropagator *,
    void (*notify_backtrack)(void *state, size_t new_level));

void ccadical_prop_set_check_model(CCaDiCaLPropagator *,
                                   bool (*check_model)(void *state, size_t size,
                                                       const int *model));
void ccadical_prop_set_decide(CCaDiCaLPropagator *, int (*decide)(void *state));
void ccadical_prop_set_propagate(CCaDiCaLPropagator *,
                                 int (*propagate)(void *state));

void ccadical_prop_set_add_reason_clause_lit(
    CCaDiCaLPropagator *,
    int (*add_reason_clause_lit)(void *state, int propagated_lit));

void ccadical_prop_set_has_external_clause(
    CCaDiCaLPropagator *, bool (*has_external_clause)(void *state));
void ccadical_prop_set_add_external_clause_lit(
    CCaDiCaLPropagator *, int (*add_external_clause_lit)(void *state));

// Additional C bindings for C++ Cadical

void ccadical_phase(CCaDiCaL *, int lit);
void ccadical_unphase(CCaDiCaL *, int lit);
CCaDiCaL *ccadical_copy(CCaDiCaL *slv);

/*------------------------------------------------------------------------*/

/*------------------------------------------------------------------------*/
#ifdef __cplusplus
}
#endif
/*------------------------------------------------------------------------*/

#endif
