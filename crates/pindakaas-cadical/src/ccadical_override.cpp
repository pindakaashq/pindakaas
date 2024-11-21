#include "../vendor/cadical/src/ccadical.cpp"

using namespace CaDiCaL;

extern "C" {

#include "ccadical_up.h"

void ccadical_connect_external_propagator(
    CCaDiCaL *slv, void *propagator_data,
    void (*prop_notify_assignments)(void *prop, const int *lits, size_t size),
    void (*prop_notify_new_decision_level)(void *prop),
    void (*prop_notify_backtrack)(void *prop, size_t new_level, bool restart),
    bool (*prop_cb_check_found_model)(void *prop, const int *model,
                                      size_t size),
    bool (*prop_cb_has_external_clause)(void *prop, bool *is_forgettable),
    int (*prop_cb_add_external_clause_lit)(void *prop), bool is_lazy,
    bool forgettable_reasons, bool notify_fixed,
    int (*prop_cb_decide)(void *prop), int (*prop_cb_propagate)(void *prop),
    int (*prop_cb_add_reason_clause_lit)(void *prop, int propagated_lit),
    void (*prop_notify_fixed_assignment)(void *prop, int lit)) {
  ((Wrapper *)slv)
      ->solver->connect_external_propagator(
          propagator_data, prop_notify_assignments,
          prop_notify_new_decision_level, prop_notify_backtrack,
          prop_cb_check_found_model, prop_cb_has_external_clause,
          prop_cb_add_external_clause_lit, is_lazy, forgettable_reasons,
          notify_fixed, prop_cb_decide, prop_cb_propagate,
          prop_cb_add_reason_clause_lit, prop_notify_fixed_assignment);
}
void ccadical_disconnect_external_propagator(CCaDiCaL *slv) {
  ((Wrapper *)slv)->solver->disconnect_external_propagator();
}

void ccadical_add_observed_var(CCaDiCaL *slv, int var) {
  ((Wrapper *)slv)->solver->add_observed_var(var);
}
void ccadical_remove_observed_var(CCaDiCaL *slv, int var) {
  ((Wrapper *)slv)->solver->remove_observed_var(var);
}
void ccadical_reset_observed_vars(CCaDiCaL *slv) {
  ((Wrapper *)slv)->solver->reset_observed_vars();
}
bool ccadical_is_decision(CCaDiCaL *slv, int lit) {
  return ((Wrapper *)slv)->solver->is_decision(lit);
}
void ccadical_force_backtrack(CCaDiCaL *slv, size_t new_level) {
  return ((Wrapper *)slv)->solver->force_backtrack(new_level);
}

void ccadical_phase(CCaDiCaL *slv, int lit) {
  ((Wrapper *)slv)->solver->phase(lit);
}
void ccadical_unphase(CCaDiCaL *slv, int lit) {
  ((Wrapper *)slv)->solver->unphase(lit);
}

CCaDiCaL *ccadical_copy(CCaDiCaL *slv) {
  auto *cp = new Wrapper();
  ((Wrapper *)slv)->solver->copy(*cp->solver);
  return (CCaDiCaL *)cp;
}
}
