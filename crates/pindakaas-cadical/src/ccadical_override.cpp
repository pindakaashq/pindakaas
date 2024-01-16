#include "../vendor/cadical/src/ccadical.cpp"

namespace CaDiCaL {

struct PropagatorWrapper : ExternalPropagator {
  void *state;

  void (*notify_assignment_fn)(void *state, int lit, bool is_fixed);
  void (*notify_new_decision_level_fn)(void *state);
  void (*notify_backtrack_fn)(void *state, size_t new_level);

  bool (*check_model_fn)(void *state, size_t size, const int *model);
  int (*decide_fn)(void *state);
  int (*propagate_fn)(void *state);
  int (*add_reason_clause_lit_fn)(void *state, int propagated_lit);
  bool (*has_external_clause_fn)(void *state);
  int (*add_external_clause_lit_fn)(void *state);

  PropagatorWrapper(void *state)
      : state(state), notify_assignment_fn(nullptr),
        notify_new_decision_level_fn(nullptr), notify_backtrack_fn(nullptr),
        check_model_fn(nullptr), propagate_fn(nullptr),
        add_reason_clause_lit_fn(nullptr), has_external_clause_fn(nullptr),
        add_external_clause_lit_fn(nullptr) {}

  virtual void notify_assignment(int lit, bool is_fixed) {
    if (notify_assignment_fn != nullptr) {
      notify_assignment_fn(state, lit, is_fixed);
    }
  };
  virtual void notify_new_decision_level() {
    if (notify_new_decision_level_fn != nullptr) {
      notify_new_decision_level_fn(state);
    }
  };
  virtual void notify_backtrack(size_t new_level) {
    if (notify_backtrack_fn != nullptr) {
      notify_backtrack_fn(state, new_level);
    }
  };

  virtual bool cb_check_found_model(const std::vector<int> &model) {
    if (check_model_fn != nullptr) {
      return check_model_fn(state, model.size(), model.data());
    }
    return true;
  };
  virtual int cb_decide() {
    if (decide_fn != nullptr) {
      return decide_fn(state);
    }
    return 0;
  };
  virtual int cb_propagate() {
    if (propagate_fn != nullptr) {
      return propagate_fn(state);
    }
    return 0;
  };

  virtual int cb_add_reason_clause_lit(int propagated_lit) {
    if (add_reason_clause_lit_fn != nullptr) {
      return add_reason_clause_lit_fn(state, propagated_lit);
    }
    return 0;
  };

  virtual bool cb_has_external_clause() {
    if (has_external_clause_fn != nullptr) {
      return has_external_clause_fn(state);
    }
    return false;
  };
  virtual int cb_add_external_clause_lit() {
    if (add_external_clause_lit_fn != nullptr) {
      return add_external_clause_lit_fn(state);
    }
    return 0;
  };
};

} // namespace CaDiCaL

using namespace CaDiCaL;

extern "C" {

#include "ccadical_up.h"

void ccadical_connect_external_propagator(CCaDiCaL *slv,
                                          CCaDiCaLPropagator *prop) {
  ((Wrapper *)slv)
      ->solver->connect_external_propagator(((PropagatorWrapper *)prop));
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

void ccadical_phase(CCaDiCaL *slv, int lit) {
  ((Wrapper *)slv)->solver->phase(lit);
}
void ccadical_unphase(CCaDiCaL *slv, int lit) {
  ((Wrapper *)slv)->solver->unphase(lit);
}

CCaDiCaLPropagator *ccadical_prop_init(void *state) {
  return (CCaDiCaLPropagator *)new PropagatorWrapper(state);
}
void ccadical_prop_release(CCaDiCaLPropagator *prop) {
  delete (PropagatorWrapper *)prop;
}
void ccadical_prop_lazy(CCaDiCaLPropagator *prop, bool is_lazy) {
  ((PropagatorWrapper *)prop)->is_lazy = is_lazy;
}

void ccadical_prop_set_notify_assignment(
    CCaDiCaLPropagator *prop,
    void (*notify_assignment)(void *state, int lit, bool is_fixed)) {
  ((PropagatorWrapper *)prop)->notify_assignment_fn = notify_assignment;
}
void ccadical_prop_set_notify_new_decision_level(
    CCaDiCaLPropagator *prop, void (*notify_new_decision_level)(void *state)) {
  ((PropagatorWrapper *)prop)->notify_new_decision_level_fn =
      notify_new_decision_level;
}
void ccadical_prop_set_notify_backtrack(
    CCaDiCaLPropagator *prop,
    void (*notify_backtrack)(void *state, size_t new_level)) {
  ((PropagatorWrapper *)prop)->notify_backtrack_fn = notify_backtrack;
}

void ccadical_prop_set_check_model(CCaDiCaLPropagator *prop,
                                   bool (*check_model)(void *state, size_t size,
                                                       const int *model)) {
  ((PropagatorWrapper *)prop)->check_model_fn = check_model;
}

void ccadical_prop_set_decide(CCaDiCaLPropagator *prop,
                              int (*decide)(void *state)) {
  ((PropagatorWrapper *)prop)->decide_fn = decide;
}
void ccadical_prop_set_propagate(CCaDiCaLPropagator *prop,
                                 int (*propagate)(void *state)) {
  ((PropagatorWrapper *)prop)->propagate_fn = propagate;
}

void ccadical_prop_set_add_reason_clause_lit(
    CCaDiCaLPropagator *prop,
    int (*add_reason_clause_lit)(void *state, int propagated_lit)) {
  ((PropagatorWrapper *)prop)->add_reason_clause_lit_fn = add_reason_clause_lit;
}

void ccadical_prop_set_has_external_clause(
    CCaDiCaLPropagator *prop, bool (*has_external_clause)(void *state)) {
  ((PropagatorWrapper *)prop)->has_external_clause_fn = has_external_clause;
}
void ccadical_prop_set_add_external_clause_lit(
    CCaDiCaLPropagator *prop, int (*add_external_clause_lit)(void *state)) {
  ((PropagatorWrapper *)prop)->add_external_clause_lit_fn =
      add_external_clause_lit;
}
}
