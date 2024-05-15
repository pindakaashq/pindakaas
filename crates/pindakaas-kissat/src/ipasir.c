#include "../vendor/kissat/src/kissat.h"
#include <assert.h>
#include <stdint.h>

/// Empty function to complete IPASIR default interface
void kissar_set_learn(void *solver, void *state, int max_length,
                      void (*learn)(void *state, int *clause)) {
  assert(0);
  solver;
  state;
  max_length;
  learn;
}

int32_t kissat_val(void *solver, int32_t lit) {
  return kissat_value(solver, lit);
  solver;
  lit;
}

int kissat_failed(void *solver, int32_t lit) {
  assert(0);
  solver;
  lit;
  return 0;
}
void kissat_assume(void *solver, int32_t lit) {
  assert(0);
  solver;
  lit;
}
