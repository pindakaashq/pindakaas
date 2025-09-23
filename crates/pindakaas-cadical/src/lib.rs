//! This crate provides low-level bindings to the
//! [CaDiCaL](https://github.com/arminbiere/cadical) SAT solver aimed at the
//! [Pindakaas](https://crates.io/crates/pindakaas) library.

use std::ffi::{c_char, c_int, c_void};

type CCaDiCaL = c_void;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
/// Type used to represent an external propagator for the IPASIR-UP interface.
pub struct CExternalPropagator {
	/// Pointer to the data associated with the propagator.
	pub data: *mut c_void,
	/// Whether the propagator only checks solutions.
	pub is_lazy: bool,
	/// Whether the reasons the propagator produces are safe to forget (i.e.
	/// they will be reproduced by the propagator if required).
	pub are_reasons_forgettable: bool,
	/// Callback to notify the propagator of assignments to observed literals.
	pub notify_assignments:
		unsafe extern "C" fn(data: *mut c_void, lits: *const c_int, size: usize),
	/// Callback to notify the propagator of new decision levels.
	pub notify_new_decision_level: unsafe extern "C" fn(data: *mut c_void),
	/// Callback to notify the propagator of backtracks.
	pub notify_backtrack: unsafe extern "C" fn(data: *mut c_void, new_level: usize, restart: bool),
	/// Callback to check if a model (i.e. solution) is valid.
	pub check_found_model:
		unsafe extern "C" fn(data: *mut c_void, model: *const c_int, size: usize) -> bool,
	/// Callback to allow the propagator to make the next branching decision,
	/// allowing `0` to be returned to leave the decision up to the SAT solver.
	pub decide: unsafe extern "C" fn(data: *mut c_void) -> c_int,
	/// Callback to allow the propagator to propagate literals.
	pub propagate: unsafe extern "C" fn(data: *mut c_void) -> c_int,
	/// Callback to allow the propagator to add a literal to the reason of a
	/// literal that is propagated, allowing `0` to be returned to end the
	/// clause.
	pub add_reason_clause_lit:
		unsafe extern "C" fn(data: *mut c_void, propagated_lit: c_int) -> c_int,
	/// Callback to check whether the propagator wants to add an additional
	/// clause.
	pub has_external_clause:
		unsafe extern "C" fn(data: *mut c_void, is_forgettable: *mut bool) -> bool,
	/// Callback to allow the propagator to add a literal to the current
	/// additional clause or end the clause with a `0` return.
	pub add_external_clause_lit: unsafe extern "C" fn(data: *mut c_void) -> c_int,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
/// Type used to represent a fixed listener for the IPASIR-UP interface.
pub struct CFixedAssignmentListener {
	/// Data pointer for the fixed listener.
	pub data: *mut c_void,
	/// Callback to notify the fixed listener of a fixed assignment.
	pub notify_fixed_assignment: unsafe extern "C" fn(data: *mut c_void, lit: c_int),
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
/// Type used to represent a tracer for the proof tracer interface.
pub struct CTracer {
	/// Data pointer for the tracer.
	pub data: *mut c_void,
	/// Callback to add an original clause to the tracer.
	pub add_original_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
		restored: bool,
	),
	/// Callback to add a derived clause to the tracer.
	pub add_derived_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
		antecedents: *const u64,
		antecedents_len: usize,
	),
	/// Callback to delete a clause from the tracer.
	pub delete_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
	),
	/// Callback to weaken a clause in the tracer.
	pub weaken_minus:
		unsafe extern "C" fn(data: *mut c_void, id: u64, clause: *const c_int, clause_len: usize),
	/// Callback to strengthen a clause in the tracer.
	pub strengthen: unsafe extern "C" fn(data: *mut c_void, id: u64),
	/// Callback to report the status to the tracer.
	pub report_status: unsafe extern "C" fn(data: *mut c_void, status: c_int, id: u64),
	/// Callback to finalize a clause in the tracer.
	pub finalize_clause:
		unsafe extern "C" fn(data: *mut c_void, id: u64, clause: *const c_int, clause_lens: usize),
	/// Callback used when a proof is started.
	pub begin_proof: unsafe extern "C" fn(data: *mut c_void, first_derived: u64),
	/// Callback to notify an assumption has been added.
	pub solve_query: unsafe extern "C" fn(data: *mut c_void),
	/// Callback to add an assumption literal to the tracer.
	pub add_assumption: unsafe extern "C" fn(data: *mut c_void, lit: c_int),
	/// Callback to add a constraint to the tracer.
	pub add_constraint:
		unsafe extern "C" fn(data: *mut c_void, clause: *const c_int, clause_len: usize),
	/// Callback to reset the assumptions in the tracer.
	pub reset_assumptions: unsafe extern "C" fn(data: *mut c_void),
	/// Callback to add an assumption clause to the tracer.
	pub add_assumption_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		clause: *const c_int,
		clause_len: usize,
		antecedents: *const u64,
		antecedents_len: usize,
	),
	/// Callback to conclude the proof as unsatisfiable.
	pub conclude_unsat: unsafe extern "C" fn(
		data: *mut c_void,
		conclusion_type: u8,
		clause_ids: *const u64,
		clause_ids_len: usize,
	),
	/// Callback to conclude the proof as satisfiable.
	pub conclude_sat:
		unsafe extern "C" fn(data: *mut c_void, assignment: *const c_int, assignment_len: usize),
	/// Callback to finish the proof without a conclusion.
	pub conclude_unknown:
		unsafe extern "C" fn(data: *mut c_void, trail: *const c_int, trail_len: usize),
}

extern "C" {
	// IPASIR definitions
	/// CaDiCaL implementation of `ipasir_signature`.
	pub fn ccadical_signature() -> *const c_char;
	/// CaDiCaL implementation of `ipasir_init`.
	pub fn ccadical_init() -> *mut CCaDiCaL;
	/// CaDiCaL implementation of `ipasir_release`.
	pub fn ccadical_release(slv: *mut CCaDiCaL);
	/// CaDiCaL implementation of `ipasir_add`.
	pub fn ccadical_add(slv: *mut CCaDiCaL, lit: i32);
	/// CaDiCaL implementation of `ipasir_assume`.
	pub fn ccadical_assume(slv: *mut CCaDiCaL, lit: i32);
	/// CaDiCaL implementation of `ipasir_solve`.
	pub fn ccadical_solve(slv: *mut CCaDiCaL) -> c_int;
	/// CaDiCaL implementation of `ipasir_val`.
	pub fn ccadical_val(slv: *mut CCaDiCaL, lit: i32) -> i32;
	/// CaDiCaL implementation of `ipasir_failed`.
	pub fn ccadical_failed(slv: *mut CCaDiCaL, lit: i32) -> c_int;
	/// CaDiCaL implementation of `ipasir_set_terminate`.
	pub fn ccadical_set_terminate(
		slv: *mut CCaDiCaL,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);
	/// CaDiCaL implementation of `ipasir_set_learn`.
	pub fn ccadical_set_learn(
		slv: *mut CCaDiCaL,
		data: *mut c_void,
		max_len: c_int,
		cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	);

	// IPASIR-UP definitions
	/// C binding to the IPASIR-UP `connect_external_propagator` function.
	pub fn ccadical_connect_external_propagator(slv: *mut CCaDiCaL, prop: CExternalPropagator);
	/// C binding to the IPASIR-UP `disconnect_external_propagator` function.
	pub fn ccadical_disconnect_external_propagator(slv: *mut CCaDiCaL);
	/// C binding to the IPASIR-UP `add_observed_var` function.
	pub fn ccadical_add_observed_var(slv: *mut CCaDiCaL, var: i32);
	/// C binding to the IPASIR-UP `is_observed` function.
	pub fn ccadical_is_observed(slv: *mut CCaDiCaL, lit: i32) -> bool;
	/// C binding to the IPASIR-UP `remove_observed_var` function.
	pub fn ccadical_remove_observed_var(slv: *mut CCaDiCaL, var: i32);
	/// C binding to the IPASIR-UP `reset_observed_vars` function.
	pub fn ccadical_reset_observed_vars(slv: *mut CCaDiCaL);
	/// C binding to the IPASIR-UP `is_decision` function.
	pub fn ccadical_is_decision(slv: *mut CCaDiCaL, lit: i32) -> bool;
	/// C binding to the IPASIR-UP `force_backtrack` function.
	pub fn ccadical_force_backtrack(slv: *mut CCaDiCaL, new_level: usize);

	/// C binding to the IPASIR-UP `connect_fixed_listener` function.
	pub fn ccadical_connect_fixed_listener(slv: *mut CCaDiCaL, listener: CFixedAssignmentListener);
	/// C binding to the IPASIR-UP `disconnect_fixed_listener` function.
	pub fn ccadical_disconnect_fixed_listener(slv: *mut CCaDiCaL);

	// Additional C-API functions in CaDiCaL
	/// C binding for the `active` function.
	pub fn ccadical_active(slv: *mut CCaDiCaL) -> i64;
	/// C binding for the `constrain` function.
	pub fn ccadical_constrain(slv: *mut CCaDiCaL, lit: i32);
	/// C binding for the `constraint_failed` function.
	pub fn ccadical_constraint_failed(slv: *mut CCaDiCaL) -> c_int;
	/// C binding for the `copy` function.
	pub fn ccadical_copy(slv: *const CCaDiCaL) -> *mut c_void;
	/// C binding for the `fixed` function.
	pub fn ccadical_fixed(slv: *mut CCaDiCaL, lit: i32) -> c_int;
	/// C binding for the `freeze` function.
	pub fn ccadical_freeze(slv: *mut CCaDiCaL, lit: i32);
	/// C binding for the `frozen` function.
	pub fn ccadical_frozen(slv: *mut CCaDiCaL, lit: i32) -> c_int;
	/// C binding for the `get_option` function.
	pub fn ccadical_get_option(slv: *mut CCaDiCaL, name: *const c_char) -> c_int;
	/// C binding for the `irredundant` function.
	pub fn ccadical_irredundant(slv: *mut CCaDiCaL) -> i64;
	/// C binding for the `limit` function.
	pub fn ccadical_limit(slv: *mut CCaDiCaL, name: *const c_char, limit: c_int);
	/// C binding for the `melt` function.
	pub fn ccadical_melt(slv: *mut CCaDiCaL, lit: i32);
	/// C binding for the `phase` function.
	pub fn ccadical_phase(slv: *mut CCaDiCaL, lit: i32);
	/// C binding for the `print_statistics` function.
	pub fn ccadical_print_statistics(slv: *mut CCaDiCaL);
	/// C binding for the `set_option` function.
	pub fn ccadical_set_option(slv: *mut CCaDiCaL, name: *const c_char, val: c_int);
	/// C binding for the `simplify` function.
	pub fn ccadical_simplify(slv: *mut CCaDiCaL) -> c_int;
	/// C binding for the `terminate` function.
	pub fn ccadical_terminate(slv: *mut CCaDiCaL);
	/// C binding for the `unphase` function.
	pub fn ccadical_unphase(slv: *mut CCaDiCaL, lit: i32);

	// Proof Tracer API
	/// C binding for the `connect_proof_tracer` function.
	pub fn ccadical_connect_proof_tracer(
		slv: *mut CCaDiCaL,
		tracer: CTracer,
		antecedents: bool,
		finalize_clauses: bool,
	);
	/// C binding for the `disconnect_proof_tracer` function.
	pub fn ccadical_disconnect_proof_tracer(slv: *mut CCaDiCaL, tracer_data: *mut c_void) -> bool;
}
