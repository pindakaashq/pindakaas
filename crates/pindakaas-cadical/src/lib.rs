use std::ffi::{c_char, c_int, c_void};

type CCaDiCaL = c_void;

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct CExternalPropagator {
	pub data: *mut c_void,
	pub is_lazy: bool,
	pub are_reasons_forgettable: bool,
	pub notify_assignments:
		unsafe extern "C" fn(data: *mut c_void, lits: *const c_int, size: usize),
	pub notify_new_decision_level: unsafe extern "C" fn(data: *mut c_void),
	pub notify_backtrack: unsafe extern "C" fn(data: *mut c_void, new_level: usize, restart: bool),
	pub check_found_model:
		unsafe extern "C" fn(data: *mut c_void, model: *const c_int, size: usize) -> bool,
	pub decide: unsafe extern "C" fn(data: *mut c_void) -> c_int,
	pub propagate: unsafe extern "C" fn(data: *mut c_void) -> c_int,
	pub add_reason_clause_lit:
		unsafe extern "C" fn(data: *mut c_void, propagated_lit: c_int) -> c_int,
	pub has_external_clause:
		unsafe extern "C" fn(data: *mut c_void, is_forgettable: *mut bool) -> bool,
	pub add_external_clause_lit: unsafe extern "C" fn(data: *mut c_void) -> c_int,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct CFixedAssignmentListener {
	pub data: *mut c_void,
	pub notify_fixed_assignment: unsafe extern "C" fn(data: *mut c_void, lit: c_int),
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct CTracer {
	pub data: *mut c_void,
	pub add_original_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
		restored: bool,
	),
	pub add_derived_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
		antecedents: *const u64,
		antecedents_len: usize,
	),
	pub delete_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
	),
	pub weaken_minus:
		unsafe extern "C" fn(data: *mut c_void, id: u64, clause: *const c_int, clause_len: usize),
	pub strengthen: unsafe extern "C" fn(data: *mut c_void, id: u64),
	pub report_status: unsafe extern "C" fn(data: *mut c_void, status: c_int, id: u64),
	pub finalize_clause:
		unsafe extern "C" fn(data: *mut c_void, id: u64, clause: *const c_int, clause_lens: usize),
	pub begin_proof: unsafe extern "C" fn(data: *mut c_void, first_derived: u64),
	pub solve_query: unsafe extern "C" fn(data: *mut c_void),
	pub add_assumption: unsafe extern "C" fn(data: *mut c_void, lit: c_int),
	pub add_constraint:
		unsafe extern "C" fn(data: *mut c_void, clause: *const c_int, clause_len: usize),
	pub reset_assumptions: unsafe extern "C" fn(data: *mut c_void),
	pub add_assumption_clause: unsafe extern "C" fn(
		data: *mut c_void,
		id: u64,
		clause: *const c_int,
		clause_len: usize,
		antecedents: *const u64,
		antecedents_len: usize,
	),
	pub conclude_unsat: unsafe extern "C" fn(
		data: *mut c_void,
		conclusion_type: u8,
		clause_ids: *const u64,
		clause_ids_len: usize,
	),
	pub conclude_sat:
		unsafe extern "C" fn(data: *mut c_void, assignment: *const c_int, assignment_len: usize),
	pub conclude_unknown:
		unsafe extern "C" fn(data: *mut c_void, trail: *const c_int, trail_len: usize),
}

extern "C" {
	// IPASIR definitions
	pub fn ccadical_signature() -> *const c_char;
	pub fn ccadical_init() -> *mut CCaDiCaL;
	pub fn ccadical_release(slv: *mut CCaDiCaL);
	pub fn ccadical_add(slv: *mut CCaDiCaL, lit: i32);
	pub fn ccadical_assume(slv: *mut CCaDiCaL, lit: i32);
	pub fn ccadical_solve(slv: *mut CCaDiCaL) -> c_int;
	pub fn ccadical_val(slv: *mut CCaDiCaL, lit: i32) -> i32;
	pub fn ccadical_failed(slv: *mut CCaDiCaL, lit: i32) -> c_int;
	pub fn ccadical_set_terminate(
		slv: *mut CCaDiCaL,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);
	pub fn ccadical_set_learn(
		slv: *mut CCaDiCaL,
		data: *mut c_void,
		max_len: c_int,
		cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	);

	// IPASIR-UP definitions
	pub fn ccadical_connect_external_propagator(slv: *mut CCaDiCaL, prop: CExternalPropagator);
	pub fn ccadical_disconnect_external_propagator(slv: *mut CCaDiCaL);
	pub fn ccadical_add_observed_var(slv: *mut CCaDiCaL, var: i32);
	pub fn ccadical_remove_observed_var(slv: *mut CCaDiCaL, var: i32);
	pub fn ccadical_reset_observed_vars(slv: *mut CCaDiCaL);
	pub fn ccadical_is_decision(slv: *mut CCaDiCaL, lit: i32) -> bool;
	pub fn ccadical_force_backtrack(slv: *mut CCaDiCaL, new_level: usize);

	pub fn ccadical_connect_fixed_listener(slv: *mut CCaDiCaL, listener: CFixedAssignmentListener);
	pub fn ccadical_disconnect_fixed_listener(slv: *mut CCaDiCaL);

	// Additional C-API functions in CaDiCaL
	pub fn ccadical_active(slv: *mut CCaDiCaL) -> i64;
	pub fn ccadical_constrain(slv: *mut CCaDiCaL, lit: i32);
	pub fn ccadical_constraint_failed(slv: *mut CCaDiCaL) -> c_int;
	pub fn ccadical_copy(slv: *const CCaDiCaL) -> *mut c_void;
	pub fn ccadical_fixed(slv: *mut CCaDiCaL, lit: i32) -> c_int;
	pub fn ccadical_freeze(slv: *mut CCaDiCaL, lit: i32);
	pub fn ccadical_frozen(slv: *mut CCaDiCaL, lit: i32) -> c_int;
	pub fn ccadical_get_option(slv: *mut CCaDiCaL, name: *const c_char) -> c_int;
	pub fn ccadical_irredundant(slv: *mut CCaDiCaL) -> i64;
	pub fn ccadical_is_observed(slv: *mut CCaDiCaL, lit: i32) -> bool;
	pub fn ccadical_limit(slv: *mut CCaDiCaL, name: *const c_char, limit: c_int);
	pub fn ccadical_melt(slv: *mut CCaDiCaL, lit: i32);
	pub fn ccadical_phase(slv: *mut CCaDiCaL, lit: i32);
	pub fn ccadical_print_statistics(slv: *mut CCaDiCaL);
	pub fn ccadical_set_option(slv: *mut CCaDiCaL, name: *const c_char, val: c_int);
	pub fn ccadical_simplify(slv: *mut CCaDiCaL) -> c_int;
	pub fn ccadical_terminate(slv: *mut CCaDiCaL);
	pub fn ccadical_unphase(slv: *mut CCaDiCaL, lit: i32);

	// Proof Tracer API
	pub fn ccadical_connect_proof_tracer(
		slv: *mut CCaDiCaL,
		tracer: CTracer,
		antecedents: bool,
		finalize_clauses: bool,
	);
	pub fn ccadical_disconnect_proof_tracer(slv: *mut CCaDiCaL, tracer_data: *mut c_void) -> bool;
}
