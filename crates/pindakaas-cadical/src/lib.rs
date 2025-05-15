#![expect(clippy::missing_safety_doc, reason = "C bindings crate")]

use std::ffi::{c_char, c_int, c_void};

// Standard IPASIR definitions
extern "C" {
	pub fn ccadical_signature() -> *const c_char;
	pub fn ccadical_init() -> *mut c_void;
	pub fn ccadical_release(slv: *mut c_void);
	pub fn ccadical_add(slv: *mut c_void, lit: i32);
	pub fn ccadical_assume(slv: *mut c_void, lit: i32);
	pub fn ccadical_solve(slv: *mut c_void) -> c_int;
	pub fn ccadical_val(slv: *mut c_void, lit: i32) -> i32;
	pub fn ccadical_failed(slv: *mut c_void, lit: i32) -> c_int;
	pub fn ccadical_set_terminate(
		slv: *mut c_void,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);
	pub fn ccadical_set_learn(
		slv: *mut c_void,
		data: *mut c_void,
		max_len: c_int,
		cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	);
}
pub unsafe fn ipasir_signature() -> *const c_char {
	ccadical_signature()
}
pub unsafe fn ipasir_init() -> *mut c_void {
	ccadical_init()
}
pub unsafe fn ipasir_release(slv: *mut c_void) {
	ccadical_release(slv);
}
pub unsafe fn ipasir_add(slv: *mut c_void, lit: i32) {
	ccadical_add(slv, lit);
}
pub unsafe fn ipasir_assume(slv: *mut c_void, lit: i32) {
	ccadical_assume(slv, lit);
}
pub unsafe fn ipasir_solve(slv: *mut c_void) -> c_int {
	ccadical_solve(slv)
}
pub unsafe fn ipasir_val(slv: *mut c_void, lit: i32) -> i32 {
	ccadical_val(slv, lit)
}
pub unsafe fn ipasir_failed(slv: *mut c_void, lit: i32) -> c_int {
	ccadical_failed(slv, lit)
}
pub unsafe fn ipasir_set_terminate(
	slv: *mut c_void,
	data: *mut c_void,
	cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
) {
	ccadical_set_terminate(slv, data, cb);
}
pub unsafe fn ipasir_set_learn(
	slv: *mut c_void,
	data: *mut c_void,
	max_len: c_int,
	cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
) {
	ccadical_set_learn(slv, data, max_len, cb);
}

// Standard IPASIR-UP definitions
extern "C" {
	pub fn ccadical_connect_external_propagator(
		slv: *mut c_void,
		propagator_data: *mut c_void,
		prop_notify_assignments: unsafe extern "C" fn(*mut c_void, *const i32, usize),
		prop_notify_new_decision_level: unsafe extern "C" fn(*mut c_void),
		prop_notify_backtrack: unsafe extern "C" fn(*mut c_void, usize, bool),
		prop_cb_check_found_model: unsafe extern "C" fn(*mut c_void, *const i32, usize) -> bool,
		prop_cb_has_external_clause: unsafe extern "C" fn(*mut c_void, *mut bool) -> bool,
		prop_cb_add_external_clause_lit: unsafe extern "C" fn(*mut c_void) -> i32,
		is_lazy: bool,
		forgettable_reasons: bool,
		notify_fixed: bool,
		prop_cb_decide: unsafe extern "C" fn(*mut c_void) -> i32,
		prop_cb_propagate: unsafe extern "C" fn(*mut c_void) -> i32,
		prop_cb_add_reason_clause_lit: unsafe extern "C" fn(*mut c_void, i32) -> i32,
		prop_notify_fixed_assignment: unsafe extern "C" fn(*mut c_void, i32),
	);
	pub fn ccadical_disconnect_external_propagator(slv: *mut c_void);
	pub fn ccadical_add_observed_var(slv: *mut c_void, var: i32);
	pub fn ccadical_remove_observed_var(slv: *mut c_void, var: i32);
	pub fn ccadical_reset_observed_vars(slv: *mut c_void);
	pub fn ccadical_is_decision(slv: *mut c_void, lit: i32) -> bool;
	pub fn ccadical_force_backtrack(slv: *mut c_void, new_level: usize);
}
#[expect(
	clippy::too_many_arguments,
	reason = "C bindings to all propagator functionality"
)]
pub unsafe fn ipasir_connect_external_propagator(
	slv: *mut c_void,
	propagator_data: *mut c_void,
	prop_notify_assignments: unsafe extern "C" fn(*mut c_void, *const i32, usize),
	prop_notify_new_decision_level: unsafe extern "C" fn(*mut c_void),
	prop_notify_backtrack: unsafe extern "C" fn(*mut c_void, usize, bool),
	prop_cb_check_found_model: unsafe extern "C" fn(*mut c_void, *const i32, usize) -> bool,
	prop_cb_has_external_clause: unsafe extern "C" fn(*mut c_void, *mut bool) -> bool,
	prop_cb_add_external_clause_lit: unsafe extern "C" fn(*mut c_void) -> i32,
	is_lazy: bool,
	forgettable_reasons: bool,
	notify_fixed: bool,
	prop_cb_decide: unsafe extern "C" fn(*mut c_void) -> i32,
	prop_cb_propagate: unsafe extern "C" fn(*mut c_void) -> i32,
	prop_cb_add_reason_clause_lit: unsafe extern "C" fn(*mut c_void, i32) -> i32,
	prop_notify_fixed_assignment: unsafe extern "C" fn(*mut c_void, i32),
) {
	ccadical_connect_external_propagator(
		slv,
		propagator_data,
		prop_notify_assignments,
		prop_notify_new_decision_level,
		prop_notify_backtrack,
		prop_cb_check_found_model,
		prop_cb_has_external_clause,
		prop_cb_add_external_clause_lit,
		is_lazy,
		forgettable_reasons,
		notify_fixed,
		prop_cb_decide,
		prop_cb_propagate,
		prop_cb_add_reason_clause_lit,
		prop_notify_fixed_assignment,
	);
}
pub unsafe fn ipasir_disconnect_external_propagator(slv: *mut c_void) {
	ccadical_disconnect_external_propagator(slv);
}
pub unsafe fn ipasir_add_observed_var(slv: *mut c_void, var: i32) {
	ccadical_add_observed_var(slv, var);
}
pub unsafe fn ipasir_remove_observed_var(slv: *mut c_void, var: i32) {
	ccadical_remove_observed_var(slv, var);
}
pub unsafe fn ipasir_reset_observed_vars(slv: *mut c_void) {
	ccadical_reset_observed_vars(slv);
}
pub unsafe fn ipasir_is_decision(slv: *mut c_void, lit: i32) -> bool {
	ccadical_is_decision(slv, lit)
}
pub unsafe fn ipasir_force_backtrack(slv: *mut c_void, new_level: usize) {
	ccadical_force_backtrack(slv, new_level);
}

// Additional C-API functions in CaDiCaL
extern "C" {
	pub fn ccadical_active(slv: *mut c_void) -> i64;
	pub fn ccadical_constrain(slv: *mut c_void, lit: i32);
	pub fn ccadical_constraint_failed(slv: *mut c_void) -> c_int;
	pub fn ccadical_copy(slv: *const c_void) -> *mut c_void;
	pub fn ccadical_fixed(slv: *mut c_void, lit: i32) -> c_int;
	pub fn ccadical_freeze(slv: *mut c_void, lit: i32);
	pub fn ccadical_frozen(slv: *mut c_void, lit: i32) -> c_int;
	pub fn ccadical_get_option(slv: *mut c_void, name: *const c_char) -> c_int;
	pub fn ccadical_irredundant(slv: *mut c_void) -> i64;
	pub fn ccadical_is_observed(slv: *mut c_void, lit: i32) -> bool;
	pub fn ccadical_limit(slv: *mut c_void, name: *const c_char, limit: c_int);
	pub fn ccadical_melt(slv: *mut c_void, lit: i32);
	pub fn ccadical_phase(slv: *mut c_void, lit: i32);
	pub fn ccadical_print_statistics(slv: *mut c_void);
	pub fn ccadical_set_option(slv: *mut c_void, name: *const c_char, val: c_int);
	pub fn ccadical_simplify(slv: *mut c_void) -> c_int;
	pub fn ccadical_terminate(slv: *mut c_void);
	pub fn ccadical_unphase(slv: *mut c_void, lit: i32);
	pub fn ccadical_enable_proof(slv: *mut c_void, name: *const c_char);
}
