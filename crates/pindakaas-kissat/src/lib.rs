#![expect(clippy::missing_safety_doc, reason = "C bindings crate")]

use std::ffi::{c_char, c_int, c_uint, c_void};

// Standard IPASIR definitions
extern "C" {
	pub fn kissat_signature() -> *const c_char;
	pub fn kissat_init() -> *mut c_void;
	pub fn kissat_release(slv: *mut c_void);
	pub fn kissat_add(slv: *mut c_void, lit: i32);
	pub fn kissat_assume(slv: *mut c_void, lit: i32);
	pub fn kissat_solve(slv: *mut c_void) -> c_int;
	pub fn kissat_val(slv: *mut c_void, lit: i32) -> i32;
	pub fn kissat_failed(slv: *mut c_void, lit: i32) -> c_int;
	pub fn kissat_set_terminate(
		slv: *mut c_void,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);
	pub fn kissat_set_learn(
		slv: *mut c_void,
		data: *mut c_void,
		max_len: c_int,
		cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	);
}
pub unsafe fn ipasir_signature() -> *const c_char {
	kissat_signature()
}
pub unsafe fn ipasir_init() -> *mut c_void {
	kissat_init()
}
pub unsafe fn ipasir_release(slv: *mut c_void) {
	kissat_release(slv);
}
pub unsafe fn ipasir_add(slv: *mut c_void, lit: i32) {
	kissat_add(slv, lit);
}
pub unsafe fn ipasir_assume(slv: *mut c_void, lit: i32) {
	kissat_assume(slv, lit);
}
pub unsafe fn ipasir_solve(slv: *mut c_void) -> c_int {
	kissat_solve(slv)
}
pub unsafe fn ipasir_val(slv: *mut c_void, lit: i32) -> i32 {
	kissat_val(slv, lit)
}
pub unsafe fn ipasir_failed(slv: *mut c_void, lit: i32) -> c_int {
	kissat_failed(slv, lit)
}
pub unsafe fn ipasir_set_terminate(
	slv: *mut c_void,
	data: *mut c_void,
	cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
) {
	kissat_set_terminate(slv, data, cb);
}
pub unsafe fn ipasir_set_learn(
	slv: *mut c_void,
	data: *mut c_void,
	max_len: c_int,
	cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
) {
	kissat_set_learn(slv, data, max_len, cb);
}

// Additional C-API functions in Kissat
extern "C" {
	pub fn kissat_banner(line_prefix: *const c_char, name_of_app: *const c_char);
	pub fn kissat_build(line_prefix: *const c_char);
	pub fn kissat_compiler() -> *const c_char;
	pub fn kissat_copyright() -> *const *const c_char;
	pub fn kissat_get_option(slv: *mut c_void, name: *const c_char) -> c_int;
	pub fn kissat_has_configuration(name: *const c_char) -> c_int;
	pub fn kissat_id() -> *const c_char;
	pub fn kissat_print_statistics(slv: *mut c_void);
	pub fn kissat_reserve(slv: *mut c_void, max_var: c_int);
	pub fn kissat_set_configuration(slv: *mut c_void, name: *const c_char) -> c_int;
	pub fn kissat_set_conflict_limit(slv: *mut c_void, limit: c_uint);
	pub fn kissat_set_decision_limit(slv: *mut c_void, limit: c_uint);
	pub fn kissat_set_option(slv: *mut c_void, name: *const c_char, new_value: c_int) -> c_int;
	pub fn kissat_terminate(slv: *mut c_void);
	pub fn kissat_version() -> *const c_char;
}
