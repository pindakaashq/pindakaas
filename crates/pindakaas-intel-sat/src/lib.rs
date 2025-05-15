#![expect(clippy::missing_safety_doc, reason = "C bindings crate")]

use std::ffi::{c_char, c_int, c_void};

// Standard IPASIR definitions
extern "C" {
	pub fn intel_sat_signature() -> *const c_char;
	pub fn intel_sat_init() -> *mut c_void;
	pub fn intel_sat_release(slv: *mut c_void);
	pub fn intel_sat_add(slv: *mut c_void, lit: i32);
	pub fn intel_sat_assume(slv: *mut c_void, lit: i32);
	pub fn intel_sat_solve(slv: *mut c_void) -> c_int;
	pub fn intel_sat_val(slv: *mut c_void, lit: i32) -> i32;
	pub fn intel_sat_failed(slv: *mut c_void, lit: i32) -> c_int;
	pub fn intel_sat_set_terminate(
		slv: *mut c_void,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);
	pub fn intel_sat_set_learn(
		slv: *mut c_void,
		data: *mut c_void,
		max_len: c_int,
		cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	);
}
pub unsafe fn ipasir_signature() -> *const c_char {
	intel_sat_signature()
}
pub unsafe fn ipasir_init() -> *mut c_void {
	intel_sat_init()
}
pub unsafe fn ipasir_release(slv: *mut c_void) {
	intel_sat_release(slv);
}
pub unsafe fn ipasir_add(slv: *mut c_void, lit: i32) {
	intel_sat_add(slv, lit);
}
pub unsafe fn ipasir_assume(slv: *mut c_void, lit: i32) {
	intel_sat_assume(slv, lit);
}
pub unsafe fn ipasir_solve(slv: *mut c_void) -> c_int {
	intel_sat_solve(slv)
}
pub unsafe fn ipasir_val(slv: *mut c_void, lit: i32) -> i32 {
	intel_sat_val(slv, lit)
}
pub unsafe fn ipasir_failed(slv: *mut c_void, lit: i32) -> c_int {
	intel_sat_failed(slv, lit)
}
pub unsafe fn ipasir_set_terminate(
	slv: *mut c_void,
	data: *mut c_void,
	cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
) {
	intel_sat_set_terminate(slv, data, cb);
}
pub unsafe fn ipasir_set_learn(
	slv: *mut c_void,
	data: *mut c_void,
	max_len: c_int,
	cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
) {
	intel_sat_set_learn(slv, data, max_len, cb);
}
