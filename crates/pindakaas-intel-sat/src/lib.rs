use std::ffi::{c_char, c_int, c_void};

extern "C" {
	// IPASIR definitions
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
