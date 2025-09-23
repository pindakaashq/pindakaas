//! This crate provides low-level bindings to the [Intel
//! SAT](https://github.com/alexander-nadel/intel_sat_solver) solver aimed at
//! the [Pindakaas](https://crates.io/crates/pindakaas) library.

use std::ffi::{c_char, c_int, c_void};

extern "C" {
	// IPASIR definitions
	/// Intel SAT `ipasir_signature` implementation.
	pub fn intel_sat_signature() -> *const c_char;
	/// Intel SAT `ipasir_init` implementation.
	pub fn intel_sat_init() -> *mut c_void;
	/// Intel SAT `ipasir_release` implementation.
	pub fn intel_sat_release(slv: *mut c_void);
	/// Intel SAT `ipasir_add` implementation.
	pub fn intel_sat_add(slv: *mut c_void, lit: i32);
	/// Intel SAT `ipasir_assume` implementation.
	pub fn intel_sat_assume(slv: *mut c_void, lit: i32);
	/// Intel SAT `ipasir_solve` implementation.
	pub fn intel_sat_solve(slv: *mut c_void) -> c_int;
	/// Intel SAT `ipasir_val` implementation.
	pub fn intel_sat_val(slv: *mut c_void, lit: i32) -> i32;
	/// Intel SAT `ipasir_failed` implementation.
	pub fn intel_sat_failed(slv: *mut c_void, lit: i32) -> c_int;
	/// Intel SAT `ipasir_set_terminate` implementation.
	pub fn intel_sat_set_terminate(
		slv: *mut c_void,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);
	/// Intel SAT `ipasir_set_learn` implementation.
	pub fn intel_sat_set_learn(
		slv: *mut c_void,
		data: *mut c_void,
		max_len: c_int,
		cb: Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	);
}
