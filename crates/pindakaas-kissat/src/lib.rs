//! This crate provides low-level bindings to the
//! [Kissat](https://github.com/arminbiere/kissat) solver aimed at the
//! [Pindakaas](https://crates.io/crates/pindakaas) library.

use std::ffi::{c_char, c_int, c_uint, c_void};

extern "C" {
	// IPASIR definitions
	/// Kissat `ipasir_signature` implementation
	pub fn kissat_signature() -> *const c_char;
	/// Kissat `ipasir_init` implementation
	pub fn kissat_init() -> *mut c_void;
	/// Kissat `ipasir_release` implementation
	pub fn kissat_release(slv: *mut c_void);
	/// Kissat `ipasir_add` implementation
	pub fn kissat_add(slv: *mut c_void, lit: c_int);
	/// Kissat `ipasir_solve` implementation
	pub fn kissat_solve(slv: *mut c_void) -> c_int;
	/// Kissat `ipasir_value` implementation
	pub fn kissat_value(slv: *mut c_void, lit: c_int) -> c_int;
	/// Kissat `ipasir_set_terminate` implementation
	pub fn kissat_set_terminate(
		slv: *mut c_void,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);

	// Additional C-API functions in Kissat
	/// C binding for the `kissat_banner` function
	pub fn kissat_banner(line_prefix: *const c_char, name_of_app: *const c_char);
	/// C binding for the `kissat_build` function
	pub fn kissat_build(line_prefix: *const c_char);
	/// C binding for the `kissat_compiler` function
	pub fn kissat_compiler() -> *const c_char;
	/// C binding for the `kissat_copyright` function
	pub fn kissat_copyright() -> *const *const c_char;
	/// C binding for the `kissat_get_option` function
	pub fn kissat_get_option(slv: *mut c_void, name: *const c_char) -> c_int;
	/// C binding for the `kissat_has_configuration` function
	pub fn kissat_has_configuration(name: *const c_char) -> c_int;
	/// C binding for the `kissat_id` function
	pub fn kissat_id() -> *const c_char;
	/// C binding for the `kissat_print_statistics` function
	pub fn kissat_print_statistics(slv: *mut c_void);
	/// C binding for the `kissat_reserve` function
	pub fn kissat_reserve(slv: *mut c_void, max_var: c_int);
	/// C binding for the `kissat_set_configuration` function
	pub fn kissat_set_configuration(slv: *mut c_void, name: *const c_char) -> c_int;
	/// C binding for the `kissat_set_conflict_limit` function
	pub fn kissat_set_conflict_limit(slv: *mut c_void, limit: c_uint);
	/// C binding for the `kissat_set_decision_limit` function
	pub fn kissat_set_decision_limit(slv: *mut c_void, limit: c_uint);
	/// C binding for the `kissat_set_option` function
	pub fn kissat_set_option(slv: *mut c_void, name: *const c_char, new_value: c_int) -> c_int;
	/// C binding for the `kissat_terminate` function
	pub fn kissat_terminate(slv: *mut c_void);
	/// C binding for the `kissat_version` function
	pub fn kissat_version() -> *const c_char;
}
