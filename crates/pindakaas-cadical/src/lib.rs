use std::ffi::{c_char, c_int, c_void};

use pindakaas_build_macros::{ipasir_definitions, ipasir_up_definitions};

// Standard IPASIR definitions
ipasir_definitions!(ccadical);
ipasir_up_definitions!(ccadical);

// Additional C-API functions in CaDiCaL
extern "C" {
	pub fn ccadical_active(slv: *mut c_void) -> i64;
	pub fn ccadical_constrain(slv: *mut c_void, lit: i32);
	pub fn ccadical_constraint_failed(slv: *mut c_void) -> c_int;
	pub fn ccadical_fixed(slv: *mut c_void, lit: i32) -> c_int;
	pub fn ccadical_freeze(slv: *mut c_void, lit: i32);
	pub fn ccadical_frozen(slv: *mut c_void, lit: i32) -> c_int;
	pub fn ccadical_get_option(slv: *mut c_void, name: *const c_char) -> c_int;
	pub fn ccadical_irredundant(slv: *mut c_void) -> i64;
	pub fn ccadical_limit(slv: *mut c_void, name: *const c_char, limit: c_int);
	pub fn ccadical_melt(slv: *mut c_void, lit: i32);
	pub fn ccadical_phase(slv: *mut c_void, lit: i32);
	pub fn ccadical_print_statistics(slv: *mut c_void);
	pub fn ccadical_set_option(slv: *mut c_void, name: *const c_char, val: c_int);
	pub fn ccadical_simplify(slv: *mut c_void) -> c_int;
	pub fn ccadical_terminate(slv: *mut c_void);
	pub fn ccadical_unphase(slv: *mut c_void, lit: i32);
	pub fn ccadical_copy(slv: *const c_void) -> *mut c_void;
}
