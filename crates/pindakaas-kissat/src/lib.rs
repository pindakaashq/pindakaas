use std::ffi::{c_char, c_int, c_uint, c_void};

use pindakaas_build_macros::ipasir_definitions;

ipasir_definitions!(kissat);

extern "C" {
	pub fn kissat_terminate(slv: *mut c_void);
	pub fn kissat_reserve(slv: *mut c_void, max_var: c_int);

	pub fn kissat_id() -> *const c_char;
	pub fn kissat_version() -> *const c_char;
	pub fn kissat_compiler() -> *const c_char;

	pub fn kissat_copyright() -> *const *const c_char;
	pub fn kissat_build(line_prefix: *const c_char);
	pub fn kissat_banner(line_prefix: *const c_char, name_of_app: *const c_char);

	pub fn kissat_get_option(slv: *mut c_void, name: *const c_char) -> c_int;
	pub fn kissat_set_option(slv: *mut c_void, name: *const c_char, new_value: c_int) -> c_int;

	pub fn kissat_has_configuration(name: *const c_char) -> c_int;
	pub fn kissat_set_configuration(slv: *mut c_void, name: *const c_char) -> c_int;

	pub fn kissat_set_conflict_limit(slv: *mut c_void, limit: c_uint);
	pub fn kissat_set_decision_limit(slv: *mut c_void, limit: c_uint);

	pub fn kissat_print_statistics(slv: *mut c_void);
}
