use std::ffi::{c_char, c_int, c_uint, c_void};

extern "C" {
	// IPASIR definitions
	pub fn kissat_signature() -> *const c_char;
	pub fn kissat_init() -> *mut c_void;
	pub fn kissat_release(slv: *mut c_void);
	pub fn kissat_add(slv: *mut c_void, lit: c_int);
	pub fn kissat_solve(slv: *mut c_void) -> c_int;
	pub fn kissat_value(slv: *mut c_void, lit: c_int) -> c_int;
	pub fn kissat_set_terminate(
		slv: *mut c_void,
		data: *mut c_void,
		cb: Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);

	// Additional C-API functions in Kissat
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
