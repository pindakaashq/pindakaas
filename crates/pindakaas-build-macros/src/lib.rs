use cc::Build;
pub use paste::paste;

#[macro_export(local_inner_macros)]
macro_rules! ipasir_definitions {
	($prefix:ident) => {
		paste! {
			extern "C" {
				pub fn [<$prefix _signature>]() -> *const std::ffi::c_char;
				pub fn [<$prefix _init>]() -> *mut std::ffi::c_void;
				pub fn [<$prefix _release>](slv: *mut std::ffi::c_void);
				pub fn [<$prefix _add>](slv: *mut std::ffi::c_void, lit: i32);
				pub fn [<$prefix _assume>](slv: *mut std::ffi::c_void, lit: i32);
				pub fn [<$prefix _solve>](slv: *mut std::ffi::c_void) -> std::ffi::c_int;
				pub fn [<$prefix _val>](slv: *mut std::ffi::c_void, lit: i32) -> i32;
				pub fn [<$prefix _failed>](slv: *mut std::ffi::c_void, lit: i32) -> std::ffi::c_int;
				pub fn [<$prefix _set_terminate>](
					slv: *mut std::ffi::c_void,
					data: *mut std::ffi::c_void,
					cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> std::ffi::c_int>,
				);
				pub fn [<$prefix _set_learn>](
					slv: *mut std::ffi::c_void,
					data: *mut std::ffi::c_void,
					max_len: std::ffi::c_int,
					cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, *const i32)>,
				);
			}
			pub unsafe fn ipasir_signature() -> *const std::ffi::c_char {
				[<$prefix _signature>]()
			}
			pub unsafe fn ipasir_init() -> *mut std::ffi::c_void {
				[<$prefix _init>]()
			}
			pub unsafe fn ipasir_release(slv: *mut std::ffi::c_void) {
				[<$prefix _release>](slv)
			}
			pub unsafe fn ipasir_add(slv: *mut std::ffi::c_void, lit: i32) {
				[<$prefix _add>](slv, lit)
			}
			pub unsafe fn ipasir_assume(slv: *mut std::ffi::c_void, lit: i32) {
				[<$prefix _assume>](slv, lit)
			}
			pub unsafe fn ipasir_solve(slv: *mut std::ffi::c_void) -> std::ffi::c_int {
				[<$prefix _solve>](slv)
			}
			pub unsafe fn ipasir_val(slv: *mut std::ffi::c_void, lit: i32) -> i32 {
				[<$prefix _val>](slv, lit)
			}
			pub unsafe fn ipasir_failed(slv: *mut std::ffi::c_void, lit: i32) -> std::ffi::c_int {
				[<$prefix _failed>](slv, lit)
			}
			pub unsafe fn ipasir_set_terminate (
				slv: *mut std::ffi::c_void,
				data: *mut std::ffi::c_void,
				cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> std::ffi::c_int>,
			) {
				[<$prefix _set_terminate>](slv, data, cb)
			}
			pub unsafe fn ipasir_set_learn(
				slv: *mut std::ffi::c_void,
				data: *mut std::ffi::c_void,
				max_len: std::ffi::c_int,
				cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, *const i32)>,
			){
				[<$prefix _set_learn>](slv, data, max_len, cb)
			}
		}
	};
}

#[macro_export(local_inner_macros)]
macro_rules! ipasir_up_definitions {
	($prefix:ident) => {
		paste! {
			extern "C" {
				#[allow(clippy::too_many_arguments)]
				pub fn [<$prefix _connect_external_propagator>](
					slv: *mut std::ffi::c_void,
					propagator_data: *mut std::ffi::c_void,
					prop_notify_assignment: unsafe extern "C" fn(*mut std::ffi::c_void, i32, bool),
					prop_notify_new_decision_level: unsafe extern "C" fn(*mut std::ffi::c_void),
					prop_notify_backtrack: unsafe extern "C" fn(*mut std::ffi::c_void, usize, bool),
					prop_cb_check_found_model: unsafe extern "C" fn(*mut std::ffi::c_void, *const i32, usize) -> bool,
					prop_cb_has_external_clause: unsafe extern "C" fn(*mut std::ffi::c_void) -> bool,
					prop_cb_add_external_clause_lit: unsafe extern "C" fn(*mut std::ffi::c_void) -> i32,
					is_lazy: bool,
					prop_cb_decide: unsafe extern "C" fn(*mut std::ffi::c_void) -> i32,
					prop_cb_propagate: unsafe extern "C" fn(*mut std::ffi::c_void) -> i32,
					prop_cb_add_reason_clause_lit: unsafe extern "C" fn(*mut std::ffi::c_void, i32) -> i32,
				);
				pub fn [<$prefix _disconnect_external_propagator>](slv: *mut std::ffi::c_void);
				pub fn [<$prefix _add_observed_var>](slv: *mut std::ffi::c_void, var: i32);
				pub fn [<$prefix _remove_observed_var>](slv: *mut std::ffi::c_void, var: i32);
				pub fn [<$prefix _reset_observed_vars>](slv: *mut std::ffi::c_void);
				pub fn [<$prefix _is_decision>](slv: *mut std::ffi::c_void, lit: i32) -> bool;
			}
			#[allow(clippy::too_many_arguments)]
			pub unsafe fn ipasir_connect_external_propagator(
				slv: *mut std::ffi::c_void,
					propagator_data: *mut std::ffi::c_void,
					prop_notify_assignment: unsafe extern "C" fn(*mut std::ffi::c_void, i32, bool),
					prop_notify_new_decision_level: unsafe extern "C" fn(*mut std::ffi::c_void),
					prop_notify_backtrack: unsafe extern "C" fn(*mut std::ffi::c_void, usize, bool),
					prop_cb_check_found_model: unsafe extern "C" fn(*mut std::ffi::c_void, *const i32, usize) -> bool,
					prop_cb_has_external_clause: unsafe extern "C" fn(*mut std::ffi::c_void) -> bool,
					prop_cb_add_external_clause_lit: unsafe extern "C" fn(*mut std::ffi::c_void) -> i32,
					is_lazy: bool,
					prop_cb_decide: unsafe extern "C" fn(*mut std::ffi::c_void) -> i32,
					prop_cb_propagate: unsafe extern "C" fn(*mut std::ffi::c_void) -> i32,
					prop_cb_add_reason_clause_lit: unsafe extern "C" fn(*mut std::ffi::c_void, i32) -> i32,
			){
				[<$prefix _connect_external_propagator>](slv, propagator_data, prop_notify_assignment, prop_notify_new_decision_level, prop_notify_backtrack, prop_cb_check_found_model, prop_cb_has_external_clause, prop_cb_add_external_clause_lit, is_lazy, prop_cb_decide, prop_cb_propagate, prop_cb_add_reason_clause_lit)
			}
			pub unsafe fn ipasir_disconnect_external_propagator(slv: *mut std::ffi::c_void) {
				[<$prefix _disconnect_external_propagator>](slv)
			}
			pub unsafe fn ipasir_add_observed_var(slv: *mut std::ffi::c_void, var: i32) {
				[<$prefix _add_observed_var>](slv, var)
			}
			pub unsafe fn ipasir_remove_observed_var(slv: *mut std::ffi::c_void, var: i32) {
				[<$prefix _remove_observed_var>](slv, var)
			}
			pub unsafe fn ipasir_reset_observed_vars(slv: *mut std::ffi::c_void) {
				[<$prefix _reset_observed_vars>](slv)
			}
			pub unsafe fn ipasir_is_decision(slv: *mut std::ffi::c_void, lit: i32) -> bool {
				[<$prefix _is_decision>](slv, lit)
			}
		}
	}
}

/// Function that renames the standard `ipasir_` when using the `cc` crate to
/// avoid conflicts when linking.
pub fn change_ipasir_prefix(build: &mut Build, prefix: &str) {
	for f in [
		"_signature",
		"_init",
		"_release",
		"_add",
		"_assume",
		"_solve",
		"_val",
		"_failed",
		"_set_terminate",
		"_set_learn",
		"_connect_external_propagator",
		"_get_external_propagator",
		"_disconnect_external_propagator",
		"_add_observed_var",
		"_remove_observed_var",
		"_reset_observed_vars",
		"_is_decision",
	] {
		let _ = build.define(&format!("ipasir{f}"), format!("{prefix}{f}").as_ref());
	}
}
