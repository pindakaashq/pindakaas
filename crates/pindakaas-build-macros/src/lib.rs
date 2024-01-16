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
				pub fn [<$prefix _connect_external_propagator>](slv: *mut std::ffi::c_void, prop: *mut std::ffi::c_void);
				pub fn [<$prefix _disconnect_external_propagator>](slv: *mut std::ffi::c_void);
				pub fn [<$prefix _add_observed_var>](slv: *mut std::ffi::c_void, var: i32);
				pub fn [<$prefix _remove_observed_var>](slv: *mut std::ffi::c_void, var: i32);
				pub fn [<$prefix _reset_observed_vars>](slv: *mut std::ffi::c_void);
				pub fn [<$prefix _is_decision>](slv: *mut std::ffi::c_void, lit: i32) -> bool;
				pub fn [<$prefix _phase>](slv: *mut std::ffi::c_void, lit: i32);
				pub fn [<$prefix _unphase>](slv: *mut std::ffi::c_void, lit: i32);
				pub fn [<$prefix _prop_init>](state: *mut std::ffi::c_void) -> *mut std::ffi::c_void;
				pub fn [<$prefix _prop_release>](prop: *mut std::ffi::c_void);
				pub fn [<$prefix _prop_lazy>](prop: *mut std::ffi::c_void, is_lazy: bool);
				pub fn [<$prefix _prop_set_notify_assignment>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, *const i32, bool)>);
				pub fn [<$prefix _prop_set_notify_new_decision_level>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void)>);
				pub fn [<$prefix _prop_set_notify_backtrack>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, usize)>);
				pub fn [<$prefix _prop_set_check_model>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, usize, *const i32) -> bool>);
				pub fn [<$prefix _prop_set_decide>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> i32>);
				pub fn [<$prefix _prop_set_propagate>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> i32>);
				pub fn [<$prefix _prop_set_add_reason_clause_lit>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, i32) -> i32>);
				pub fn [<$prefix _prop_set_has_external_clause>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> bool>);
				pub fn [<$prefix _prop_set_add_external_clause_lit>](prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> i32>);
			}
			pub unsafe fn ipasir_connect_external_propagator(slv: *mut std::ffi::c_void, prop: *mut std::ffi::c_void) {
				[<$prefix _connect_external_propagator>](slv, prop)
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
			pub unsafe fn ipasir_phase(slv: *mut std::ffi::c_void, lit: i32) {
				[<$prefix _phase>](slv, lit)
			}
			pub unsafe fn ipasir_unphase(slv: *mut std::ffi::c_void, lit: i32) {
				[<$prefix _unphase>](slv, lit)
			}
			pub unsafe fn ipasir_prop_init(state: *mut std::ffi::c_void) -> *mut std::ffi::c_void {
				[<$prefix _prop_init>](state)
			}
			pub unsafe fn ipasir_prop_release(prop: *mut std::ffi::c_void) {
				[<$prefix _prop_release>](prop)
			}
			pub unsafe fn ipasir_prop_lazy(prop: *mut std::ffi::c_void, is_lazy: bool) {
				[<$prefix _prop_lazy>](prop, is_lazy)
			}
			pub unsafe fn ipasir_prop_set_notify_assignment(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, *const i32, bool)>) {
				[<$prefix _prop_set_notify_assignment>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_notify_new_decision_level(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void)>) {
				[<$prefix _prop_set_notify_new_decision_level>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_notify_backtrack(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, usize)>) {
				[<$prefix _prop_set_notify_backtrack>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_check_model(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, usize, *const i32) -> bool>) {
				[<$prefix _prop_set_check_model>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_decide(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> i32>) {
				[<$prefix _prop_set_decide>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_propagate(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> i32>) {
				[<$prefix _prop_set_propagate>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_add_reason_clause_lit(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, i32) -> i32>) {
				[<$prefix _prop_set_add_reason_clause_lit>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_has_external_clause(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> bool>) {
				[<$prefix _prop_set_has_external_clause>](prop, cb)
			}
			pub unsafe fn ipasir_prop_set_add_external_clause_lit(prop: *mut std::ffi::c_void, cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> i32>) {
				[<$prefix _prop_set_add_external_clause_lit>](prop, cb)
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
		"_disconnect_external_propagator",
		"_add_observed_var",
		"_remove_observed_var",
		"_reset_observed_vars",
		"_is_decision",
		"_phase",
		"_unphase",
		"_prop_init",
		"_prop_release",
		"_prop_lazy",
		"_prop_set_notify_assignment",
		"_prop_set_notify_new_decision_level",
		"_prop_set_notify_backtrack",
		"_prop_set_check_model",
		"_prop_set_decide",
		"_prop_set_propagate",
		"_prop_set_add_reason_clause_lit",
		"_prop_set_has_external_clause",
		"_prop_set_add_external_clause_lit",
	] {
		build.define(&format!("ipasir{f}"), format!("{prefix}{f}").as_ref());
	}
}
