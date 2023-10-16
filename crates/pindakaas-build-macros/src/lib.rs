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

/// Function that renames the standard `ipasir_` when using the `cc` crate to
/// avoid conflicts when linking.
pub fn change_ipasir_prefix(build: &mut Build, prefix: &str) {
	build
		.define("ipasir_signature", format!("{prefix}_signature").as_ref())
		.define("ipasir_init", format!("{prefix}_init").as_ref())
		.define("ipasir_release", format!("{prefix}_release").as_ref())
		.define("ipasir_add", format!("{prefix}_add").as_ref())
		.define("ipasir_assume", format!("{prefix}_assume").as_ref())
		.define("ipasir_solve", format!("{prefix}_solve").as_ref())
		.define("ipasir_val", format!("{prefix}_val").as_ref())
		.define("ipasir_failed", format!("{prefix}_failed").as_ref())
		.define(
			"ipasir_set_terminate",
			format!("{prefix}_set_terminate").as_ref(),
		)
		.define("ipasir_set_learn", format!("{prefix}_set_learn").as_ref());
}
