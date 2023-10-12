#[macro_export]
macro_rules! ipasir_definitions {
	() => {
		extern "C" {
			pub fn ipasir_signature() -> *const std::ffi::c_char;
			pub fn ipasir_init() -> *mut std::ffi::c_void;
			pub fn ipasir_release(slv: *mut std::ffi::c_void);
			pub fn ipasir_add(slv: *mut std::ffi::c_void, lit: i32);
			pub fn ipasir_assume(slv: *mut std::ffi::c_void, lit: i32);
			pub fn ipasir_solve(slv: *mut std::ffi::c_void) -> std::ffi::c_int;
			pub fn ipasir_val(slv: *mut std::ffi::c_void, lit: i32) -> i32;
			pub fn ipasir_failed(slv: *mut std::ffi::c_void, lit: i32) -> std::ffi::c_int;
			pub fn ipasir_set_terminate(
				slv: *mut std::ffi::c_void,
				data: *mut std::ffi::c_void,
				cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void) -> std::ffi::c_int>,
			);
			pub fn ipasir_set_learn(
				ptr: *mut std::ffi::c_void,
				data: *mut std::ffi::c_void,
				max_len: std::ffi::c_int,
				cb: Option<unsafe extern "C" fn(*mut std::ffi::c_void, *const i32)>,
			);
		}
	};
}
