use std::{
	ffi::{c_char, c_int, c_void, CStr},
	num::NonZeroI32,
	ptr,
};

use libloading::{Library, Symbol};

use super::{
	get_trampoline0, get_trampoline1, ExplIter, FailFn, SolveResult, Solver, SolverAction,
	VarFactory,
};
use crate::{ClauseDatabase, Lit, Result, Valuation};

pub struct IpasirLibrary {
	lib: Library,
}

pub type SymResult<'a, S, E = libloading::Error> = std::result::Result<Symbol<'a, S>, E>;

impl IpasirLibrary {
	fn ipasir_signature_sym(&self) -> SymResult<extern "C" fn() -> *const c_char> {
		unsafe { self.lib.get(b"ipasir_signature") }
	}

	fn ipasir_init_sym(&self) -> SymResult<extern "C" fn() -> *mut c_void> {
		unsafe { self.lib.get(b"ipasir_init") }
	}

	fn ipasir_release_sym(&self) -> SymResult<extern "C" fn(*mut c_void)> {
		unsafe { self.lib.get(b"ipasir_release") }
	}

	fn ipasir_add_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		unsafe { self.lib.get(b"ipasir_add") }
	}

	fn ipasir_assume_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		unsafe { self.lib.get(b"ipasir_assume") }
	}

	fn ipasir_solve_sym(&self) -> SymResult<extern "C" fn(*mut c_void) -> c_int> {
		unsafe { self.lib.get(b"ipasir_solve") }
	}
	fn ipasir_value_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> i32> {
		unsafe { self.lib.get(b"ipasir_val") }
	}

	fn ipasir_failed_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> c_int> {
		unsafe { self.lib.get(b"ipasir_failed") }
	}

	fn ipasir_set_terminate_sym(
		&self,
	) -> SymResult<
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	> {
		unsafe { self.lib.get(b"ipasir_set_terminate") }
	}

	fn ipasir_set_learn_sym(
		&self,
	) -> SymResult<
		extern "C" fn(
			*mut c_void,
			*mut c_void,
			c_int,
			Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
		),
	> {
		unsafe { self.lib.get(b"ipasir_set_learn") }
	}

	pub fn signature(&self) -> &str {
		unsafe { CStr::from_ptr((self.ipasir_signature_sym().unwrap())()) }
			.to_str()
			.unwrap()
	}

	pub fn new_solver(&self) -> IpasirSolver<'_> {
		IpasirSolver {
			slv: (self.ipasir_init_sym().unwrap())(),
			next_var: VarFactory::default(),
			signature_fn: self.ipasir_signature_sym().unwrap(),
			release_fn: self.ipasir_release_sym().unwrap(),
			add_fn: self.ipasir_add_sym().unwrap(),
			assume_fn: self.ipasir_assume_sym().unwrap(),
			solve_fn: self.ipasir_solve_sym().unwrap(),
			value_fn: self.ipasir_value_sym().unwrap(),
			failed_fn: self.ipasir_failed_sym().unwrap(),
			set_terminate_fn: self.ipasir_set_terminate_sym().unwrap(),
			set_learn_fn: self.ipasir_set_learn_sym().unwrap(),
		}
	}
}

impl TryFrom<Library> for IpasirLibrary {
	type Error = libloading::Error;

	fn try_from(lib: Library) -> Result<Self, Self::Error> {
		let lib = IpasirLibrary { lib };
		lib.ipasir_signature_sym()?;
		lib.ipasir_init_sym()?;
		lib.ipasir_release_sym()?;
		lib.ipasir_add_sym()?;
		lib.ipasir_assume_sym()?;
		lib.ipasir_solve_sym()?;
		lib.ipasir_value_sym()?;
		lib.ipasir_failed_sym()?;
		lib.ipasir_set_terminate_sym()?;
		lib.ipasir_set_learn_sym()?;
		Ok(lib)
	}
}

pub struct IpasirSolver<'lib> {
	slv: *mut c_void,
	next_var: VarFactory,
	signature_fn: Symbol<'lib, extern "C" fn() -> *const c_char>,
	release_fn: Symbol<'lib, extern "C" fn(*mut c_void)>,
	add_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32)>,
	assume_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32)>,
	solve_fn: Symbol<'lib, extern "C" fn(*mut c_void) -> c_int>,
	value_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> i32>,
	failed_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> c_int>,
	set_terminate_fn: Symbol<
		'lib,
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	>,
	set_learn_fn: Symbol<
		'lib,
		extern "C" fn(
			*mut c_void,
			*mut c_void,
			c_int,
			Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
		),
	>,
}

impl<'lib> Drop for IpasirSolver<'lib> {
	fn drop(&mut self) {
		(self.release_fn)(self.slv)
	}
}

impl<'lib> ClauseDatabase for IpasirSolver<'lib> {
	fn new_var(&mut self) -> Lit {
		self.next_var.next().expect("variable pool exhaused").into()
	}

	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, clause: I) -> Result {
		let mut added = false;
		for lit in clause.into_iter() {
			(self.add_fn)(self.slv, lit.into());
			added = true;
		}
		if added {
			(self.add_fn)(self.slv, 0);
		}
		Ok(())
	}
}

impl<'lib> Solver for IpasirSolver<'lib> {
	fn signature(&self) -> &str {
		unsafe { CStr::from_ptr((self.signature_fn)()) }
			.to_str()
			.unwrap()
	}

	fn solve<SolCb: FnOnce(&dyn Valuation), FailCb: FnOnce(&FailFn<'_>)>(
		&mut self,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult {
		let res = (self.solve_fn)(self.slv);
		match res {
			10 => {
				// 10 -> Sat
				let val_fn = |lit: Lit| {
					let lit: i32 = lit.into();
					let val = (self.value_fn)(self.slv, lit);
					match val {
						_ if val == lit => Some(true),
						_ if val == -lit => Some(false),
						_ => {
							debug_assert_eq!(val, 0); // zero according to spec, both value are valid
							None
						}
					}
				};
				on_sol(&val_fn);
				SolveResult::Sat
			}
			20 => {
				// 20 -> Unsat
				let fail_fn = |lit: Lit| {
					let lit: i32 = lit.into();
					let failed = (self.failed_fn)(self.slv, lit);
					failed != 0
				};
				on_fail(&fail_fn);
				SolveResult::Unsat
			}
			_ => {
				debug_assert_eq!(res, 0); // According to spec should be 0, unknown
				SolveResult::Unknown
			}
		}
	}

	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&dyn Valuation),
		FailCb: FnOnce(&FailFn<'_>),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult {
		for i in assumptions {
			(self.assume_fn)(self.slv, i.into());
		}
		self.solve(on_sol, on_fail)
	}

	fn set_terminate_callback<F: FnMut() -> SolverAction>(&mut self, cb: Option<F>) {
		if let Some(mut cb) = cb {
			let mut wrapped_cb = || -> c_int {
				match cb() {
					SolverAction::Continue => c_int::from(0),
					SolverAction::Terminate => c_int::from(1),
				}
			};
			let data = &mut wrapped_cb as *mut _ as *mut c_void;
			(self.set_terminate_fn)(self.slv, data, Some(get_trampoline0(&wrapped_cb)));
		} else {
			(self.set_terminate_fn)(self.slv, ptr::null_mut(), None);
		}
	}

	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>)>(
		&mut self,
		max_len: usize,
		cb: Option<F>,
	) {
		let max_len = max_len as c_int;
		if let Some(mut cb) = cb {
			let mut wrapped_cb = |clause: *const i32| {
				let mut iter = ExplIter(clause).map(|i: i32| Lit(NonZeroI32::new(i).unwrap()));
				cb(&mut iter)
			};
			let data = &mut wrapped_cb as *mut _ as *mut c_void;
			(self.set_learn_fn)(self.slv, data, max_len, Some(get_trampoline1(&wrapped_cb)));
		} else {
			(self.set_learn_fn)(self.slv, ptr::null_mut(), max_len, None);
		}
	}
}
