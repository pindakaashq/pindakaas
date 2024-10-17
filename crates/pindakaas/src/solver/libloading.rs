use std::{
	ffi::{c_char, c_int, c_void, CStr},
	num::NonZeroI32,
	ptr,
};

use libloading::{Library, Symbol};

use crate::{
	solver::{
		get_trampoline0, get_trampoline1, ExplIter, FFIPointer, FailedAssumtions, LearnCallback,
		SlvTermSignal, SolveAssuming, SolveResult, Solver, TermCallback, VarFactory,
	},
	ClauseDatabase, ConditionalDatabase, Lit, Result, Valuation, Var,
};

#[derive(Debug)]
pub struct IpasirFailed<'lib> {
	slv: *mut c_void,
	failed_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> c_int>,
}

#[derive(Debug)]
pub struct IpasirLibrary {
	lib: Library,
}

#[derive(Debug)]
pub struct IpasirSol<'lib> {
	slv: *mut c_void,
	value_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> i32>,
}

#[derive(Debug)]
pub struct IpasirSolver<'lib> {
	/// The raw pointer to the Intel SAT solver.
	slv: *mut c_void,
	/// The variable factory for this solver.
	vars: VarFactory,

	/// The callback used when a clause is learned.
	learn_cb: FFIPointer,
	/// The callback used to check whether the solver should terminate.
	term_cb: FFIPointer,

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

pub type SymResult<'a, S, E = libloading::Error> = std::result::Result<Symbol<'a, S>, E>;

// --- Helpers for C interface ---
impl FailedAssumtions for IpasirFailed<'_> {
	fn fail(&self, lit: Lit) -> bool {
		let lit: i32 = lit.into();
		let failed = (self.failed_fn)(self.slv, lit);
		failed != 0
	}
}

impl IpasirLibrary {
	fn ipasir_add_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_add") }
	}

	fn ipasir_assume_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_assume") }
	}

	fn ipasir_failed_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> c_int> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_failed") }
	}

	fn ipasir_init_sym(&self) -> SymResult<extern "C" fn() -> *mut c_void> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_init") }
	}

	fn ipasir_release_sym(&self) -> SymResult<extern "C" fn(*mut c_void)> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_release") }
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
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_set_learn") }
	}

	fn ipasir_set_terminate_sym(
		&self,
	) -> SymResult<
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_set_terminate") }
	}
	fn ipasir_signature_sym(&self) -> SymResult<extern "C" fn() -> *const c_char> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_signature") }
	}

	fn ipasir_solve_sym(&self) -> SymResult<extern "C" fn(*mut c_void) -> c_int> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_solve") }
	}
	fn ipasir_value_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> i32> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_val") }
	}

	pub fn new_solver(&self) -> IpasirSolver<'_> {
		IpasirSolver {
			slv: (self.ipasir_init_sym().unwrap())(),
			vars: VarFactory::default(),
			learn_cb: FFIPointer::default(),
			term_cb: FFIPointer::default(),
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

	pub fn signature(&self) -> &str {
		// SAFETY: We assume that the signature function as part of the IPASIR
		// interface returns a valid C string.
		unsafe { CStr::from_ptr((self.ipasir_signature_sym().unwrap())()) }
			.to_str()
			.unwrap()
	}
}

impl TryFrom<Library> for IpasirLibrary {
	type Error = libloading::Error;

	fn try_from(lib: Library) -> Result<Self, Self::Error> {
		let lib = IpasirLibrary { lib };
		let _ = lib.ipasir_signature_sym()?;
		let _ = lib.ipasir_init_sym()?;
		let _ = lib.ipasir_release_sym()?;
		let _ = lib.ipasir_add_sym()?;
		let _ = lib.ipasir_assume_sym()?;
		let _ = lib.ipasir_solve_sym()?;
		let _ = lib.ipasir_value_sym()?;
		let _ = lib.ipasir_failed_sym()?;
		let _ = lib.ipasir_set_terminate_sym()?;
		let _ = lib.ipasir_set_learn_sym()?;
		Ok(lib)
	}
}

impl Valuation for IpasirSol<'_> {
	fn value(&self, lit: Lit) -> bool {
		let lit: i32 = lit.into();
		let val = (self.value_fn)(self.slv, lit);
		match val {
			_ if val == lit => true,
			_ if val == -lit => false,
			_ => {
				debug_assert_eq!(val, 0); // zero according to spec, both value are valid
				false
			}
		}
	}
}

impl<'lib> IpasirSolver<'lib> {
	fn failed_obj(&self) -> IpasirFailed<'lib> {
		IpasirFailed {
			slv: self.slv,
			failed_fn: self.failed_fn.clone(),
		}
	}
	fn sol_obj(&self) -> IpasirSol<'lib> {
		IpasirSol {
			slv: self.slv,
			value_fn: self.value_fn.clone(),
		}
	}
}

impl<'lib> ClauseDatabase for IpasirSolver<'lib> {
	type CondDB = Self;

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
	fn new_var(&mut self) -> Var {
		self.vars.next().expect("variable pool exhaused")
	}
	fn with_conditions(&mut self, conditions: Vec<Lit>) -> ConditionalDatabase<Self::CondDB> {
		ConditionalDatabase {
			db: self,
			conditions,
		}
	}
}

impl<'lib> Drop for IpasirSolver<'lib> {
	fn drop(&mut self) {
		// Release the solver.
		(self.release_fn)(self.slv);
	}
}

impl<'lib> LearnCallback for IpasirSolver<'lib> {
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		const MAX_LEN: c_int = 512;
		if let Some(mut cb) = cb {
			let wrapped_cb = move |clause: *const i32| {
				let mut iter = ExplIter(clause).map(|i: i32| Lit(NonZeroI32::new(i).unwrap()));
				cb(&mut iter);
			};

			let trampoline = get_trampoline1(&wrapped_cb);
			self.learn_cb = FFIPointer::new(wrapped_cb);
			(self.set_learn_fn)(self.slv, self.learn_cb.get_ptr(), MAX_LEN, Some(trampoline));
		} else {
			self.learn_cb = FFIPointer::default();
			(self.set_learn_fn)(self.slv, ptr::null_mut(), MAX_LEN, None);
		}
	}
}

impl<'lib> SolveAssuming for IpasirSolver<'lib> {
	type FailFn = IpasirFailed<'lib>;

	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&<Self as Solver>::ValueFn),
		FailCb: FnOnce(&Self::FailFn),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult {
		for i in assumptions {
			(self.assume_fn)(self.slv, i.into());
		}
		match self.solve(on_sol) {
			SolveResult::Unsat => {
				on_fail(&self.failed_obj());
				SolveResult::Unsat
			}
			r => r,
		}
	}
}

impl<'lib> Solver for IpasirSolver<'lib> {
	type ValueFn = IpasirSol<'lib>;

	fn signature(&self) -> &str {
		// SAFETY: We assume that the signature function as part of the IPASIR
		// interface returns a valid C string.
		unsafe { CStr::from_ptr((self.signature_fn)()) }
			.to_str()
			.unwrap()
	}

	fn solve<SolCb: FnOnce(&Self::ValueFn)>(&mut self, on_sol: SolCb) -> SolveResult {
		let res = (self.solve_fn)(self.slv);
		match res {
			10 => {
				// 10 -> Sat
				on_sol(&self.sol_obj());
				SolveResult::Sat
			}
			20 => SolveResult::Unsat, // 20 -> Unsat
			_ => {
				debug_assert_eq!(res, 0); // According to spec should be 0, unknown
				SolveResult::Unknown
			}
		}
	}
}

impl<'lib> TermCallback for IpasirSolver<'lib> {
	fn set_terminate_callback<F: FnMut() -> SlvTermSignal + 'static>(&mut self, cb: Option<F>) {
		if let Some(mut cb) = cb {
			let wrapped_cb = move || -> c_int {
				match cb() {
					SlvTermSignal::Continue => c_int::from(0),
					SlvTermSignal::Terminate => c_int::from(1),
				}
			};
			let trampoline = get_trampoline0(&wrapped_cb);
			self.term_cb = FFIPointer::new(wrapped_cb);
			(self.set_terminate_fn)(self.slv, self.term_cb.get_ptr(), Some(trampoline));
		} else {
			self.term_cb = FFIPointer::default();
			(self.set_terminate_fn)(self.slv, ptr::null_mut(), None);
		}
	}
}
