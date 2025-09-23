//! This module contains pindakaas interface for (at runtime) dynamically loaded
//! libraries implementing the IPASIR interface.
use std::{
	ffi::{c_char, c_int, c_void, CStr},
	fmt,
	num::NonZeroI32,
	ptr,
};

use libloading::{Library, Symbol};

use crate::{
	solver::{
		ipasir::{get_trampoline0, get_trampoline1, ExplIter, IpasirLearnCb, IpasirTerminationCb},
		Assumptions, FailedAssumptions, LearnCallback, SolveResult, Solver, TermSignal,
		TerminateCallback, VarFactory,
	},
	ClauseDatabase, Lit, Result, Valuation,
};

#[derive(Debug)]
/// Wrapper around the `ipasir_failed` function that can be used to retrieve the
/// failed assumptions.
pub struct IpasirFailed<'lib> {
	slv: *mut c_void,
	failed_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> c_int>,
}

#[derive(Debug)]
/// A dynamically loaded library implementing the IPASIR interface.
pub struct IpasirLibrary {
	lib: Library,
}

#[derive(Debug)]
/// Wrapper around the `ipasir_value` function that can be used to retrieve the
/// value of a literal in the current satisfying assignment.
pub struct IpasirSol<'lib> {
	slv: *mut c_void,
	value_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> i32>,
}

/// Instance of a dynamically loaded IPASIR solver, created using a
/// [`IpasirLibrary`].
pub struct IpasirSolver<'lib> {
	/// The raw pointer to the Intel SAT solver.
	slv: *mut c_void,
	/// The variable factory for this solver.
	vars: VarFactory,

	/// The callback used when a clause is learned.
	learn_cb: Option<IpasirLearnCb>,
	/// The callback used to check whether the solver should terminate.
	term_cb: Option<IpasirTerminationCb>,

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

/// Internal wrapper to simplify the result of different symbol lookup
/// functions.
type SymResult<'a, S, E = libloading::Error> = std::result::Result<Symbol<'a, S>, E>;

// --- Helpers for C interface ---
impl FailedAssumptions for IpasirFailed<'_> {
	fn fail(&self, lit: Lit) -> bool {
		let lit: i32 = lit.into();
		let failed = (self.failed_fn)(self.slv, lit);
		failed != 0
	}
}

impl IpasirLibrary {
	fn ipasir_add_sym(&self) -> SymResult<'_, extern "C" fn(*mut c_void, i32)> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_add") }
	}

	fn ipasir_assume_sym(&self) -> SymResult<'_, extern "C" fn(*mut c_void, i32)> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_assume") }
	}

	fn ipasir_failed_sym(&self) -> SymResult<'_, extern "C" fn(*mut c_void, i32) -> c_int> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_failed") }
	}

	fn ipasir_init_sym(&self) -> SymResult<'_, extern "C" fn() -> *mut c_void> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_init") }
	}

	fn ipasir_release_sym(&self) -> SymResult<'_, extern "C" fn(*mut c_void)> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_release") }
	}

	fn ipasir_set_learn_sym(
		&self,
	) -> SymResult<
		'_,
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
		'_,
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_set_terminate") }
	}

	fn ipasir_signature_sym(&self) -> SymResult<'_, extern "C" fn() -> *const c_char> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_signature") }
	}

	fn ipasir_solve_sym(&self) -> SymResult<'_, extern "C" fn(*mut c_void) -> c_int> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_solve") }
	}

	fn ipasir_value_sym(&self) -> SymResult<'_, extern "C" fn(*mut c_void, i32) -> i32> {
		// SAFETY: We assume that if this symbol is present, then it is part of a
		// valid implementation of the IPASIR interface.
		unsafe { self.lib.get(b"ipasir_val") }
	}

	/// Create a new solver instance that uses the IPASIR methods included in
	/// the [`IpasirLibrary`].
	pub fn new_solver(&self) -> IpasirSolver<'_> {
		IpasirSolver {
			slv: (self.ipasir_init_sym().unwrap())(),
			vars: VarFactory::default(),
			learn_cb: None,
			term_cb: None,
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

	/// Wrapper for the `ipasir_signature` function.
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

impl IpasirSolver<'_> {
	fn failed_obj(&self) -> IpasirFailed<'_> {
		IpasirFailed {
			slv: self.slv,
			failed_fn: self.failed_fn.clone(),
		}
	}

	/// Wrapper for the `ipasir_signature` function.
	pub fn signature(&self) -> &str {
		// SAFETY: We assume that the signature function as part of the IPASIR
		// interface returns a valid C string.
		unsafe { CStr::from_ptr((self.signature_fn)()) }
			.to_str()
			.unwrap()
	}

	fn sol_obj(&self) -> IpasirSol<'_> {
		IpasirSol {
			slv: self.slv,
			value_fn: self.value_fn.clone(),
		}
	}
}

impl Assumptions for IpasirSolver<'_> {
	#[expect(
		refining_impl_trait,
		reason = "user can use more specific type if needed"
	)]
	fn solve_assuming<I: IntoIterator<Item = Lit>>(
		&mut self,
		assumptions: I,
	) -> SolveResult<IpasirSol<'_>, IpasirFailed<'_>> {
		for i in assumptions {
			(self.assume_fn)(self.slv, i.into());
		}
		self.solve()
	}
}

impl ClauseDatabase for IpasirSolver<'_> {
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
		let mut added = false;
		for &lit in clause {
			(self.add_fn)(self.slv, lit.into());
			added = true;
		}
		if added {
			(self.add_fn)(self.slv, 0);
		}
		Ok(())
	}

	fn new_var_range(&mut self, len: usize) -> crate::VarRange {
		self.vars.next_var_range(len)
	}
}

impl Drop for IpasirSolver<'_> {
	fn drop(&mut self) {
		// Release the solver.
		(self.release_fn)(self.slv);
	}
}

impl LearnCallback for IpasirSolver<'_> {
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		const MAX_LEN: c_int = 512;
		if let Some(mut cb) = cb {
			let mut wrapped_cb = Box::new(move |clause: *const i32| {
				let mut iter = ExplIter(clause).map(|i: i32| Lit(NonZeroI32::new(i).unwrap()));
				cb(&mut iter);
			});
			let (data_ptr, fn_ptr) = get_trampoline1(&mut wrapped_cb);
			self.learn_cb = Some(wrapped_cb);
			(self.set_learn_fn)(self.slv, data_ptr, MAX_LEN, Some(fn_ptr));
		} else {
			self.learn_cb = None;
			(self.set_learn_fn)(self.slv, ptr::null_mut(), MAX_LEN, None);
		}
	}
}

impl Solver for IpasirSolver<'_> {
	#[expect(
		refining_impl_trait,
		reason = "user can use more specific type if needed"
	)]
	fn solve(&mut self) -> SolveResult<IpasirSol<'_>, IpasirFailed<'_>> {
		let res = (self.solve_fn)(self.slv);
		match res {
			10 => SolveResult::Satisfied(self.sol_obj()), // 10 -> Sat
			20 => SolveResult::Unsatisfiable(self.failed_obj()), // 20 -> Unsat
			_ => {
				debug_assert_eq!(res, 0); // According to spec should be 0, unknown
				SolveResult::Unknown
			}
		}
	}
}

impl TerminateCallback for IpasirSolver<'_> {
	fn set_terminate_callback<F: FnMut() -> TermSignal + 'static>(&mut self, cb: Option<F>) {
		if let Some(mut cb) = cb {
			let mut wrapped_cb = Box::new(move || -> c_int {
				match cb() {
					TermSignal::Continue => c_int::from(0),
					TermSignal::Terminate => c_int::from(1),
				}
			});
			let (data_ptr, fn_ptr) = get_trampoline0(&mut wrapped_cb);
			self.term_cb = Some(wrapped_cb);
			(self.set_terminate_fn)(self.slv, data_ptr, Some(fn_ptr));
		} else {
			self.term_cb = None;
			(self.set_terminate_fn)(self.slv, ptr::null_mut(), None);
		}
	}
}

impl fmt::Debug for IpasirSolver<'_> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("IpasirSolver")
			.field("slv", &self.slv)
			.field("vars", &self.vars)
			.field(
				"learn_cb",
				&self.learn_cb.as_ref().map(|b| {
					let p: *const _ = b.as_ref();
					p
				}),
			)
			.field(
				"term_cb",
				&self.learn_cb.as_ref().map(|b| {
					let p: *const _ = b.as_ref();
					p
				}),
			)
			.finish()
	}
}
