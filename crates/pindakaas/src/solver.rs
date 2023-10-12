use std::{ffi::c_void, num::NonZeroI32};

use crate::{ClauseDatabase, Lit, Valuation, Var};

pub mod libloading;

#[cfg(feature = "cadical")]
pub mod cadical;
#[cfg(feature = "intel-sat")]
pub mod intel_sat;
#[cfg(feature = "splr")]
pub mod splr;

pub trait Solver: ClauseDatabase {
	/// Return the name and the version of SAT solving library.
	fn signature(&self) -> &str;

	/// Solve the formula with specified clauses.
	///
	/// If the search is interrupted (see [`set_terminate_callback`]) the function
	/// returns unknown
	fn solve<SolCb: FnOnce(&dyn Valuation), FailCb: FnOnce(&FailFn<'_>)>(
		&mut self,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult;

	/// Solve the formula with specified clauses under the given assumptions.
	///
	/// If the search is interrupted (see [`set_terminate_callback`]) the function
	/// returns unknown
	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&dyn Valuation),
		FailCb: FnOnce(&FailFn<'_>),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult;

	/// Set a callback function used to indicate a termination requirement to the
	/// solver.
	///
	/// The solver will periodically call this function and check its return value
	/// during the search. Subsequent calls to this method override the previously
	/// set callback function.
	fn set_terminate_callback<F: FnMut() -> SolverAction>(&mut self, cb: Option<F>);

	/// Set a callback function used to extract learned clauses up to a given
	/// length from the solver.
	///
	/// The solver will call this function for each learned clause that satisfies
	/// the maximum length (literal count) condition. Subsequent calls to this
	/// method override the previously set callback function.
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>)>(
		&mut self,
		max_len: usize,
		cb: Option<F>,
	);
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum SolveResult {
	Sat,
	Unsat,
	Unknown,
}

/// Check if the given assumption literal was used to prove the unsatisfiability
/// of the formula under the assumptions used for the last SAT search.
///
/// Note that for literals 'lit' which are not assumption literals, the behavior
/// of is not specified.
pub type FailFn<'a> = dyn Fn(Lit) -> bool + 'a;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarFactory {
	pub(crate) next_var: Option<Var>,
}

pub enum SolverAction {
	Continue,
	Terminate,
}

impl VarFactory {
	const MAX_VARS: usize = NonZeroI32::MAX.get() as usize;

	pub fn emited_vars(&self) -> usize {
		if let Some(x) = self.next_var {
			x.0.get() as usize - 1
		} else {
			Self::MAX_VARS
		}
	}
}

impl Default for VarFactory {
	fn default() -> Self {
		Self {
			next_var: Some(Var(NonZeroI32::new(1).unwrap())),
		}
	}
}

impl Iterator for VarFactory {
	type Item = Var;

	fn next(&mut self) -> Option<Self::Item> {
		let var = self.next_var;
		if let Some(var) = var {
			self.next_var = var.next_var();
		}
		var
	}
}

#[allow(unused_macros)]
macro_rules! ipasir_solver {
	($loc:ident, $name:ident) => {
		pub struct $name {
			ptr: *mut std::ffi::c_void,
			vars: $crate::solver::VarFactory,
		}

		impl Default for $name {
			fn default() -> Self {
				Self {
					ptr: unsafe { $loc::ipasir_init() },
					vars: crate::solver::VarFactory::default(),
				}
			}
		}

		impl Drop for $name {
			fn drop(&mut self) {
				unsafe { $loc::ipasir_release(self.ptr) }
			}
		}

		impl crate::ClauseDatabase for $name {
			fn new_var(&mut self) -> crate::Lit {
				self.vars.next().expect("variable pool exhaused").into()
			}

			fn add_clause<I: IntoIterator<Item = crate::Lit>>(
				&mut self,
				clause: I,
			) -> crate::Result {
				let mut added = false;
				for lit in clause.into_iter() {
					unsafe { $loc::ipasir_add(self.ptr, lit.into()) };
					added = true;
				}
				if added {
					unsafe { $loc::ipasir_add(self.ptr, 0) };
				}
				Ok(())
			}
		}

		impl crate::solver::Solver for $name {
			fn signature(&self) -> &str {
				unsafe { std::ffi::CStr::from_ptr($loc::ipasir_signature()) }
					.to_str()
					.unwrap()
			}

			fn solve<
				SolCb: FnOnce(&dyn crate::Valuation),
				FailCb: FnOnce(&crate::solver::FailFn<'_>),
			>(
				&mut self,
				on_sol: SolCb,
				on_fail: FailCb,
			) -> crate::solver::SolveResult {
				let res = unsafe { $loc::ipasir_solve(self.ptr) };
				match res {
					10 => {
						// 10 -> Sat
						let val_fn = |lit: crate::Lit| {
							let lit: i32 = lit.into();
							let val = unsafe { $loc::ipasir_val(self.ptr, lit) };
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
						crate::solver::SolveResult::Sat
					}
					20 => {
						// 20 -> Unsat
						let fail_fn = |lit: crate::Lit| {
							let lit: i32 = lit.into();
							let failed = unsafe { $loc::ipasir_failed(self.ptr, lit) };
							failed != 0
						};
						on_fail(&fail_fn);
						crate::solver::SolveResult::Unsat
					}
					_ => {
						debug_assert_eq!(res, 0); // According to spec should be 0, unknown
						crate::solver::SolveResult::Unknown
					}
				}
			}

			fn solve_assuming<
				I: IntoIterator<Item = crate::Lit>,
				SolCb: FnOnce(&dyn crate::Valuation),
				FailCb: FnOnce(&crate::solver::FailFn<'_>),
			>(
				&mut self,
				assumptions: I,
				on_sol: SolCb,
				on_fail: FailCb,
			) -> crate::solver::SolveResult {
				for i in assumptions {
					unsafe { $loc::ipasir_assume(self.ptr, i.into()) }
				}
				self.solve(on_sol, on_fail)
			}

			fn set_terminate_callback<F: FnMut() -> crate::solver::SolverAction>(
				&mut self,
				cb: Option<F>,
			) {
				if let Some(mut cb) = cb {
					let mut wrapped_cb = || -> std::ffi::c_int {
						match cb() {
							crate::solver::SolverAction::Continue => std::ffi::c_int::from(0),
							crate::solver::SolverAction::Terminate => std::ffi::c_int::from(1),
						}
					};
					let data = &mut wrapped_cb as *mut _ as *mut std::ffi::c_void;
					unsafe {
						$loc::ipasir_set_terminate(
							self.ptr,
							data,
							Some(crate::solver::get_trampoline0(&wrapped_cb)),
						)
					}
				} else {
					unsafe { $loc::ipasir_set_terminate(self.ptr, std::ptr::null_mut(), None) }
				}
			}

			fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = crate::Lit>)>(
				&mut self,
				max_len: usize,
				cb: Option<F>,
			) {
				let max_len = max_len as std::ffi::c_int;
				if let Some(mut cb) = cb {
					let mut wrapped_cb = |clause: *const i32| {
						let mut iter = crate::solver::ExplIter(clause)
							.map(|i: i32| crate::Lit(std::num::NonZeroI32::new(i).unwrap()));
						cb(&mut iter)
					};
					let data = &mut wrapped_cb as *mut _ as *mut std::ffi::c_void;
					unsafe {
						$loc::ipasir_set_learn(
							self.ptr,
							data,
							max_len,
							Some(crate::solver::get_trampoline1(&wrapped_cb)),
						)
					}
				} else {
					unsafe { $loc::ipasir_set_learn(self.ptr, std::ptr::null_mut(), max_len, None) }
				}
			}
		}
	};
}
#[allow(unused_imports)]
pub(crate) use ipasir_solver;

type CB0<R> = unsafe extern "C" fn(*mut c_void) -> R;
unsafe extern "C" fn trampoline0<R, F: FnMut() -> R>(user_data: *mut c_void) -> R {
	let user_data = &mut *(user_data as *mut F);
	user_data()
}
fn get_trampoline0<R, F: FnMut() -> R>(_closure: &F) -> CB0<R> {
	trampoline0::<R, F>
}
type CB1<R, A> = unsafe extern "C" fn(*mut c_void, A) -> R;
unsafe extern "C" fn trampoline1<R, A, F: FnMut(A) -> R>(user_data: *mut c_void, arg1: A) -> R {
	let user_data = &mut *(user_data as *mut F);
	user_data(arg1)
}
fn get_trampoline1<R, A, F: FnMut(A) -> R>(_closure: &F) -> CB1<R, A> {
	trampoline1::<R, A, F>
}
/// Iterator over the elements of a null-terminated i32 array
#[derive(Debug, Clone, Copy)]
struct ExplIter(*const i32);
impl Iterator for ExplIter {
	type Item = i32;
	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		unsafe {
			if *self.0 == 0 {
				None
			} else {
				let ptr = self.0;
				self.0 = ptr.offset(1);
				Some(*ptr)
			}
		}
	}
}
