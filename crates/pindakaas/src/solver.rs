use std::{ffi::c_void, num::NonZeroI32, ops::RangeInclusive};

use crate::{ClauseDatabase, Lit, Valuation, Var};

pub mod libloading;

#[cfg(feature = "cadical")]
pub mod cadical;
#[cfg(feature = "intel-sat")]
pub mod intel_sat;
#[cfg(feature = "kissat")]
pub mod kissat;
#[cfg(feature = "splr")]
pub mod splr;

pub trait Solver: ClauseDatabase {
	/// Return the name and the version of SAT solver.
	fn signature(&self) -> &str;

	/// Solve the formula with specified clauses.
	///
	/// If the search is interrupted (see [`set_terminate_callback`]) the function
	/// returns unknown
	fn solve<SolCb: FnOnce(&dyn Valuation)>(&mut self, on_sol: SolCb) -> SolveResult;
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum SolveResult {
	Sat,
	Unsat,
	Unknown,
}

pub trait SolveAssuming: Solver {
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
}

/// Check if the given assumption literal was used to prove the unsatisfiability
/// of the formula under the assumptions used for the last SAT search.
///
/// Note that for literals 'lit' which are not assumption literals, the behavior
/// of is not specified.
pub type FailFn<'a> = dyn Fn(Lit) -> bool + 'a;

pub trait LearnCallback: Solver {
	/// Set a callback function used to extract learned clauses up to a given
	/// length from the solver.
	///
	/// WARNING: Subsequent calls to this method override the previously set
	/// callback function.
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>)>(&mut self, cb: Option<F>);
}

pub trait TermCallback: Solver {
	/// Set a callback function used to indicate a termination requirement to the
	/// solver.
	///
	/// The solver will periodically call this function and check its return value
	/// during the search. Subsequent calls to this method override the previously
	/// set callback function.
	fn set_terminate_callback<F: FnMut() -> SolverAction>(&mut self, cb: Option<F>);
}

pub enum SolverAction {
	Continue,
	Terminate,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarFactory {
	pub(crate) next_var: Option<Var>,
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

	pub fn next_range(&mut self, size: usize) -> Option<RangeInclusive<Var>> {
		let Some(start) = self.next_var else {
			return None;
		};
		match size {
			0 => Some(Var(NonZeroI32::new(2).unwrap())..=Var(NonZeroI32::new(1).unwrap())),
			_ if size > NonZeroI32::MAX.get() as usize => None,
			_ => {
				let size = NonZeroI32::new(size as i32).unwrap();
				if let Some(end) = start.checked_add(size) {
					self.next_var = end.checked_add(NonZeroI32::new(1).unwrap());
					Some(start..=end)
				} else {
					None
				}
			}
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
