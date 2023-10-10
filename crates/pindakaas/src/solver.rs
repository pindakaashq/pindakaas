use std::num::NonZeroI32;

use crate::{ClauseDatabase, Lit, Valuation, Var};

#[cfg(feature = "splr")]
pub mod splr;

#[cfg(feature = "libloading")]
pub mod libloading;

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
