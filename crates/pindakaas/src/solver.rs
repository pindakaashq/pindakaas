//! This module contains common traits for Boolean satisfiability (SAT) solvers
//! as well as direct interfaces for different SAT solvers, which implement
//! these traits.

#[cfg(any(feature = "cadical", test))]
pub mod cadical;
#[cfg(feature = "intel-sat")]
pub mod intel_sat;
pub(crate) mod ipasir;
#[cfg(feature = "kissat")]
pub mod kissat;
#[cfg(feature = "libloading")]
pub mod libloading;
#[cfg(feature = "external-propagation")]
pub mod propagation;
#[cfg(feature = "splr")]
pub mod splr;

use std::num::NonZeroI32;

use crate::{ClauseDatabase, Lit, Valuation, Var, VarRange};

/// Trait implemented by solver that support assumptions, a list of literals
/// that are assumed to be true during the solving call. The resulting
/// [`SolveResult`] will allow inspection of which assumptions failed if the
/// formula is unsatisfiable under the assumptions.
pub trait Assumptions: Solver {
	/// Solve the formula with specified clauses under the given assumptions.
	///
	/// If the search is interrupted (see
	/// [`TerminateCallback::set_terminate_callback`]) the function returns
	/// unknown
	fn solve_assuming<I: IntoIterator<Item = Lit>>(
		&mut self,
		assumptions: I,
	) -> SolveResult<impl Valuation + '_, impl FailedAssumptions + '_>;
}

/// Trait implemented by the object given to the callback on detecting failure
pub trait FailedAssumptions {
	/// Check if the given assumption literal was used to prove the
	/// unsatisfiability of the formula under the assumptions used for the last
	/// SAT search.
	///
	/// Note that for literals 'lit' which are not assumption literals, the
	/// behavior of is not specified.
	fn fail(&self, lit: Lit) -> bool;
}

/// Trait implemented by solvers that support a callback when it infers a new
/// clause. In CDCL solvers, this generally happens when a clause is learned on
/// conflict.
pub trait LearnCallback: Solver {
	/// Set a callback function used to extract learned clauses up to a given
	/// length from the solver.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + 'static>(
		&mut self,
		cb: Option<F>,
	);
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// The result of a [`Solver::solve`] call.
pub enum SolveResult<Sol: Valuation, Fail = ()> {
	/// The solver found a satisfying assignment.
	Satisfied(Sol),
	/// The solver proved no satisfying assignment exists.
	Unsatisfiable(Fail),
	/// The solver was unable to determine whether a satisfying assignment
	/// exists given the computational limits.
	Unknown,
}

/// General trait for SAT solvers, extending the general [`ClauseDatabase`]
/// capabilities with being able to look for satisfying assignments.
pub trait Solver: ClauseDatabase {
	/// Solve the formula with specified clauses.
	///
	/// If the search is interrupted (see
	/// [`TerminateCallback::set_terminate_callback`]) the function returns
	/// unknown
	fn solve(&mut self) -> SolveResult<impl Valuation + '_, impl Sized>;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
/// Signal sent by termination callbacks telling the solver whether to continue
/// or terminate the search.
pub enum TermSignal {
	/// Continue the search process.
	Continue,
	/// Terminate the search process.
	Terminate,
}

/// Trait implemented by solvers that will make a call to the given callback
/// function to determine whether to continue or terminate the search.
pub trait TerminateCallback: Solver {
	/// Set a callback function used to indicate a termination requirement to
	/// the solver.
	///
	/// The solver will periodically call this function and check its return
	/// value during the search. Subsequent calls to this method override the
	/// previously set callback function.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	fn set_terminate_callback<F: FnMut() -> TermSignal + 'static>(&mut self, cb: Option<F>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// Type that helps create [`Var`]s in a consecutive manner.
pub struct VarFactory {
	pub(crate) next_var: Option<Var>,
}

impl VarFactory {
	/// Get the [`VarRange`] of all variables that have been created using this
	/// factory.
	pub fn emitted_vars(&self) -> VarRange {
		let mut start = Var(NonZeroI32::new(1).unwrap());
		let end = if let Some(v) = self.next_var {
			if let Some(prev) = v.prev_var() {
				prev
			} else {
				start = Var(NonZeroI32::new(2).unwrap());
				Var(NonZeroI32::new(1).unwrap())
			}
		} else {
			Var(NonZeroI32::MAX)
		};
		VarRange { start, end }
	}

	pub(crate) fn next_var_range(&mut self, size: usize) -> VarRange {
		let Some(start) = self.next_var else {
			panic!("unable to create more than `Var::MAX_VARS` variables")
		};
		match size {
			0 => VarRange::new(
				Var(NonZeroI32::new(2).unwrap()),
				Var(NonZeroI32::new(1).unwrap()),
			),
			1 => {
				self.next_var = start.next_var();
				VarRange::new(start, start)
			}
			_ if size > Var::MAX_VARS => {
				panic!("unable to create more than `Var::MAX_VARS` variables")
			}
			_ => {
				// Size is reduced by 1 since it includes self.next_var
				let size = NonZeroI32::new((size - 1) as i32).unwrap();
				if let Some(end) = start.checked_add(size) {
					// Set self.next_var to one after end
					self.next_var = end.next_var();
					VarRange::new(start, end)
				} else {
					// If end is None, then the range is too large
					panic!("unable to create more than `Var::MAX_VARS` variables")
				}
			}
		}
	}

	/// Get the number of variables that have been created using this factory.
	pub fn num_emitted_vars(&self) -> usize {
		if let Some(x) = self.next_var {
			x.0.get() as usize - 1
		} else {
			Var::MAX_VARS
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
