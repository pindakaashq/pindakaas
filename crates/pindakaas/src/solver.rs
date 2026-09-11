//! Solving clause databases and inspecting their models or failed assumptions.
//!
//! [`Solver`] is the common search interface. Optional traits expose
//! assumptions, learned-clause callbacks, and termination callbacks without
//! requiring every backend to implement those extensions.

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

/// Solving under temporary literals without adding them permanently.
pub trait Assumptions: Solver {
	/// Search under assumptions that hold for this call only.
	///
	/// If the search is interrupted (see
	/// [`TerminateCallback::set_terminate_callback`]) the function returns
	/// [`SolveResult::Unknown`].
	fn solve_assuming<I: IntoIterator<Item = Lit>>(
		&mut self,
		assumptions: I,
	) -> SolveResult<impl Valuation + '_, impl FailedAssumptions + '_>;
}

/// Membership queries on an unsatisfiable assumption core.
pub trait FailedAssumptions {
	/// Reports whether the assumption contributed to the last unsatisfiable
	/// result.
	///
	/// The result is unspecified when `lit` was not an assumption of that
	/// search.
	fn fail(&self, lit: Lit) -> bool;
}

/// Trait implemented by solvers that support a callback when it infers a new
/// clause. In CDCL solvers, this generally happens when a clause is learned on
/// conflict.
pub trait LearnCallback: Solver {
	/// Set the learned-clause callback, replacing the previous one.
	///
	/// The callback runs on whichever thread is solving.
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + Send + 'static>(
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

/// SAT search over the clauses accumulated in a [`ClauseDatabase`].
pub trait Solver: ClauseDatabase {
	/// Search the current permanent clauses.
	///
	/// If the search is interrupted (see
	/// [`TerminateCallback::set_terminate_callback`]) the function returns
	/// [`SolveResult::Unknown`].
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
	/// Set the periodically polled termination callback, replacing the previous
	/// one.
	///
	/// The callback runs on whichever thread is solving.
	fn set_terminate_callback<F: FnMut() -> TermSignal + Send + 'static>(&mut self, cb: Option<F>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// Allocation of consecutive [`Var`] identifiers.
pub struct VarFactory {
	pub(crate) next_var: Option<Var>,
}

impl VarFactory {
	/// Returns the range allocated so far, empty before the first allocation.
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
					self.next_var = end.next_var();
					VarRange::new(start, end)
				} else {
					panic!("unable to create more than `Var::MAX_VARS` variables")
				}
			}
		}
	}

	/// Number of identifiers allocated so far.
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
