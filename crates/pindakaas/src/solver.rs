#[cfg(feature = "cadical")]
pub mod cadical;
#[cfg(feature = "intel-sat")]
pub mod intel_sat;
#[cfg(feature = "kissat")]
pub mod kissat;
#[cfg(feature = "splr")]
pub mod splr;

pub mod libloading;

#[cfg(feature = "ipasir-up")]
use std::any::Any;
use std::num::NonZeroI32;

pub use crate::helpers::VarRange;
use crate::{ClauseDatabase, Lit, Valuation, Var};

pub trait Solver: ClauseDatabase {
	type ValueFn: Valuation;
	/// Return the name and the version of SAT solver.
	fn signature(&self) -> &str;

	/// Solve the formula with specified clauses.
	///
	/// If the search is interrupted (see [`set_terminate_callback`]) the function
	/// returns unknown
	fn solve<SolCb: FnOnce(&Self::ValueFn)>(&mut self, on_sol: SolCb) -> SolveResult;
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum SolveResult {
	Sat,
	Unsat,
	Unknown,
}

pub trait SolveAssuming: Solver {
	type FailFn: FailedAssumtions;

	/// Solve the formula with specified clauses under the given assumptions.
	///
	/// If the search is interrupted (see [`set_terminate_callback`]) the function
	/// returns unknown
	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&Self::ValueFn),
		FailCb: FnOnce(&Self::FailFn),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult;
}

/// Trait implemented by the object given to the callback on detecting failure
pub trait FailedAssumtions {
	/// Check if the given assumption literal was used to prove the unsatisfiability
	/// of the formula under the assumptions used for the last SAT search.
	///
	/// Note that for literals 'lit' which are not assumption literals, the behavior
	/// of is not specified.
	fn fail(&self, lit: Lit) -> bool;
}

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

pub trait TermCallback: Solver {
	/// Set a callback function used to indicate a termination requirement to the
	/// solver.
	///
	/// The solver will periodically call this function and check its return value
	/// during the search. Subsequent calls to this method override the previously
	/// set callback function.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	fn set_terminate_callback<F: FnMut() -> SlvTermSignal + 'static>(&mut self, cb: Option<F>);
}

#[cfg(feature = "ipasir-up")]
pub trait PropagatingSolver: Solver + PropagatorAccess + MutPropagatorAccess
where
	Self::ValueFn: PropagatorAccess,
{
	/// Set Propagator implementation which allows to learn, propagate and
	/// backtrack based on external constraints.
	///
	/// Only one Propagator can be connected, any previous propagator will be
	/// overriden. This Propagator is notified of all changes to which it has
	/// subscribed, using the [`add_observed_var`] method.
	///
	/// # Warning
	///
	/// Calling this method automatically resets the observed variable set.
	fn set_external_propagator<P: Propagator + 'static>(&mut self, prop: Option<P>);

	fn add_observed_var(&mut self, var: Var);
	fn remove_observed_var(&mut self, var: Var);
	fn reset_observed_vars(&mut self);
}

/// Access the external propagator given the to solver
#[cfg(feature = "ipasir-up")]
pub trait PropagatorAccess {
	/// Access the external propagator given the to solver
	///
	/// This method will return [`None`] if no propagator is set, or if the
	/// propagator is not of type [`P`].
	fn propagator<P: Propagator + 'static>(&self) -> Option<&P>;
}

/// Get mutable access to the external propagator given the to solver
#[cfg(feature = "ipasir-up")]
pub trait MutPropagatorAccess {
	/// Get mutable access to the external propagator given the to solver
	///
	/// This method will return [`None`] if no propagator is set, or if the
	/// propagator is not of type [`P`].
	fn propagator_mut<P: Propagator + 'static>(&mut self) -> Option<&mut P>;
}

#[cfg(feature = "ipasir-up")]
pub trait Propagator {
	/// This method is called checked only when the propagator is connected. When
	/// a Propagator is marked as lazy, it is only asked to check complete
	/// assignments.
	fn is_lazy(&self) -> bool {
		false
	}

	/// Method called to notify the propagator about assignments of literals
	/// concerning observed variables.
	///
	/// The notification is not necessarily eager. It usually happens before the
	/// call of propagator callbacks and when a driving clause is leading to an
	/// assignment.
	///
	/// If [`persistent`] is set to `true`, then the assignment is known to
	/// persist through backtracking.
	fn notify_assignment(&mut self, lit: Lit, persistent: bool) {
		let _ = lit;
		let _ = persistent;
	}
	fn notify_new_decision_level(&mut self) {}
	fn notify_backtrack(&mut self, new_level: usize) {
		let _ = new_level;
	}

	/// Method called to check the found complete solution (after solution
	/// reconstruction). If it returns false, the propagator must provide an
	/// external clause during the next callback.
	fn check_model(&mut self, slv: &mut dyn SolvingActions, value: &dyn Valuation) -> bool {
		let _ = value;
		let _ = slv;
		true
	}

	/// Method called when the solver asks for the next decision literal. If it
	/// returns None, the solver makes its own choice.
	fn decide(&mut self) -> Option<Lit> {
		None
	}

	/// Method to ask the propagator if there is an propagation to make under the
	/// current assignment. It returns queue of literals to be propagated in order,
	/// if an empty queue is returned it indicates that there is no propagation
	/// under the current assignment.
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Vec<Lit> {
		let _ = slv;
		Vec::new()
	}

	/// Ask the external propagator for the reason clause of a previous external
	/// propagation step (done by [`Propagator::propagate`]). The clause must
	/// contain the propagated literal.
	fn add_reason_clause(&mut self, propagated_lit: Lit) -> Vec<Lit> {
		let _ = propagated_lit;
		Vec::new()
	}

	/// Method to ask whether there is an external clause to add to the solver.
	fn add_external_clause(&mut self, slv: &mut dyn SolvingActions) -> Option<Vec<Lit>> {
		let _ = slv;
		None
	}

	/// Method to help access to the propagator when given to the solver.
	///
	/// See [`PropagatingSolver::propagator`].
	///
	/// # Note
	///
	/// This method can generally be implemented as
	/// ```rust
	/// use std::any::Any;
	/// use pindakaas::solver::Propagator;
	///
	/// struct A;
	///
	/// impl Propagator for A {
	///   fn as_any(&self) -> &dyn Any {
	///     self
	///   }
	///
	/// #  fn as_mut_any(&mut self) -> &mut dyn Any { self }
	/// }
	///
	/// ```
	fn as_any(&self) -> &dyn Any;

	/// Method to help access to the propagator when given to the solver.
	///
	/// See [`PropagatingSolver::propagator`].
	///
	/// # Note
	///
	/// This method can generally be implemented as
	/// ```rust
	/// use std::any::Any;
	/// use pindakaas::solver::Propagator;
	///
	/// struct A;
	///
	/// impl Propagator for A {
	///   fn as_mut_any(&mut self) -> &mut dyn Any {
	///     self
	///   }
	/// #  fn as_any(&self) -> &dyn Any { self }
	/// }
	///
	/// ```
	fn as_mut_any(&mut self) -> &mut dyn Any;
}

#[cfg(feature = "ipasir-up")]
pub trait SolvingActions {
	fn new_var(&mut self) -> Var;
	fn add_observed_var(&mut self, var: Var);
	fn is_decision(&mut self, lit: Lit) -> bool;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum SlvTermSignal {
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

/// Allow request for sequential ranges of variables.
pub trait NextVarRange {
	/// Request the next sequential range of variables.
	///
	/// The method is can return [`None`] if the range of the requested [`size`] is not
	/// available.
	fn next_var_range(&mut self, size: usize) -> Option<VarRange>;
}

impl NextVarRange for VarFactory {
	fn next_var_range(&mut self, size: usize) -> Option<VarRange> {
		let start = self.next_var?;
		match size {
			0 => Some(VarRange::new(
				Var(NonZeroI32::new(2).unwrap()),
				Var(NonZeroI32::new(1).unwrap()),
			)),
			1 => {
				self.next_var = start.next_var();
				Some(VarRange::new(start, start))
			}
			_ if size > NonZeroI32::MAX.get() as usize => None,
			_ => {
				// Size is reduced by 1 since it includes self.next_var
				let size = NonZeroI32::new((size - 1) as i32).unwrap();
				if let Some(end) = start.checked_add(size) {
					// Set self.next_var to one after end
					self.next_var = end.next_var();
					Some(VarRange::new(start, end))
				} else {
					None
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use std::num::NonZeroI32;

	use crate::{
		solver::{NextVarRange, VarFactory},
		Var,
	};

	#[test]
	fn test_var_range() {
		let mut factory = VarFactory::default();

		let range = factory.next_var_range(0).unwrap();
		assert_eq!(range.len(), 0);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(1).unwrap())));

		let range = factory.next_var_range(1).unwrap();
		assert_eq!(range.len(), 1);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(2).unwrap())));

		let range = factory.next_var_range(2).unwrap();
		assert_eq!(range.len(), 2);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(4).unwrap())));

		let range = factory.next_var_range(100).unwrap();
		assert_eq!(range.len(), 100);
		assert_eq!(factory.next_var, Some(Var(NonZeroI32::new(104).unwrap())));
	}
}
