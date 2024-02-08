use std::{marker::PhantomData, num::NonZeroI32};

use crate::{helpers::VarRange, ClauseDatabase, Lit, Valuation, Var};

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
	/// If the search is interrupted (see [`SolveArgs::term_callback`]) the method
	/// returns unknown
	fn solve(&mut self, args: SolveArgs<Self>) -> SolveResult;
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum SolveResult {
	Sat,
	Unsat,
	Unknown,
}

/// Argument builder of the [`Solver::solve`] method
///
/// This argument builder makes it easy to specify only some (non-default)
/// arguments and ensures only implemented functionality is exposed.
#[derive(Default)]
pub struct SolveArgs<'a, T: Solver + ?Sized> {
	slv: PhantomData<T>,
	on_sol: Option<BoxSolCb<'a>>,
	on_fail: Option<BoxFailCb<'a>>,
	assumptions: Option<Box<dyn Iterator<Item = Lit> + 'a>>,
	learn_cb: Option<LearnCbRef<'a>>,
	term_cb: Option<&'a mut dyn FnMut() -> SlvTermSignal>,
	prop: Option<&'a mut dyn Propagator>,
}

type BoxSolCb<'a> = Box<dyn FnOnce(&dyn Valuation) + 'a>;
type BoxFailCb<'a> = Box<dyn FnOnce(&FailFn<'_>) + 'a>;
type LearnCbRef<'a> = &'a mut dyn FnMut(&mut dyn Iterator<Item = Lit>);

impl<'a, T: Solver> SolveArgs<'a, T> {
	pub fn on_sol<F: FnOnce(&dyn Valuation) + 'a>(mut self, cb: F) -> Self {
		self.on_sol = Some(Box::new(cb));
		self
	}
	pub fn take_on_sol(&mut self) -> Option<BoxSolCb<'a>> {
		self.on_sol.take()
	}
}

impl<'a, T: SolveAssuming> SolveArgs<'a, T> {
	pub fn assuming<O: IntoIterator<IntoIter = I>, I: Iterator<Item = Lit> + 'a>(
		mut self,
		assumptions: O,
	) -> Self {
		self.assumptions = Some(Box::new(assumptions.into_iter()));
		self
	}

	pub fn take_assumptions(&mut self) -> Option<Box<dyn Iterator<Item = Lit> + 'a>> {
		self.assumptions.take()
	}

	pub fn on_fail<FailCb: FnOnce(&FailFn<'_>) + 'a>(mut self, cb: FailCb) -> Self {
		self.on_fail = Some(Box::new(cb));
		self
	}

	pub fn take_on_fail(&mut self) -> Option<BoxFailCb<'a>> {
		self.on_fail.take()
	}
}

impl<'a, T: CallbackOnLearn> SolveArgs<'a, T> {
	pub fn learn_callback(mut self, cb: LearnCbRef<'a>) -> Self {
		self.learn_cb = Some(cb);
		self
	}
	pub fn take_learn_callback(&mut self) -> Option<LearnCbRef<'a>> {
		self.learn_cb.take()
	}
}

impl<'a, T: CheckTermCallback> SolveArgs<'a, T> {
	pub fn term_callback(mut self, cb: &'a mut dyn FnMut() -> SlvTermSignal) -> Self {
		self.term_cb = Some(cb);
		self
	}
	pub fn take_term_callback(&mut self) -> Option<&'a mut dyn FnMut() -> SlvTermSignal> {
		self.term_cb.take()
	}
}

#[cfg(feature = "ipasir-up")]
impl<'a, T: PropagatingSolver> SolveArgs<'a, T> {
	pub fn with_propagator(mut self, prop: &'a mut dyn Propagator) -> Self {
		self.prop = Some(prop);
		self
	}

	pub fn take_propagator(&mut self) -> Option<&'a mut dyn Propagator> {
		self.prop.take()
	}
}

/// Trait implementation by [`Solver`]s that promises to assume all literals
/// given by [`SolveArgs::assumptions`], allowing the user to question which
/// ones caused failures, using [`SolveArgs::on_fail`], when the solve status is
/// [`SolveResult::Unsat`].
pub trait SolveAssuming: Solver {}

/// Check if the given assumption literal was used to prove the unsatisfiability
/// of the formula under the assumptions used for the last SAT search.
///
/// Note that for literals 'lit' which are not assumption literals, the behavior
/// of is not specified.
pub type FailFn<'a> = dyn Fn(Lit) -> bool + 'a;

/// Trait implemented by [`Solver`]s that promise to call the
/// [`SolveArgs::learn_callback`] callback function on learned clauses.
pub trait CallbackOnLearn: Solver {}

/// Trait implemented by [`Solver`]s that promise to occassionally call the
/// [`SolveArgs::term_callback`] callback function to see whether the solving
/// process should be interrupted.
pub trait CheckTermCallback: Solver {}

/// Trait implemented by solvers that allow the connection of an external
/// [`Propagator`] which allows to learn, propagate and backtrack based on
/// external constraints.
#[cfg(feature = "ipasir-up")]
pub trait PropagatingSolver: Solver {
	fn add_observed_var(&mut self, var: Var);
	fn remove_observed_var(&mut self, var: Var);
	fn reset_observed_vars(&mut self);
}

#[cfg(feature = "ipasir-up")]
pub trait Propagator {
	/// This method is called checked only when the propagator is connected. When
	/// a Propagator is marked as lazy, it is only asked to check complete
	/// assignments.
	fn is_lazy(&self) -> bool {
		false
	}

	/// Method called to notify the propagator about assignments to observed
	/// variables.
	///
	/// The notification is not necessarily eager. It usually happens before the
	/// call of propagator callbacks and when a driving clause is leading to an
	/// assignment.
	///
	/// If [`persistent`] is set to `true`, then the assignment is known to
	/// persist through backtracking.
	fn notify_assignment(&mut self, var: Var, val: bool, persistent: bool) {
		let _ = var;
		let _ = val;
		let _ = persistent;
	}
	fn notify_new_decision_level(&mut self) {}
	fn notify_backtrack(&mut self, new_level: usize) {
		let _ = new_level;
	}

	/// Method called to check the found complete solution (after solution
	/// reconstruction). If it returns false, the propagator must provide an
	/// external clause during the next callback.
	fn check_model(&mut self, value: &dyn Valuation) -> bool {
		let _ = value;
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
	fn add_external_clause(&mut self) -> Option<Vec<Lit>> {
		None
	}
}

#[cfg(feature = "ipasir-up")]
pub trait SolvingActions {
	fn new_var(&mut self) -> Var;
	fn add_observed_var(&mut self, var: Var);
	fn is_decision(&mut self, lit: Lit) -> bool;
}

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

	/// Return the next [`size`] variables that can be stored as an inclusive range.
	pub fn new_var_range(&mut self, size: usize) -> Option<VarRange> {
		let Some(start) = self.next_var else {
			return None;
		};
		match size {
			0 => Some(VarRange::new(
				Var(NonZeroI32::new(2).unwrap()),
				Var(NonZeroI32::new(1).unwrap()),
			)),
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
