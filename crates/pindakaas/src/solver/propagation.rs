//! This module contains interfaces for extending SAT solvers with external
//! propagation functionality.

use std::{cell::RefCell, rc::Rc};

use crate::{solver::Solver, Lit, Var};

/// A builder for a clause being communicated to the solver, used by
/// [`Propagator::provide_clause`] and [`Propagator::explain_propagation`].
#[derive(Debug)]
pub struct ClauseBuilder<'a> {
	clause: &'a mut Vec<Lit>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Whether a clause could possibly be removed from the clause database.
pub enum ClausePersistence {
	/// The clause is to be considered forgettable. Its removal would not affect
	/// the solver's correctness (in combination with the propagator), and it
	/// can be re-derived if needed.
	Forgettable,
	/// The clause is to be considered irredundant. It contains information that
	/// can not (easily) be re-derived.
	Irredundant,
}

/// Trait implemented by [`Solver`]s that allow connecting an external
/// propagator.
pub trait ExternalPropagation: Solver {
	/// Add a variable to the set of observed variables.
	///
	/// The external propagator will be notified when the variable is assigned.
	fn add_observed_var(&mut self, var: Var);

	/// Connect a [`Propagator`] implementation which allows to learn, propagate
	/// and backtrack based on external constraints.
	///
	/// The connected [`Propagator`] is notified of all changes to which it has
	/// subscribed, using the [`Self::add_observed_var`] method.
	///
	/// # Warning
	///
	/// The [`RefCell<Propagator>`] should never be in a borrowed state when a
	/// method call is made to the solver.
	///
	/// Only one [`Propagator`] can be connected, any previously connected
	/// [`Propagator`]s will be disconnected (see
	/// [`Self::disconnect_propagator`]).
	fn connect_propagator<P: PropagatorConfig + 'static>(&mut self, propagator: Rc<RefCell<P>>);

	/// Disconnect any previously connected a [`Propagator`] (using
	/// [`Self::connect_propagator`])
	///
	/// # Warning
	///
	/// Disconnecting the [`Propagator`] will reset the observed variable set.
	fn disconnect_propagator(&mut self);

	/// Add a new observed literal to the solver.
	fn new_observed_lit(&mut self) -> Lit {
		self.new_observed_var().into()
	}

	/// Add a new observed variable to the solver.
	fn new_observed_var(&mut self) -> Var {
		let var = self.new_var_range(1).next().unwrap();
		self.add_observed_var(var);
		var
	}

	/// Set the default decision phase of a variable to the given [`Lit`].
	fn phase(&mut self, lit: Lit);

	/// Remove a variable from the set of observed variables.
	///
	/// The external propagator will no longer be notified of assignments to
	/// the variable.
	fn remove_observed_var(&mut self, var: Var);

	/// Reset the set of observed variables.
	///
	/// The external propagator will no longer be notified of assignments to
	/// any variables.
	fn reset_observed_vars(&mut self);

	/// Remove the default decision phase of the given variable (given as a
	/// [`Lit`]).
	fn unphase(&mut self, lit: Lit);
}

/// Connected listener gets notified whenever the truth value of a variable
/// is fixed (for example during inprocessing or due to some derived unit
/// clauses).
///
/// # Warning
///
/// As with [`Propagator`], this method is called by the solver from C and must
/// not panic or re-enter the solver.
pub trait PersistentAssignmentListener {
	/// Notify the listener that a variable has been assigned a value that is
	/// considered persistent. This means that the variable will not be
	/// backtracked over during the solving process.
	fn notify_persistent_assignment(&mut self, lit: Lit) {
		let _ = lit;
	}
}

/// Trait implemented by [`Solver`]s that support persistent assignment
/// notifications.
pub trait PersistentAssignmentNotifier: Solver {
	/// Connect a listener that gets notified whenever the truth value of a
	/// variable is permanently set (e.g. during inprocessing or when a unit
	/// clause is derived).
	///
	/// # Warning
	///
	/// Only one [`PersistentAssignmentListener`] can be connected, any
	/// previously connected [`PersistentAssignmentListener`]s will be
	/// disconnected (see [`Self::disconnect_persistent_assignment_listener`]).
	fn connect_persistent_assignment_listener<L: PersistentAssignmentListener + 'static>(
		&mut self,
		listener: Rc<RefCell<L>>,
	);

	/// Disconnect the any connected [`PersistentAssignmentListener`].
	fn disconnect_persistent_assignment_listener(&mut self);
}

/// Trait implemented to provide external propagation for [`Solver`]s
/// implementing the [`ExternalPropagation`] trait.
///
/// # Warning
///
/// The methods of this trait are invoked by the solver from C, through an
/// `extern "C"` trampoline. Two consequences follow for implementations:
///
/// - **Do not panic.** A panic cannot unwind through the C frames and aborts
///   the process instead. This includes the implicit panics from `unwrap`,
///   indexing, and arithmetic overflow in debug builds.
/// - **Do not re-enter the solver.** These methods are called while the
///   propagator's [`RefCell`] is mutably borrowed, so calling back into the
///   solver in a way that triggers another propagator callback panics in
///   `RefCell::borrow_mut` (and thus aborts, per the previous point). The
///   actions that *are* safe to perform during a callback are the ones offered
///   by [`SolvingActions`].
///
/// [`RefCell`]: std::cell::RefCell
pub trait Propagator {
	/// Method called to check the found complete `solution` (after solution
	/// reconstruction). If it returns false, the propagator must provide an
	/// external clause during the next callback.
	fn check_solution(&mut self, slv: &mut dyn SolvingActions, solution: Solution<'_>) -> bool {
		let _ = solution;
		let _ = slv;
		true
	}

	/// Method called when the solver asks for the next search decision.
	///
	/// The propagator can either decide to assign a given literal, force the
	/// solver to backtrack to a given decision level, or leave the decision to
	/// the solver.
	fn decide(&mut self, slv: &mut dyn SolvingActions) -> SearchDecision {
		let _ = slv;
		SearchDecision::Free
	}

	/// Ask the propagator to explain a literal it previously propagated (using
	/// [`Propagator::propagate`]).
	///
	/// The propagator must push the complete reason clause into `clause`, e.g.
	/// an implication `(p_1 ∧ … ∧ p_n) → propagated_lit` with premises `p_i`
	/// that currently hold and imply `propagated_lit`, which would be expressed
	/// as the clause `(¬p_1 ∨ … ∨ ¬p_n ∨ propagated_lit)`.
	fn explain_propagation(&mut self, propagated_lit: Lit, clause: ClauseBuilder<'_>) {
		let _ = propagated_lit;
		let _ = clause;
	}

	/// Method called to notify the propagator about assignments of literals
	/// concerning observed variables.
	///
	/// The notification is not necessarily eager. It usually happens before the
	/// call of propagator callbacks and when a driving clause is leading to an
	/// assignment.
	fn notify_assignment(&mut self, lits: &[Lit]) {
		let _ = lits;
	}

	/// Method called to notify the propagator about a backtrack to an earlier
	/// decision level.
	fn notify_backtrack(&mut self, new_level: usize, restart: bool) {
		let _ = new_level;
		let _ = restart;
	}
	/// Method called to notify the propagator about a new decision level.
	fn notify_new_decision_level(&mut self) {}

	/// Ask the propagator for the next literal to propagate under the current
	/// assignment.
	///
	/// This is called repeatedly: each call returns one literal to propagate,
	/// and `None` indicates that there is nothing (more) to propagate under
	/// the current assignment.
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Option<Lit> {
		let _ = slv;
		None
	}

	/// Ask the propagator to provide a clause to add to the solver.
	///
	/// If there is a clause to provide, the propagator pushes its literals into
	/// `clause` and returns its [`ClausePersistence`]. Returning `None` (and
	/// leaving `clause` untouched) indicates that there is no clause to
	/// provide.
	fn provide_clause(
		&mut self,
		slv: &mut dyn SolvingActions,
		clause: ClauseBuilder<'_>,
	) -> Option<ClausePersistence> {
		let _ = slv;
		let _ = clause;
		None
	}
}

/// Trait that gives extra information about the [`Propagator`] implementation.
/// This information is used to optimize the interaction between the
/// [`Propagator`] and the solver.
pub trait PropagatorConfig: Propagator {
	/// Whether the [`Propagator`] implementation only checks complete
	/// assignments.
	///
	/// If the set to `true`, then only [`Propagator::check_solution`] is
	/// called.
	const CHECK_ONLY: bool = false;

	/// The persistence level of the [`Propagator`] implementation's produced
	/// reasons using [`Propagator::explain_propagation`].
	///
	/// If set to [`ClausePersistence::Forgettable`], then the solver might
	/// remove the reason clauses to save memory. The [`Propagator`]
	/// implementation must be able to re-derive the reason clause at a later
	/// point.
	const REASON_PERSISTENCE: ClausePersistence = ClausePersistence::Irredundant;
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// A representation of a search decision made by a propagator.
pub enum SearchDecision {
	/// Leave the search decision to the solver.
	Free,
	/// Make the decision to assign the given literal.
	Assign(Lit),
	/// Force the solver to backtrack to the given decision level.
	Backtrack(usize),
}

/// A complete solution found by the solver, handed to
/// [`Propagator::check_solution`].
///
/// The solver must provide the literals sorted by variable, which lets
/// [`Solution::value`] look up a literal's value with a binary search and
/// without any allocation.
#[derive(Clone, Copy, Debug)]
pub struct Solution<'a> {
	/// The assigned literals of the observed variables, sorted by variable, as
	/// provided by the solver.
	model: &'a [Lit],
}

/// Actions that a [`Propagator`] can generally undertake when making
/// inferences.
pub trait SolvingActions {
	/// Query whether a literal was assigned as a search decision.
	fn is_decision(&mut self, lit: Lit) -> bool;

	/// Add a new observed literal to the solver.
	fn new_observed_lit(&mut self) -> Lit {
		self.new_observed_var().into()
	}

	/// Add a new observed variable to the solver.
	fn new_observed_var(&mut self) -> Var;

	/// Set the default decision phase of a variable to the given [`Lit`].
	fn phase(&mut self, lit: Lit);

	/// Remove the default decision phase of the given variable (given as a
	/// [`Lit`]).
	fn unphase(&mut self, lit: Lit);
}

impl<'a> ClauseBuilder<'a> {
	/// Create a clause builder that appends into the given buffer.
	///
	/// Literals are appended to the buffer as-is, so any literals already in it
	/// remain part of the clause.
	pub fn new(clause: &'a mut Vec<Lit>) -> Self {
		Self { clause }
	}

	/// Add a literal to the clause.
	pub fn push(&mut self, lit: Lit) {
		self.clause.push(lit);
	}

	/// Reserve capacity for at least `additional` more literals.
	pub fn reserve(&mut self, additional: usize) {
		self.clause.reserve(additional);
	}
}

impl Extend<Lit> for ClauseBuilder<'_> {
	fn extend<I: IntoIterator<Item = Lit>>(&mut self, lits: I) {
		self.clause.extend(lits);
	}
}

impl<'a> Solution<'a> {
	/// The assigned literals of the observed variables, in order of their
	/// variable.
	pub fn literals(&self) -> &'a [Lit] {
		self.model
	}

	/// Creates a solution view over the model literals provided by the solver.
	///
	/// The literals must be sorted by variable, as the solver provides them;
	/// [`Solution::value`] relies on this ordering.
	pub(crate) fn new(model: &'a [Lit]) -> Self {
		debug_assert!(
			model.windows(2).all(|w| w[0].var() < w[1].var()),
			"the solver must provide the model sorted by (distinct) variable"
		);
		Self { model }
	}

	/// Returns the truth value of `lit` in the solution.
	///
	/// The literal's variable must be observed by the propagator, and hence be
	/// part of the solution. Querying any other variable is a usage error that
	/// is caught by a debug assertion and otherwise treated as `false`.
	pub fn value(&self, lit: Lit) -> bool {
		match self
			.model
			.binary_search_by(|assigned| assigned.var().cmp(&lit.var()))
		{
			Ok(i) => self.model[i] == lit,
			Err(_) => {
				// A literal absent from the model belongs to a variable that is
				// not observed by the propagator, which it should therefore
				// not query.
				debug_assert!(false, "queried an unobserved variable");
				false
			}
		}
	}
}
