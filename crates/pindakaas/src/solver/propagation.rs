//! This module contains interfaces for extending SAT solvers with external
//! propagation functionality.

use std::{cell::RefCell, rc::Rc};

use crate::{solver::Solver, Lit, Valuation, Var};

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// Whether a clause could possibly be removed from the clause database.
pub enum ClausePersistence {
	/// The clause is to be considered forgettable. Its removal would not affect
	/// the solver's correctness (in combination with the propagator), and it
	/// can be re-derived if needed.
	Forgettable,
	/// The clause is to be considered irreduntant. It contains information that
	/// can not (easily) be re-derived.
	Irreduntant,
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
	fn connect_propagator<P: PropagatorDefinition + 'static>(&mut self, propagator: Rc<RefCell<P>>);

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
pub trait Propagator {
	/// Method called to notify the propagator about assignments of literals
	/// concerning observed variables.
	///
	/// The notification is not necessarily eager. It usually happens before the
	/// call of propagator callbacks and when a driving clause is leading to an
	/// assignment.
	fn notify_assignments(&mut self, lits: &[Lit]) {
		let _ = lits;
	}
	/// Method called to notify the propagator about a new decision level.
	fn notify_new_decision_level(&mut self) {}

	/// Method called to notify the propagator about a backtrack to an earlier
	/// decision level.
	fn notify_backtrack(&mut self, new_level: usize, restart: bool) {
		let _ = new_level;
		let _ = restart;
	}

	/// Method called to check the found complete solution (after solution
	/// reconstruction). If it returns false, the propagator must provide an
	/// external clause during the next callback.
	fn check_solution(&mut self, slv: &mut dyn SolvingActions, value: &dyn Valuation) -> bool {
		let _ = value;
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

	/// Method to ask the propagator if there is an propagation to make under
	/// the current assignment. It returns queue of literals to be propagated
	/// in order, if an empty queue is returned it indicates that there is no
	/// propagation under the current assignment.
	fn propagate(&mut self, slv: &mut dyn SolvingActions) -> Option<Lit> {
		let _ = slv;
		None
	}

	/// Ask the external propagator for the reason clause of a previous external
	/// propagation step (done by [`Propagator::propagate`]). The clause must
	/// contain the propagated literal.
	fn add_reason_clause(&mut self, propagated_lit: Lit) -> Vec<Lit> {
		let _ = propagated_lit;
		Vec::new()
	}

	/// Method to ask whether there is an external clause to add to the solver.
	fn add_external_clause(
		&mut self,
		slv: &mut dyn SolvingActions,
	) -> Option<(Vec<Lit>, ClausePersistence)> {
		let _ = slv;
		None
	}
}

/// Trait that gives extra information about the [`Propagator`] implementation.
/// This information is used to optimize the interaction between the
/// [`Propagator`] and the solver.
pub trait PropagatorDefinition: Propagator {
	/// Whether the [`Propagator`] implementation only checks complete
	/// assignments.
	///
	/// If the set to `true`, then only [`Propagator::check_solution`] is
	/// called.
	const CHECK_ONLY: bool = false;

	/// The persistence level of the [`Propagator`] implementation's produced
	/// reasons using [`Propagator::add_reason_clause`].
	///
	/// If set to [`ClausePersistence::Forgettable`], then the solver might
	/// remove the reason clauses to save memory. The [`Propagator`]
	/// implementation must be able to re-derive the reason clause at a later
	/// point.
	const REASON_PERSISTENCE: ClausePersistence = ClausePersistence::Irreduntant;
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
