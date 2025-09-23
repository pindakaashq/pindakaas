//! This module contains the pindakaas interface to the
//! [CaDiCaL](https://github.com/arminbiere/cadical) SAT solver.

use std::{
	cell::RefCell,
	ffi::{c_int, c_void, CString},
	fmt,
	marker::PhantomData,
	rc::Rc,
};

use pindakaas_cadical::{
	ccadical_add, ccadical_assume, ccadical_connect_proof_tracer, ccadical_copy,
	ccadical_disconnect_proof_tracer, ccadical_failed, ccadical_get_option, ccadical_init,
	ccadical_limit, ccadical_phase, ccadical_release, ccadical_set_learn, ccadical_set_option,
	ccadical_set_terminate, ccadical_solve, ccadical_unphase, ccadical_val, CTracer,
};
#[cfg(feature = "external-propagation")]
use pindakaas_cadical::{
	ccadical_add_observed_var, ccadical_connect_external_propagator,
	ccadical_disconnect_external_propagator, ccadical_force_backtrack, ccadical_is_decision,
	ccadical_is_observed, ccadical_remove_observed_var, ccadical_reset_observed_vars,
	CExternalPropagator,
};

#[cfg(feature = "external-propagation")]
use crate::solver::{
	ipasir::user_propagation::IpasirUserPropagationMethods, propagation::ExternalPropagation,
};
use crate::{
	helpers::opt_field::OptField,
	solver::{
		ipasir::{
			AccessIpasirStore, BasicIpasirStorage, IpasirAssumptionMethods,
			IpasirLearnCallbackMethod, IpasirSolverMethods, IpasirStore, IpasirStoreInner,
			IpasirTermCallbackMethod,
		},
		LearnCallback, TermSignal, TerminateCallback,
	},
	ClauseDatabaseTools, Cnf, Lit, VarRange,
};

#[derive(Default)]
/// Representation of an instance of the
/// [CaDiCaL](https://github.com/arminbiere/cadical) SAT solver.
pub struct Cadical {
	store: IpasirStore<Cadical, 1, 1, 1>,
	tracers: Vec<Rc<RefCell<dyn ProofTracer>>>,
}

/// Enum to represent the proof conclusion type of a SAT solver run.
#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
pub enum ProofConclusionType {
	/// Problem is unsatisfiable because of a inherent conflict in the clauses.
	Conflict = 1,
	/// Problem is unsatisfiable because of assumptions made.
	Assumptions = 2,
	/// Problem unsatisfiability is caused by a constraint.
	Constraint = 4,
}

/// Trait that observers can implement to receive notifications about proof
/// events.
pub trait ProofTracer {
	// -----------------------------
	// Basic Events
	// -----------------------------

	/// An original clause is added.
	fn add_original_clause(&mut self, id: u64, redundant: bool, clause: &[Lit], restored: bool) {
		let _ = (id, redundant, clause, restored);
	}

	/// A derived clause is added.
	fn add_derived_clause(
		&mut self,
		id: u64,
		redundant: bool,
		clause: &[Lit],
		antecedents: &[u64],
	) {
		let _ = (id, redundant, clause, antecedents);
	}

	/// A clause is deleted.
	fn delete_clause(&mut self, id: u64, redundant: bool, clause: &[Lit]) {
		let _ = (id, redundant, clause);
	}

	/// Mark a clause as potentially restorable later.
	fn weaken_minus(&mut self, id: u64, clause: &[Lit]) {
		let _ = (id, clause);
	}

	/// A clause was strengthened.
	fn strengthen(&mut self, id: u64) {
		let _ = id;
	}

	/// Reports the result of the solver.
	///
	/// - `status`: Status code.
	/// - `id`: Clause ID of the conflict clause.
	fn report_status(&mut self, status: i32, id: u64) {
		let _ = (status, id);
	}

	// -----------------------------
	// Non-Incremental Features
	// -----------------------------

	/// Finalizes a clause.
	///
	/// - `id`: Clause ID.
	/// - `clause`: Clause literals.
	fn finalize_clause(&mut self, id: u64, clause: &[Lit]) {
		let _ = (id, clause);
	}

	/// Notification that the proof begins with a set of reserved ids for
	/// original clauses.
	///
	/// - `first_derived_id`: Clause ID of the first derived clause ID.
	fn begin_proof(&mut self, first_derived_id: u64) {
		let _ = first_derived_id;
	}

	// -----------------------------
	// Incremental Features
	// -----------------------------

	/// Notification that an assumption has been added.
	fn solve_query(&mut self) {}

	/// Adds an assumption literal.
	fn add_assumption(&mut self, lit: Lit) {
		let _ = lit;
	}

	/// Adds constraint clause has been added.
	fn add_constraint(&mut self, clause: &[Lit]) {
		let _ = clause;
	}

	/// All assumptions and constraints have been reset.
	fn reset_assumptions(&mut self) {}

	/// This clause could be derived, which is the negation of a core of failing
	/// assumptions/constraints. If antecedents are derived they will be
	/// included here.
	fn add_assumption_clause(&mut self, id: u64, clause: &[Lit], antecedents: &[u64]) {
		let _ = (id, clause, antecedents);
	}

	/// Conclude unsat was requested. It will give either the id of the empty
	/// clause, the id of a failing assumption clause or the ids of the failing
	/// constrain clauses
	fn conclude_unsat(&mut self, conclusion_type: ProofConclusionType, clause_ids: &[u64]) {
		let _ = (conclusion_type, clause_ids);
	}

	/// SAT has been concluded, and the satisfying assignment provided
	fn conclude_sat(&mut self, assignment: &[Lit]) {
		let _ = assignment;
	}

	/// Reports that the result is unknown, providing the current trail.
	fn conclude_unknown(&mut self, trail: &[Lit]) {
		let _ = trail;
	}
}

/// Trait that gives extra information about the [`ProofTracer`] implementation.
/// This information is used to optimize the interaction between the
/// [`ProofTracer`] and the solver.
pub trait ProofTracerDefinition: ProofTracer {
	/// Whether the [`ProofTracer`] uses the antecedents of derived clauses.
	const ANTECEDENTS: bool;
	/// Whether the [`ProofTracer`] needs the solver to finalize non-deleted
	/// clauses in proof.
	const FINALIZE_CLAUSES: bool = false;
}

impl Cadical {
	// TODO: Hidden for now as it requires the user to set the proof tracer during
	// CONFIGURATION. This should probably be a separate state/builder.
	#[doc(hidden)]
	pub fn connect_proof_tracer<P: ProofTracerDefinition + 'static>(
		&mut self,
		tracer: Rc<RefCell<P>>,
	) {
		let ptr = Rc::as_ptr(&tracer);
		let ctracer = CTracer {
			data: ptr as *mut c_void,
			add_original_clause: ffi::add_original_clause::<P>,
			add_derived_clause: ffi::add_derived_clause::<P>,
			delete_clause: ffi::delete_clause::<P>,
			weaken_minus: ffi::weaken_minus::<P>,
			strengthen: ffi::strengthen::<P>,
			report_status: ffi::report_status::<P>,
			finalize_clause: ffi::finalize_clause::<P>,
			begin_proof: ffi::begin_proof::<P>,
			solve_query: ffi::solve_query::<P>,
			add_assumption: ffi::add_assumption::<P>,
			add_constraint: ffi::add_constraint::<P>,
			reset_assumptions: ffi::reset_assumptions::<P>,
			add_assumption_clause: ffi::add_assumption_clause::<P>,
			conclude_unsat: ffi::conclude_unsat::<P>,
			conclude_sat: ffi::conclude_sat::<P>,
			conclude_unknown: ffi::conclude_unknown::<P>,
		};
		self.tracers.push(tracer);
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe {
			ccadical_connect_proof_tracer(
				self.ipasir_store().solver_ptr(),
				ctracer,
				P::ANTECEDENTS,
				P::FINALIZE_CLAUSES,
			);
		}
	}

	#[doc(hidden)]
	// TODO: Hidden until [`Self::connect_proof_tracer`] has been finalized.
	pub fn disconnect_proof_tracer<P: ProofTracer + 'static>(&mut self, tracer: Rc<RefCell<P>>) {
		let len = self.tracers.len();
		let ptr = Rc::as_ptr(&tracer);
		let dyn_rc: Rc<RefCell<dyn ProofTracer>> = tracer;
		self.tracers.retain(|t| !Rc::ptr_eq(t, &dyn_rc));
		if len != self.tracers.len() {
			// SAFETY: Pointer known to be non-null, no other known safety concerns.
			unsafe {
				let removed = ccadical_disconnect_proof_tracer(
					self.ipasir_store().solver_ptr(),
					ptr as *mut c_void,
				);
				debug_assert!(removed);
			}
		}
	}
	// TODO: Unsure whether this is a good idea.
	#[doc(hidden)]
	pub fn emitted_vars(&self) -> VarRange {
		self.ipasir_store().vars().emitted_vars()
	}

	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn get_option(&self, name: &str) -> i32 {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { ccadical_get_option(self.ipasir_store().solver_ptr(), name.as_ptr()) }
	}

	#[cfg(feature = "external-propagation")]
	/// Check whether a given literal is marked as observed in the solver's for
	/// the [`ExternalPropagation`] interface.
	pub fn is_observed(&self, lit: Lit) -> bool {
		// SAFETY: Pointer known to be non-null, lit is known to be non-zero and not
		// MIN_INT as required by Cadical.
		unsafe { ccadical_is_observed(self.ipasir_store().solver_ptr(), lit.0.get()) }
	}

	// TODO: This can be replaced by [`ExternalPropagation::phase`] if
	// `external_propagation` feature is ever automatically enabled.
	/// Set the default decision phase of a variable to the given [`Lit`].
	pub fn phase(&mut self, lit: Lit) {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe { ccadical_phase(self.ipasir_store().solver_ptr(), lit.0.get()) }
	}

	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn set_limit(&mut self, name: &str, value: i32) {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { ccadical_limit(self.ipasir_store().solver_ptr(), name.as_ptr(), value) }
	}

	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn set_option(&mut self, name: &str, value: i32) {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { ccadical_set_option(self.ipasir_store().solver_ptr(), name.as_ptr(), value) }
	}

	/// Make a shallow clone of the [`Cadical`] solver using an efficient
	/// internal method.
	///
	/// The shallow copy includes the permanent clauses, but will not include
	/// learned clauses, connected callbacks, or external propagator.
	pub fn shallow_clone(&self) -> Self {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		let ptr = unsafe { ccadical_copy(self.ipasir_store().solver_ptr()) };
		let vars = *self.ipasir_store().vars(); // Copy

		// Initialize [`Self`] instance.
		let mut slv = Self {
			store: IpasirStore {
				store: Box::new(IpasirStoreInner {
					ptr,
					vars,
					learn_cb: OptField::default(),
					term_cb: OptField::default(),
					#[cfg(feature = "external-propagation")]
					propagator: OptField::default(),
					#[cfg(not(feature = "external-propagation"))]
					_propagator: PhantomData,
				}),
				_methods: PhantomData,
			},
			tracers: Vec::new(),
		};
		// Make sure no pointers are left behind in the backend.
		slv.set_learn_callback::<fn(&mut dyn Iterator<Item = Lit>)>(None);
		slv.set_terminate_callback::<fn() -> TermSignal>(None);
		#[cfg(feature = "external-propagation")]
		slv.disconnect_propagator();

		slv
	}

	// TODO: This can be replaced by [`ExternalPropagation::unphase`] if
	// `external_propagation` feature is ever automatically enabled.
	/// Remove the default decision phase of the given variable (given as a
	/// [`Lit`]).
	pub fn unphase(&mut self, lit: Lit) {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe { ccadical_unphase(self.ipasir_store().solver_ptr(), lit.0.get()) }
	}
}

impl AccessIpasirStore for Cadical {
	type Store = IpasirStore<Self, 1, 1, 1>;

	fn ipasir_store(&self) -> &Self::Store {
		&self.store
	}

	fn ipasir_store_mut(&mut self) -> &mut Self::Store {
		&mut self.store
	}
}

impl From<&Cnf> for Cadical {
	fn from(value: &Cnf) -> Self {
		let mut slv: Self = Default::default();
		*slv.ipasir_store_mut().vars_mut() = value.nvar;
		for cl in value.iter() {
			// Ignore early detected unsatisfiability
			let _ = slv.add_clause(cl.iter().copied());
		}
		slv
	}
}

impl IpasirAssumptionMethods for Cadical {
	const IPASIR_ASSUME: unsafe extern "C" fn(*mut c_void, i32) = ccadical_assume;
	const IPASIR_FAILED: unsafe extern "C" fn(*mut c_void, i32) -> c_int = ccadical_failed;
}

impl IpasirLearnCallbackMethod for Cadical {
	const IPASIR_SET_LEARN_CALLBACK: unsafe extern "C" fn(
		*mut c_void,
		*mut c_void,
		c_int,
		Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	) = ccadical_set_learn;
}

impl IpasirSolverMethods for Cadical {
	const IPASIR_ADD: unsafe extern "C" fn(*mut c_void, i32) = ccadical_add;
	const IPASIR_INIT: unsafe extern "C" fn() -> *mut c_void = ccadical_init;
	const IPASIR_RELEASE: unsafe extern "C" fn(*mut c_void) = ccadical_release;
	const IPASIR_SOLVE: unsafe extern "C" fn(*mut c_void) -> c_int = ccadical_solve;
	const IPASIR_VAL: unsafe extern "C" fn(*mut c_void, i32) -> i32 = ccadical_val;
}

impl IpasirTermCallbackMethod for Cadical {
	const IPASIR_SET_TERMINATE_CALLBACK: unsafe extern "C" fn(
		*mut c_void,
		*mut c_void,
		Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	) = ccadical_set_terminate;
}

#[cfg(feature = "external-propagation")]
impl IpasirUserPropagationMethods for Cadical {
	const IPASIR_ADD_OBSERVED_VAR: unsafe extern "C" fn(slv: *mut c_void, lit: i32) =
		ccadical_add_observed_var;
	const IPASIR_CONNECT_EXTERNAL_PROPAGATOR: unsafe extern "C" fn(
		slv: *mut c_void,
		propagator: CExternalPropagator,
	) = ccadical_connect_external_propagator;
	const IPASIR_DISCONNECT_EXTERNAL_PROPAGATOR: unsafe extern "C" fn(slv: *mut c_void) =
		ccadical_disconnect_external_propagator;
	const IPASIR_FORCE_BACKTRACK: unsafe extern "C" fn(slv: *mut c_void, level: usize) =
		ccadical_force_backtrack;
	const IPASIR_IS_DECISION: unsafe extern "C" fn(slv: *mut c_void, lit: i32) -> bool =
		ccadical_is_decision;
	const IPASIR_PHASE: unsafe extern "C" fn(slv: *mut c_void, lit: i32) = ccadical_phase;
	const IPASIR_REMOVE_OBSERVED_VAR: unsafe extern "C" fn(slv: *mut c_void, lit: i32) =
		ccadical_remove_observed_var;
	const IPASIR_RESET_OBSERVED_VARS: unsafe extern "C" fn(slv: *mut c_void) =
		ccadical_reset_observed_vars;
	const IPASIR_UNPHASE: unsafe extern "C" fn(slv: *mut c_void, lit: i32) = ccadical_unphase;
}

impl fmt::Debug for Cadical {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let tracers: Vec<_> = self.tracers.iter().map(Rc::as_ptr).collect();
		f.debug_struct("Cadical")
			.field("store", &self.store)
			.field("tracers", &tracers)
			.finish()
	}
}

mod ffi {
	use std::{
		cell::RefCell,
		ffi::{c_int, c_void},
		num::NonZero,
		slice,
	};

	use crate::{
		solver::cadical::{ProofConclusionType, ProofTracer},
		Lit,
	};

	pub(super) unsafe extern "C" fn add_assumption<P: ProofTracer>(data: *mut c_void, lit: c_int) {
		let tracer = &*(data as *const RefCell<P>);
		tracer.borrow_mut().add_assumption(Lit::from_raw(
			NonZero::new(lit).expect("zero cannot be a literal"),
		));
	}

	pub(super) unsafe extern "C" fn add_assumption_clause<P: ProofTracer>(
		data: *mut c_void,
		id: u64,
		clause: *const c_int,
		clause_len: usize,
		antecedents: *const u64,
		antecedents_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause = if clause_len != 0 {
			slice::from_raw_parts(clause as *const Lit, clause_len)
		} else {
			&[]
		};
		let antecedents = if antecedents_len != 0 {
			slice::from_raw_parts(antecedents, antecedents_len)
		} else {
			&[]
		};
		tracer
			.borrow_mut()
			.add_assumption_clause(id, clause, antecedents);
	}

	pub(super) unsafe extern "C" fn add_constraint<P: ProofTracer>(
		data: *mut c_void,
		clause: *const c_int,
		clause_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause = if clause_len != 0 {
			slice::from_raw_parts(clause as *const Lit, clause_len)
		} else {
			&[]
		};
		tracer.borrow_mut().add_constraint(clause);
	}

	pub(super) unsafe extern "C" fn add_derived_clause<P: ProofTracer>(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
		antecedents: *const u64,
		antecedents_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause = if clause_len != 0 {
			slice::from_raw_parts(clause as *const Lit, clause_len)
		} else {
			&[]
		};
		let antecedents = if antecedents_len != 0 {
			slice::from_raw_parts(antecedents, antecedents_len)
		} else {
			&[]
		};
		tracer
			.borrow_mut()
			.add_derived_clause(id, redundant, clause, antecedents);
	}

	pub(super) unsafe extern "C" fn add_original_clause<P: ProofTracer>(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
		restored: bool,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause = if clause_len != 0 {
			slice::from_raw_parts(clause as *const Lit, clause_len)
		} else {
			&[]
		};
		tracer
			.borrow_mut()
			.add_original_clause(id, redundant, clause, restored);
	}

	pub(super) unsafe extern "C" fn begin_proof<P: ProofTracer>(
		data: *mut c_void,
		first_derived: u64,
	) {
		let tracer = &*(data as *const RefCell<P>);
		tracer.borrow_mut().begin_proof(first_derived);
	}

	pub(super) unsafe extern "C" fn conclude_sat<P: ProofTracer>(
		data: *mut c_void,
		assignment: *const c_int,
		assignment_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let assignment = if assignment_len != 0 {
			slice::from_raw_parts(assignment as *const Lit, assignment_len)
		} else {
			&[]
		};
		tracer.borrow_mut().conclude_sat(assignment);
	}

	pub(super) unsafe extern "C" fn conclude_unknown<P: ProofTracer>(
		data: *mut c_void,
		trail: *const c_int,
		trail_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let trail = if trail_len != 0 {
			slice::from_raw_parts(trail as *const Lit, trail_len)
		} else {
			&[]
		};
		tracer.borrow_mut().conclude_unknown(trail);
	}

	pub(super) unsafe extern "C" fn conclude_unsat<P: ProofTracer>(
		data: *mut c_void,
		conclusion_type: u8,
		clause_ids: *const u64,
		clause_ids_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause_ids = if clause_ids_len != 0 {
			slice::from_raw_parts(clause_ids, clause_ids_len)
		} else {
			&[]
		};
		let conclusion_type = match conclusion_type {
			1 => ProofConclusionType::Conflict,
			2 => ProofConclusionType::Assumptions,
			4 => ProofConclusionType::Constraint,
			_ => panic!("invalid conclusion type"),
		};
		tracer
			.borrow_mut()
			.conclude_unsat(conclusion_type, clause_ids);
	}

	pub(super) unsafe extern "C" fn delete_clause<P: ProofTracer>(
		data: *mut c_void,
		id: u64,
		redundant: bool,
		clause: *const c_int,
		clause_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause = if clause_len != 0 {
			slice::from_raw_parts(clause as *const Lit, clause_len)
		} else {
			&[]
		};
		tracer.borrow_mut().delete_clause(id, redundant, clause);
	}

	pub(super) unsafe extern "C" fn finalize_clause<P: ProofTracer>(
		data: *mut c_void,
		id: u64,
		clause: *const c_int,
		clause_lens: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause = if clause_lens != 0 {
			slice::from_raw_parts(clause as *const Lit, clause_lens)
		} else {
			&[]
		};
		tracer.borrow_mut().finalize_clause(id, clause);
	}

	pub(super) unsafe extern "C" fn report_status<P: ProofTracer>(
		data: *mut c_void,
		status: c_int,
		id: u64,
	) {
		let tracer = &*(data as *const RefCell<P>);
		tracer.borrow_mut().report_status(status, id);
	}

	pub(super) unsafe extern "C" fn reset_assumptions<P: ProofTracer>(data: *mut c_void) {
		let tracer = &*(data as *const RefCell<P>);
		tracer.borrow_mut().reset_assumptions();
	}

	pub(super) unsafe extern "C" fn solve_query<P: ProofTracer>(data: *mut c_void) {
		let tracer = &*(data as *const RefCell<P>);
		tracer.borrow_mut().solve_query();
	}

	pub(super) unsafe extern "C" fn strengthen<P: ProofTracer>(data: *mut c_void, id: u64) {
		let tracer = &*(data as *const RefCell<P>);
		tracer.borrow_mut().strengthen(id);
	}

	pub(super) unsafe extern "C" fn weaken_minus<P: ProofTracer>(
		data: *mut c_void,
		id: u64,
		clause: *const c_int,
		clause_len: usize,
	) {
		let tracer = &*(data as *const RefCell<P>);
		let clause = if clause_len != 0 {
			slice::from_raw_parts(clause as *const Lit, clause_len)
		} else {
			&[]
		};
		tracer.borrow_mut().weaken_minus(id, clause);
	}
}

#[cfg(test)]
mod tests {
	use std::iter::repeat_with;

	use itertools::Itertools;
	use traced_test::test;

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		helpers::tests::{assert_solutions, expect_file},
		solver::{
			cadical::Cadical, Assumptions, FailedAssumptions, SolveResult, Solver, TermSignal,
			TerminateCallback,
		},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder, Lit, Unsatisfiable, Valuation,
	};

	#[test]
	fn clone() {
		let mut slv = Cadical::default();
		let (a, b) = slv.new_lits();
		slv.add_clause([a, b]).unwrap();

		let mut cp = slv.shallow_clone();
		cp.add_clause([!a]).unwrap();
		cp.add_clause([!b]).unwrap();

		let SolveResult::Satisfied(solution) = slv.solve() else {
			unreachable!()
		};
		assert!(solution.value(a) && solution.value(b));

		let SolveResult::Unsatisfiable(_) = cp.solve() else {
			unreachable!()
		};
	}

	#[test]
	fn empty_clause() {
		let mut slv = Cadical::default();
		assert_eq!(slv.add_clause([false]), Err(Unsatisfiable));
		assert!(matches!(slv.solve(), SolveResult::Unsatisfiable(_)));
	}

	#[test]
	fn empty_clause_2() {
		let mut slv = Cadical::default();
		const EMPTY: [BoolVal; 0] = [];
		assert_eq!(slv.add_clause(EMPTY), Err(Unsatisfiable));
		assert!(matches!(slv.solve(), SolveResult::Unsatisfiable(_)));
	}

	#[test]
	fn empty_formula() {
		let mut cnf = Cnf::default();
		assert_solutions(
			&cnf,
			Vec::<Lit>::new(),
			&expect_file!["cadical/test_cadical_empty_formula.sol"],
		);

		let mut slv = Cadical::from(&cnf);
		assert!(matches!(slv.solve(), SolveResult::Satisfied(_)));
	}

	#[test]
	fn empty_formula_single_var() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		assert_solutions(
			&cnf,
			Vec::<Lit>::new(),
			&expect_file!["cadical/test_cadical_empty_formula_single_var.sol"],
		);

		let mut slv = Cadical::from(&cnf);
		assert!(matches!(slv.solve(), SolveResult::Satisfied(_)));
	}

	#[test]
	fn solve() {
		let mut slv = Cadical::default();

		let a = slv.new_var().into();
		let b = slv.new_var().into();
		PairwiseEncoder::default()
			.encode(
				&mut slv,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();
		let SolveResult::Satisfied(solution) = slv.solve() else {
			unreachable!()
		};
		assert!(
			(solution.value(!a) && solution.value(b)) || (solution.value(a) && solution.value(!b))
		);
	}

	#[test]
	fn terminate_callback() {
		let mut slv = Cadical::default();

		// Encode a pidgeon hole problem that is not trivially solvable
		const LARGE: usize = 10;
		let vars: Vec<_> = repeat_with(|| slv.new_var_range(LARGE - 1))
			.take(LARGE)
			.collect();
		for x in vars.iter().permutations(2) {
			let &[a, b] = x.as_slice() else {
				unreachable!()
			};
			for i in 0..(LARGE - 1) {
				let a_lit = a.index(i);
				let b_lit = b.index(i);
				slv.add_clause([!a_lit, !b_lit]).unwrap();
			}
		}
		// Set termination callback that stops immediately
		slv.set_terminate_callback(Some(|| TermSignal::Terminate));
		assert!(matches!(slv.solve(), SolveResult::Unknown));
	}

	#[test]
	fn test_failed() {
		let mut cnf = Cnf::default();
		let x = cnf.new_lit();
		let y = cnf.new_lit();
		// An unsatisfiable problem with only `x` in the unsat core
		// same as the tie/shirt example unit test in the Cadical repo
		cnf.add_clause([x, y]).unwrap();
		cnf.add_clause([!x, !y]).unwrap();
		cnf.add_clause([!x, y]).unwrap();
		let mut slv = Cadical::from(&cnf);
		match slv.solve_assuming([x, y]) {
			SolveResult::Unsatisfiable(fail) => {
				assert!(fail.fail(x), "`x` should be responsible");
				assert!(
					!fail.fail(y),
					"`y` is not an assumption, so is not in the core"
				);
			}
			_ => panic!(),
		};
	}

	#[test]
	fn trivial_example() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		cnf.add_clause([a, !b]).unwrap();

		assert_solutions(
			&cnf,
			cnf.get_variables(),
			&expect_file!["cadical/test_cadical_trivial_example.sol"],
		);
		let mut slv = Cadical::from(&cnf);
		assert!(matches!(slv.solve(), SolveResult::Satisfied(_)));
	}

	#[cfg(feature = "external-propagation")]
	#[test]
	fn user_propagator() {
		use std::{cell::RefCell, rc::Rc};

		use itertools::Itertools;

		use crate::{
			helpers::tests::assert_solutions,
			solver::{
				propagation::{
					ClausePersistence, ExternalPropagation, Propagator, PropagatorDefinition,
					SolvingActions,
				},
				VarRange,
			},
			ClauseDatabase, Lit,
		};

		let mut slv = Cadical::default();

		let vars = slv.new_var_range(5);

		struct Dist2 {
			vars: VarRange,
			tmp: Vec<Vec<Lit>>,
		}
		impl Propagator for Dist2 {
			fn check_solution(
				&mut self,
				_slv: &mut dyn SolvingActions,
				model: &dyn crate::Valuation,
			) -> bool {
				let mut vars = self.vars.clone();
				while let Some(v) = vars.next() {
					if model.value(v.into()) {
						let next_2 = vars.clone().take(2);
						for o in next_2 {
							if model.value(o.into()) {
								self.tmp.push(vec![!v, !o]);
							}
						}
					}
				}
				self.tmp.is_empty()
			}
			fn add_external_clause(
				&mut self,
				_slv: &mut dyn SolvingActions,
			) -> Option<(Vec<Lit>, ClausePersistence)> {
				self.tmp.pop().map(|c| (c, ClausePersistence::Forgettable))
			}
		}
		impl PropagatorDefinition for Dist2 {
			const CHECK_ONLY: bool = true;
		}

		let p = Rc::new(RefCell::new(Dist2 {
			vars,
			tmp: Vec::new(),
		}));
		assert_eq!(Rc::strong_count(&p), 1);
		slv.connect_propagator(Rc::clone(&p));
		assert_eq!(Rc::strong_count(&p), 2);
		slv.add_clause(vars).unwrap();
		for v in vars {
			slv.add_observed_var(v)
		}

		let mut solns: Vec<Vec<Lit>> = Vec::new();
		while let SolveResult::Satisfied(sol) = slv.solve() {
			let sol: Vec<Lit> = vars
				.clone()
				.map(|v| if sol.value(v.into()) { v.into() } else { !v })
				.collect_vec();
			solns.push(sol);
			slv.add_clause(solns.last().unwrap().iter().map(|&l| !l))
				.unwrap()
		}
		solns.sort();

		let (a, b, c, d, e) = vars.clone().iter_lits().collect_tuple().unwrap();
		assert_eq!(
			solns,
			vec![
				vec![a, !b, !c, d, !e],
				vec![a, !b, !c, !d, e],
				vec![a, !b, !c, !d, !e],
				vec![!a, b, !c, !d, e],
				vec![!a, b, !c, !d, !e],
				vec![!a, !b, c, !d, !e],
				vec![!a, !b, !c, d, !e],
				vec![!a, !b, !c, !d, e],
			]
		);
		assert!(p.borrow().tmp.is_empty());

		// Test disconnecting propagator
		slv.disconnect_propagator();
		assert_eq!(Rc::strong_count(&p), 1);
		slv.connect_propagator(Rc::clone(&p));
		assert_eq!(Rc::strong_count(&p), 2);
		// Test correct release of propagator on drop
		drop(slv);
		assert_eq!(Rc::strong_count(&p), 1);
	}
}
