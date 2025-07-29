use std::{
	ffi::{c_int, c_void, CString},
	marker::PhantomData,
};

use pindakaas_cadical::{
	ccadical_add, ccadical_assume, ccadical_copy, ccadical_failed, ccadical_get_option,
	ccadical_init, ccadical_limit, ccadical_phase, ccadical_release, ccadical_set_learn,
	ccadical_set_option, ccadical_set_terminate, ccadical_solve, ccadical_unphase, ccadical_val,
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
	ipasir::user_propagation::IpasirUserPropagationMethods, propagation::PropagatingSolver,
};
use crate::{
	helpers::opt_field::OptField,
	solver::{
		ipasir::{
			AccessIpasirStore, BasicIpasirStorage, IpasirAssumptionMethods,
			IpasirLearnCallbackMethod, IpasirSolverMethods, IpasirStore, IpasirStoreInner,
			IpasirTermCallbackMethod,
		},
		LearnCallback, SlvTermSignal, TerminateCallback,
	},
	ClauseDatabaseTools, Cnf, Lit, VarRange,
};

#[derive(Debug, Default)]
pub struct Cadical {
	store: IpasirStore<Cadical, 1, 1, 1>,
}

impl Cadical {
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
	/// Check whether a given literal is marked as observed in the solver's
	/// for the [`PropagatingSolver`] interface.
	pub fn is_observed(&self, lit: Lit) -> bool {
		// SAFETY: Pointer known to be non-null, lit is known to be non-zero and not
		// MIN_INT as required by Cadical.
		unsafe { ccadical_is_observed(self.ipasir_store().solver_ptr(), lit.0.get()) }
	}

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

	/// Make a shallow clone of the [`Cadical`] solver using an efficient internal method.
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
		};
		// Make sure no pointers are left behind in the backend.
		slv.set_learn_callback::<fn(&mut dyn Iterator<Item = Lit>)>(None);
		slv.set_terminate_callback::<fn() -> SlvTermSignal>(None);
		#[cfg(feature = "external-propagation")]
		slv.disconnect_propagator();

		slv
	}

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
	const IPASIR_REMOVE_OBSERVED_VAR: unsafe extern "C" fn(slv: *mut c_void, lit: i32) =
		ccadical_remove_observed_var;
	const IPASIR_RESET_OBSERVED_VARS: unsafe extern "C" fn(slv: *mut c_void) =
		ccadical_reset_observed_vars;
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
		solver::{cadical::Cadical, SlvTermSignal, SolveResult, Solver, TerminateCallback},
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
		slv.set_terminate_callback(Some(|| SlvTermSignal::Terminate));
		assert!(matches!(slv.solve(), SolveResult::Unknown));
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
					ClausePersistence, PropagatingSolver, Propagator, PropagatorDefinition,
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
