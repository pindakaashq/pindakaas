use std::{
	ffi::{c_void, CString},
	fmt,
};

use pindakaas_cadical::{ccadical_copy, ccadical_enable_proof, ccadical_phase, ccadical_unphase};
use pindakaas_derive::IpasirSolver;

use crate::{solver::FFIPointer, Lit, VarFactory};

#[derive(IpasirSolver)]
#[ipasir(krate = pindakaas_cadical, assumptions, learn_callback, term_callback, ipasir_up)]
pub struct Cadical {
	/// The raw pointer to the Cadical solver.
	ptr: *mut c_void,
	/// The variable factory for this solver.
	vars: VarFactory,
	/// The callback used when a clause is learned.
	learn_cb: FFIPointer,
	/// The callback used to check whether the solver should terminate.
	term_cb: FFIPointer,
}

impl Cadical {
	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn get_option(&self, name: &str) -> i32 {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { pindakaas_cadical::ccadical_get_option(self.ptr, name.as_ptr()) }
	}

	#[cfg(feature = "external-propagation")]
	/// Check whether a given literal is marked as observed in the solver's
	/// external propagator interface.
	fn is_observed(&self, lit: Lit) -> bool {
		// SAFETY: Pointer known to be non-null, lit is known to be non-zero and not
		// MIN_INT as required by Cadical.
		unsafe { pindakaas_cadical::ccadical_is_observed(self.ptr, lit.0.get()) }
	}

	pub fn phase(&mut self, lit: Lit) {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe { ccadical_phase(self.ptr, lit.0.get()) }
	}

	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn set_option(&mut self, name: &str, value: i32) {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { pindakaas_cadical::ccadical_set_option(self.ptr, name.as_ptr(), value) }
	}

	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn set_limit(&mut self, name: &str, value: i32) {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { pindakaas_cadical::ccadical_limit(self.ptr, name.as_ptr(), value) }
	}

	pub fn unphase(&mut self, lit: Lit) {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe { ccadical_unphase(self.ptr, lit.0.get()) }
	}

	pub fn enable_proof(&mut self, name: &str) {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer is known to be valid, CaDiCaL's file API should handle
		// all possible name paths.
		unsafe {
			ccadical_enable_proof(self.ptr, name.as_ptr());
		}
	}
}

impl Clone for Cadical {
	fn clone(&self) -> Self {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		let ptr = unsafe { ccadical_copy(self.ptr) };
		let vars = self.vars; // Copy
		Self {
			ptr,
			vars,
			learn_cb: FFIPointer::default(),
			term_cb: FFIPointer::default(),
		}
	}
}

impl Default for Cadical {
	fn default() -> Self {
		Self {
			// SAFETY: Assume ipasir_init() returns a non-null pointer.
			ptr: unsafe { pindakaas_cadical::ipasir_init() },
			vars: VarFactory::default(),
			learn_cb: FFIPointer::default(),
			term_cb: FFIPointer::default(),
		}
	}
}

impl fmt::Debug for Cadical {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("Cadical")
			.field("ptr", &self.ptr)
			.field("vars", &self.vars)
			.finish()
	}
}

#[cfg(feature = "external-propagation")]
impl<P> Clone for PropagatingCadical<P>
where
	P: Clone + crate::solver::propagation::Propagator,
{
	fn clone(&self) -> Self {
		use crate::solver::propagation::{PropagatingSolver, WithPropagator};

		let cadical = self.solver().clone();
		let propagator = self.propagator().clone();
		let mut cadical = cadical.with_propagator(propagator);
		for v in self.solver().vars.emitted_vars() {
			if self.solver().is_observed(v.into()) {
				cadical.add_observed_var(v);
			}
		}
		cadical
	}
}

#[cfg(test)]
mod tests {
	use std::iter::repeat_with;

	use itertools::Itertools;
	use traced_test::test;
	use tracing::warn;

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		helpers::tests::{assert_solutions, expect_file},
		solver::{cadical::Cadical, SlvTermSignal, SolveResult, Solver, TermCallback},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder, Lit, Unsatisfiable, Valuation,
	};

	#[test]
	fn test_cadical() {
		let mut slv = Cadical::default();
		assert!(slv.signature().starts_with("cadical"));

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
	fn test_cadical_clone() {
		let mut slv = Cadical::default();
		let (a, b) = slv.new_lits();
		slv.add_clause([a, b]).unwrap();

		let mut cp = slv.clone();
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
	fn test_cadical_empty_clause() {
		let mut slv = Cadical::default();
		assert_eq!(slv.add_clause([false]), Err(Unsatisfiable));
		assert!(matches!(slv.solve(), SolveResult::Unsatisfiable(_)));
	}

	#[test]
	fn test_cadical_empty_clause_2() {
		let mut slv = Cadical::default();
		const EMPTY: [BoolVal; 0] = [];
		assert_eq!(slv.add_clause(EMPTY), Err(Unsatisfiable));
		assert!(matches!(slv.solve(), SolveResult::Unsatisfiable(_)));
	}

	#[test]
	fn test_cadical_terminate_callback() {
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
	fn test_cadical_trivial_example() {
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

	#[test]
	fn test_cadical_empty_formula() {
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
	fn test_cadical_empty_formula_single_var() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		assert_solutions(
			&cnf,
			Vec::<Lit>::new(),
			&expect_file!["cadical/test_cadical_empty_formula_single_var.sol"],
		);

		warn!("{}", cnf);
		let mut slv = Cadical::from(&cnf);
		assert!(matches!(slv.solve(), SolveResult::Satisfied(_)));
	}

	#[cfg(feature = "external-propagation")]
	#[test]
	fn test_ipasir_up() {
		use std::any::Any;

		use itertools::Itertools;

		use crate::{
			helpers::tests::assert_solutions,
			solver::{
				cadical::CadicalSol,
				propagation::{
					ClausePersistence, PropagatingSolver, Propagator, SolvingActions,
					WithPropagator,
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
			fn is_check_only(&self) -> bool {
				true
			}
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

		let p = Dist2 {
			vars,
			tmp: Vec::new(),
		};
		let mut slv = slv.with_propagator(p);
		slv.add_clause(vars).unwrap();
		for v in vars {
			PropagatingSolver::add_observed_var(&mut slv, v)
		}

		let mut solns: Vec<Vec<Lit>> = Vec::new();
		while let (_, SolveResult::Satisfied(sol)) = slv.solve() {
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
		assert!(slv.propagator().tmp.is_empty())
	}
}
