use std::{
	ffi::{c_void, CString},
	fmt,
};

use pindakaas_cadical::{ccadical_copy, ccadical_phase, ccadical_unphase};
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

	pub fn unphase(&mut self, lit: Lit) {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe { ccadical_unphase(self.ptr, lit.0.get()) }
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

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		solver::{cadical::Cadical, SlvTermSignal, SolveResult},
	};

	use crate::solver::Solver;
	use crate::ClauseDatabase;
	use crate::Encoder;
	use crate::Valuation;


        use crate::solver::TermCallback;

	#[test]
	fn test_cadical_term() {
		let mut slv = Cadical::default();

                slv.set_terminate_callback(Some(move || SlvTermSignal::Terminate));
                assert!(matches!(slv.solve(), SolveResult::Unknown));
	}

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
		// Test clone implementation
		let mut cp = slv.clone();
		let SolveResult::Satisfied(solution) = cp.solve() else {
			unreachable!()
		};
		assert!(
			(solution.value(!a) && solution.value(b)) || (solution.value(a) && solution.value(!b))
		);
	}

	use crate::Cnf;
	use std::path::Path;

	// #[test]
	// fn test_cadical_examples() {
	// 	let mut slv = Cadical::default();
	// 	slv.clone()
	// 		.add_cnf(Cnf::from_file(Path::new("res/dimacs/ex1.dimacs")).unwrap());
	// assert_solutions(
	// &cnf,
	// vec![a, b, c],
	// &expect_file!["res/dimacs/ex1.cnf.sol"],
	// );
	// 	assert_eq!(slv.solve(), SolveResult::Satisfied(MapSol::default()));
	// 	slv.clone()
	// 		.add_cnf(Cnf::from_file(Path::new("res/dimacs/ex2.dimacs")).unwrap());
	// 	// assert_eq!(slv.solve(|_| ()), SolveResult::Unsat); // TODO failing.
	// 	slv.clone()
	// 		.add_cnf(Cnf::from_file(Path::new("res/dimacs/ex3.dimacs")).unwrap());
	// 	assert_eq!(slv.solve(|_| ()), SolveResult::Satisfied(_));
	// }

	use crate::Unsatisfiable;
	#[test]
	fn test_cadical_empty_clause() {
		let mut slv = Cadical::default();
		assert_eq!(slv.add_clause([]), Err(Unsatisfiable));
		assert!(matches!(slv.solve(), SolveResult::Unsatisfiable(_)));
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
			Lit,
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
			vars: vars.clone(),
			tmp: Vec::new(),
		};
		let mut slv = slv.with_propagator(p);
		slv.add_clause(vars.clone().map_into()).unwrap();
		for v in vars.clone() {
			PropagatingSolver::add_observed_var(&mut slv, v)
		}

		let solns: Vec<Vec<Lit>> = slv
			.solve_all(&vars.into_iter().collect_vec())
			.into_iter()
			.map(|sol| sol.try_into().unwrap())
			.sorted()
			.collect_vec();

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
