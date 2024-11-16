use std::fmt;

use pindakaas_cadical::{ccadical_copy, ccadical_phase, ccadical_unphase};
use pindakaas_derive::IpasirSolver;

use super::VarFactory;
use crate::Lit;

#[derive(IpasirSolver)]
#[ipasir(krate = pindakaas_cadical, assumptions, learn_callback, term_callback, ipasir_up)]
pub struct Cadical {
	ptr: *mut std::ffi::c_void,
	vars: VarFactory,
	#[cfg(feature = "ipasir-up")]
	prop: Option<Box<CadicalProp>>,
}

impl Default for Cadical {
	fn default() -> Self {
		Self {
			ptr: unsafe { pindakaas_cadical::ipasir_init() },
			vars: VarFactory::default(),
			#[cfg(feature = "ipasir-up")]
			prop: None,
		}
	}
}

impl Clone for Cadical {
	fn clone(&self) -> Self {
		let ptr = unsafe { ccadical_copy(self.ptr) };
		Self {
			ptr,
			vars: self.vars,
			#[cfg(feature = "ipasir-up")]
			prop: None,
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

impl Cadical {
	pub fn phase(&mut self, lit: Lit) {
		unsafe { ccadical_phase(self.ptr, lit.0.get()) }
	}

	pub fn unphase(&mut self, lit: Lit) {
		unsafe { ccadical_unphase(self.ptr, lit.0.get()) }
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		linear::LimitComp,
		solver::{SolveResult, Solver},
		CardinalityOne, ClauseDatabase, Encoder, PairwiseEncoder, Valuation,
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
		let res = slv.solve(|model| {
			assert!(
				(model.value(!a).unwrap() && model.value(b).unwrap())
					|| (model.value(a).unwrap() && model.value(!b).unwrap()),
			)
		});
		assert_eq!(res, SolveResult::Sat);
		// Test clone implementation
		let mut cp = slv.clone();
		cp.solve(|model| {
			assert!(
				(model.value(!a).unwrap() && model.value(b).unwrap())
					|| (model.value(a).unwrap() && model.value(!b).unwrap()),
			)
		});
	}
	use crate::Cnf;
	use std::path::Path;
	#[test]
	fn test_cadical_examples() {
		let mut slv = Cadical::default();
		slv.clone()
			.add_cnf(Cnf::from_file(Path::new("res/dimacs/ex1.dimacs")).unwrap());
		assert_eq!(slv.solve(|_| ()), SolveResult::Sat);
		slv.clone()
			.add_cnf(Cnf::from_file(Path::new("res/dimacs/ex2.dimacs")).unwrap());
		// assert_eq!(slv.solve(|_| ()), SolveResult::Unsat); // TODO failing.
		slv.clone()
			.add_cnf(Cnf::from_file(Path::new("res/dimacs/ex3.dimacs")).unwrap());
		assert_eq!(slv.solve(|_| ()), SolveResult::Sat);
	}

	#[cfg(feature = "ipasir-up")]
	#[test]
	fn test_ipasir_up() {
		use std::any::Any;

		use itertools::Itertools;

		use crate::{
			helpers::tests::lits,
			solver::{
				NextVarRange, PropagatingSolver, Propagator, PropagatorAccess, SolvingActions,
				VarRange,
			},
		};

		let mut slv = Cadical::default();

		let vars = slv.next_var_range(5).unwrap();

		struct Dist2 {
			vars: VarRange,
			tmp: Vec<Vec<Lit>>,
		}
		impl Propagator for Dist2 {
			fn is_lazy(&self) -> bool {
				true
			}
			fn check_model(
				&mut self,
				_slv: &mut dyn SolvingActions,
				model: &dyn crate::Valuation,
			) -> bool {
				let mut vars = self.vars.clone();
				while let Some(v) = vars.next() {
					if model.value(v.into()).unwrap_or(true) {
						let next_2 = vars.clone().take(2);
						for o in next_2 {
							if model.value(o.into()).unwrap_or(true) {
								self.tmp.push(vec![!v, !o]);
							}
						}
					}
				}
				self.tmp.is_empty()
			}
			fn add_external_clause(&mut self, _slv: &mut dyn SolvingActions) -> Option<Vec<Lit>> {
				self.tmp.pop()
			}

			fn as_any(&self) -> &dyn Any {
				self
			}
			fn as_mut_any(&mut self) -> &mut dyn Any {
				self
			}
		}

		let p = Box::new(Dist2 {
			vars: vars.clone(),
			tmp: Vec::new(),
		});
		slv.set_external_propagator(Some(p));
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
		assert_eq!(
			solns,
			vec![
				lits![1, -2, -3, 4, -5],
				lits![1, -2, -3, -4, 5],
				lits![1, -2, -3, -4, -5],
				lits![-1, 2, -3, -4, 5],
				lits![-1, 2, -3, -4, -5],
				lits![-1, -2, 3, -4, -5],
				lits![-1, -2, -3, 4, -5],
				lits![-1, -2, -3, -4, 5],
			]
		);
		assert!(slv.propagator::<Dist2>().unwrap().tmp.is_empty())
	}
}
