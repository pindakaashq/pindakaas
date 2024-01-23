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
		CardinalityOne, ClauseDatabase, Encoder, PairwiseEncoder,
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
		let res = slv.solve(|value| {
			assert!(
				(value(!a).unwrap() && value(b).unwrap())
					|| (value(a).unwrap() && value(!b).unwrap()),
			)
		});
		assert_eq!(res, SolveResult::Sat);
		// Test clone implementation
		let mut cp = slv.clone();
		cp.solve(|value| {
			assert!(
				(value(!a).unwrap() && value(b).unwrap())
					|| (value(a).unwrap() && value(!b).unwrap()),
			)
		});
	}

	#[cfg(feature = "ipasir-up")]
	#[test]
	fn test_ipasir_up() {
		use itertools::Itertools;

		use crate::{
			helpers::tests::lits,
			solver::{PropagatingSolver, Propagator, VarRange},
		};

		let mut slv = Cadical::default();

		let vars = slv.new_var_range(5);

		struct Dist2 {
			vars: VarRange,
			tmp: Vec<Vec<Lit>>,
		}
		impl Propagator for Dist2 {
			fn is_lazy(&self) -> bool {
				true
			}
			fn check_model(&mut self, value: &dyn crate::Valuation) -> bool {
				let mut vars = self.vars.clone();
				while let Some(v) = vars.next() {
					if value(v.into()).unwrap_or(true) {
						let next_2 = vars.clone().take(2);
						for o in next_2 {
							if value(o.into()).unwrap_or(true) {
								self.tmp.push(vec![!v, !o]);
							}
						}
					}
				}
				self.tmp.is_empty()
			}
			fn add_external_clause(&mut self) -> Option<Vec<Lit>> {
				self.tmp.pop()
			}
		}

		let p = Box::new(Dist2 {
			vars: vars.clone(),
			tmp: Vec::new(),
		});
		slv.set_external_propagator(Some(p));
		slv.add_clause(vars.clone().map_into()).unwrap();
		for v in vars.clone() {
			slv.add_observed_var(v)
		}

		let mut solns = Vec::new();
		while slv.solve(|value| {
			let sol: Vec<Lit> = vars
				.clone()
				.map(|v| {
					if value(v.into()).unwrap() {
						v.into()
					} else {
						!v
					}
				})
				.collect_vec();
			solns.push(sol);
		}) == SolveResult::Sat
		{
			slv.add_clause(solns.last().unwrap().iter().map(|l| !l))
				.unwrap()
		}
		solns.sort();
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
	}
}
