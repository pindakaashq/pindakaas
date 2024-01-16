use pindakaas_derive::IpasirSolver;

use super::VarFactory;
use crate::Lit;

#[derive(IpasirSolver)]
#[ipasir(krate = pindakaas_cadical, assumptions, learn_callback, term_callback, ipasir_up)]
pub struct Cadical {
	ptr: *mut std::ffi::c_void,
	vars: VarFactory,
	prop: Option<Box<CadicalProp>>,
}

impl Default for Cadical {
	fn default() -> Self {
		Self {
			ptr: unsafe { pindakaas_cadical::ipasir_init() },
			vars: VarFactory::default(),
			prop: None,
		}
	}
}

impl Cadical {
	pub fn phase(&mut self, lit: Lit) {
		unsafe { pindakaas_cadical::ccadical_phase(self.ptr, lit.0.get()) }
	}

	pub fn unphase(&mut self, lit: Lit) {
		unsafe { pindakaas_cadical::ccadical_unphase(self.ptr, lit.0.get()) }
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		linear::LimitComp,
		solver::{PropagatingSolver, Propagator, SolveResult, Solver},
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
	}
}
