use pindakaas_derive::IpasirSolver;

use super::VarFactory;

#[derive(IpasirSolver)]
#[ipasir(krate = pindakaas_intel_sat, assumptions, learn_callback, term_callback)]
pub struct IntelSat {
	ptr: *mut std::ffi::c_void,
	vars: VarFactory,
}

impl Default for IntelSat {
	fn default() -> Self {
		Self {
			ptr: unsafe { pindakaas_intel_sat::ipasir_init() },
			vars: VarFactory::default(),
		}
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
	fn test_intel_sat() {
		let mut slv = IntelSat::default();
		assert!(slv.signature().starts_with("IntelSat"));
		let a = slv.new_var();
		let b = slv.new_var();
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
