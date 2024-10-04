use pindakaas_derive::IpasirSolver;

use super::VarFactory;

#[derive(Debug, IpasirSolver)]
#[ipasir(krate = pindakaas_kissat)]
pub struct Kissat {
	ptr: *mut std::ffi::c_void,
	vars: VarFactory,
}

impl Default for Kissat {
	fn default() -> Self {
		Self {
			// SAFETY: Assume correct creation of the solver using the IPASIR API.
			ptr: unsafe { pindakaas_kissat::ipasir_init() },
			vars: VarFactory::default(),
		}
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use super::*;
	use crate::{
		linear::LimitComp,
		solver::{SolveResult, Solver},
		CardinalityOne, ClauseDatabase, Encoder, PairwiseEncoder, Valuation,
	};

	#[test]
	fn test_kissat() {
		let mut slv = Kissat::default();
		assert!(slv.signature().starts_with("kissat"));

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
	}
}
