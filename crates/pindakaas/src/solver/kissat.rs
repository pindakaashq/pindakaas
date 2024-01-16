use pindakaas_derive::IpasirSolver;

use super::VarFactory;

#[derive(IpasirSolver)]
#[ipasir(krate = pindakaas_kissat)]
pub struct Kissat {
	ptr: *mut std::ffi::c_void,
	vars: VarFactory,
}

impl Default for Kissat {
	fn default() -> Self {
		Self {
			ptr: unsafe { pindakaas_kissat::ipasir_init() },
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
		let res = slv.solve(|value| {
			assert!(
				(value(!a).unwrap() && value(b).unwrap())
					|| (value(a).unwrap() && value(!b).unwrap()),
			)
		});
		assert_eq!(res, SolveResult::Sat);
	}
}
