use pindakaas_derive::IpasirSolver;

use crate::VarFactory;

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

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		solver::{kissat::Kissat, SolveResult, Solver},
		ClauseDatabase, Encoder, Valuation,
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
		let SolveResult::Satisfied(solution) = slv.solve() else {
			unreachable!()
		};
		assert!(
			(solution.value(!a) && solution.value(b)) || (solution.value(a) && solution.value(!b))
		);
	}
}
