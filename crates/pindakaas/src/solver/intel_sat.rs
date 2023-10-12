use super::ipasir_solver;

ipasir_solver!(pindakaas_intel_sat, IntelSat);

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
		let res = slv.solve(
			|value| {
				assert!(
					(value(!a).unwrap() && value(b).unwrap())
						|| (value(a).unwrap() && value(!b).unwrap()),
				)
			},
			|_| {},
		);
		assert_eq!(res, SolveResult::Sat);
	}
}
