use std::ffi::c_void;

use pindakaas_derive::IpasirSolver;

use super::VarFactory;
use crate::solver::libloading::FFIPointer;

#[derive(Debug, IpasirSolver)]
#[ipasir(krate = pindakaas_intel_sat, assumptions, learn_callback, term_callback)]
pub struct IntelSat {
	/// The raw pointer to the Intel SAT solver.
	ptr: *mut c_void,
	/// The variable factory for this solver.
	vars: VarFactory,
	/// The callback used when a clause is learned.
	learn_cb: FFIPointer,
	/// The callback used to check whether the solver should terminate.
	term_cb: FFIPointer,
}

impl Default for IntelSat {
	fn default() -> Self {
		Self {
			ptr: unsafe { pindakaas_intel_sat::ipasir_init() },
			vars: VarFactory::default(),
			term_cb: FFIPointer::default(),
			learn_cb: FFIPointer::default(),
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
		CardinalityOne, ClauseDatabase, Encoder, PairwiseEncoder, Valuation,
	};

	#[test]
	fn test_intel_sat() {
		let mut slv = IntelSat::default();
		assert!(slv.signature().starts_with("IntelSat"));
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
