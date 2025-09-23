//! This module contains the pindakaas interface to the
//! [Intel SAT](https://github.com/alexander-nadel/intel_sat_solver) solver.

use std::ffi::{c_int, c_void};

use pindakaas_intel_sat::{
	intel_sat_add, intel_sat_assume, intel_sat_failed, intel_sat_init, intel_sat_release,
	intel_sat_set_learn, intel_sat_set_terminate, intel_sat_solve, intel_sat_val,
};

use crate::{
	solver::ipasir::{
		AccessIpasirStore, BasicIpasirStorage, IpasirAssumptionMethods, IpasirLearnCallbackMethod,
		IpasirSolverMethods, IpasirStore, IpasirTermCallbackMethod,
	},
	ClauseDatabaseTools, Cnf,
};

#[derive(Debug, Default)]
/// Representation of an instance of the [Intel
/// SAT](https://github.com/alexander-nadel/intel_sat_solver) solver.
pub struct IntelSat {
	store: IpasirStore<IntelSat, 1, 1, 0>,
}

impl AccessIpasirStore for IntelSat {
	type Store = IpasirStore<IntelSat, 1, 1, 0>;

	fn ipasir_store(&self) -> &Self::Store {
		&self.store
	}
	fn ipasir_store_mut(&mut self) -> &mut Self::Store {
		&mut self.store
	}
}

impl From<&Cnf> for IntelSat {
	fn from(value: &Cnf) -> Self {
		let mut slv: Self = Default::default();
		*slv.ipasir_store_mut().vars_mut() = value.nvar;
		for cl in value.iter() {
			// Ignore early detected unsatisfiability
			let _ = slv.add_clause(cl.iter().copied());
		}
		slv
	}
}

impl IpasirAssumptionMethods for IntelSat {
	const IPASIR_ASSUME: unsafe extern "C" fn(slv: *mut c_void, lit: i32) = intel_sat_assume;
	const IPASIR_FAILED: unsafe extern "C" fn(slv: *mut c_void, lit: i32) -> c_int =
		intel_sat_failed;
}

impl IpasirLearnCallbackMethod for IntelSat {
	const IPASIR_SET_LEARN_CALLBACK: unsafe extern "C" fn(
		*mut c_void,
		*mut c_void,
		c_int,
		Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	) = intel_sat_set_learn;
}

impl IpasirSolverMethods for IntelSat {
	const IPASIR_ADD: unsafe extern "C" fn(slv: *mut c_void, lit_or_zero: i32) = intel_sat_add;
	const IPASIR_INIT: unsafe extern "C" fn() -> *mut c_void = intel_sat_init;
	const IPASIR_RELEASE: unsafe extern "C" fn(slv: *mut c_void) = intel_sat_release;
	const IPASIR_SOLVE: unsafe extern "C" fn(slv: *mut c_void) -> c_int = intel_sat_solve;
	const IPASIR_VAL: unsafe extern "C" fn(slv: *mut c_void, lit: i32) -> i32 = intel_sat_val;
}

impl IpasirTermCallbackMethod for IntelSat {
	const IPASIR_SET_TERMINATE_CALLBACK: unsafe extern "C" fn(
		*mut c_void,
		*mut c_void,
		Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	) = intel_sat_set_terminate;
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		solver::{intel_sat::IntelSat, SolveResult, Solver},
		ClauseDatabaseTools, Encoder, Valuation,
	};

	#[test]
	fn solve() {
		let mut slv = IntelSat::default();

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
