//! This module contains the pindakaas interface to the
//! [Kissat](https://github.com/arminbiere/kissat) SAT solver.

use std::ffi::{c_int, c_void};

use pindakaas_kissat::{
	kissat_add, kissat_init, kissat_release, kissat_set_terminate, kissat_solve, kissat_value,
};

use crate::{
	solver::ipasir::{
		AccessIpasirStore, BasicIpasirStorage, IpasirSolverMethods, IpasirStore,
		IpasirTermCallbackMethod,
	},
	ClauseDatabaseTools, Cnf, VarRange,
};

#[derive(Debug, Default)]
/// Representation of an instance of the
/// [Kissat](https://github.com/arminbiere/kissat) SAT solver.
pub struct Kissat {
	store: IpasirStore<Self, 0, 1, 0>,
}

impl Kissat {
	// TODO: Unsure whether this is a good idea.
	#[doc(hidden)]
	pub fn emitted_vars(&self) -> VarRange {
		self.ipasir_store().vars().emitted_vars()
	}
}

impl AccessIpasirStore for Kissat {
	type Store = IpasirStore<Self, 0, 1, 0>;

	fn ipasir_store(&self) -> &Self::Store {
		&self.store
	}
	fn ipasir_store_mut(&mut self) -> &mut Self::Store {
		&mut self.store
	}
}

impl From<&Cnf> for Kissat {
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

impl IpasirSolverMethods for Kissat {
	const IPASIR_ADD: unsafe extern "C" fn(*mut c_void, i32) = kissat_add;
	const IPASIR_INIT: unsafe extern "C" fn() -> *mut c_void = kissat_init;
	const IPASIR_RELEASE: unsafe extern "C" fn(*mut c_void) = kissat_release;
	const IPASIR_SOLVE: unsafe extern "C" fn(*mut c_void) -> c_int = kissat_solve;
	const IPASIR_VAL: unsafe extern "C" fn(*mut c_void, i32) -> c_int = kissat_value;
}

impl IpasirTermCallbackMethod for Kissat {
	const IPASIR_SET_TERMINATE_CALLBACK: unsafe extern "C" fn(
		*mut c_void,
		*mut c_void,
		Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	) = kissat_set_terminate;
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		solver::{kissat::Kissat, SolveResult, Solver},
		ClauseDatabaseTools, Encoder, Valuation,
	};

	#[test]
	fn solve() {
		let mut slv = Kissat::default();

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
