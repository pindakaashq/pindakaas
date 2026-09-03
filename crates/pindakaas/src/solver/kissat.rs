//! This module contains the pindakaas interface to the
//! [Kissat](https://github.com/arminbiere/kissat) SAT solver.

use std::ffi::{c_int, c_void};

use pindakaas_kissat::{
	kissat_add, kissat_init, kissat_release, kissat_set_terminate, kissat_solve, kissat_value,
};

use crate::{
	solver::{
		ipasir::{
			var_factory_next_var, var_factory_next_var_range, AccessIpasirStore,
			IpasirLiteralMethods, IpasirSolverMethods, IpasirStore, IpasirTermCallbackMethod,
		},
		VarFactory,
	},
	ClauseDatabaseTools, Cnf,
};

#[derive(Debug, Default)]
/// Representation of an instance of the
/// [Kissat](https://github.com/arminbiere/kissat) SAT solver.
pub struct Kissat {
	store: IpasirStore<Self, VarFactory, 0, 1, 0>,
}

impl AccessIpasirStore for Kissat {
	type Store = IpasirStore<Self, VarFactory, 0, 1, 0>;

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
		slv.store.store.vars = value.nvar;
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

impl IpasirLiteralMethods for Kissat {
	const IPASIR_NEW_RANGE: fn(slv: *mut c_void, vars: *mut c_void, len: usize) -> [i32; 2] =
		var_factory_next_var_range;
	const IPASIR_NEW_VAR: fn(slv: *mut c_void, vars: *mut c_void) -> i32 = var_factory_next_var;
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
		constraint::{
			linear::LimitComp,
			cardinality_one::{CardinalityOne, PairwiseEncoder},
		},
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
