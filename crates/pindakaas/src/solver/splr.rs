//! This module implements common Pindakaas [`Solver`] interfaces for the
//! [SPLR](https://github.com/shnarazk/splr) SAT solver.

use std::num::NonZeroI32;

use itertools::Itertools;
pub use splr::Solver as Splr;
use splr::{Certificate, SatSolverIF, SolveIF};

use crate::{
	solver::{SolveResult, Solver},
	ClauseDatabase, ClauseDatabaseTools, Cnf, Lit, Result, Valuation, Var, VarRange,
};

impl Valuation for Certificate {
	fn value(&self, lit: Lit) -> bool {
		if let Certificate::SAT(sol) = self {
			let var = lit.var();
			let v = Into::<i32>::into(var) as usize;
			if v <= sol.len() {
				debug_assert_eq!(sol[v - 1].abs(), lit.var().into());
				sol[v - 1] == lit.into()
			} else {
				false
			}
		} else {
			panic!("value called on an unsatisfiable certificate")
		}
	}
}

impl ClauseDatabase for Splr {
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
		use splr::SolverError::*;

		let cl: Vec<i32> = clause.iter().copied().map_into().collect();
		match SatSolverIF::add_clause(self, cl) {
			Ok(_) => Ok(()),
			Err(e) => match e {
				InvalidLiteral => panic!("clause referenced a non-existing variable"),
				RootLevelConflict(_) | EmptyClause | Inconsistent => Err(crate::Unsatisfiable),
				TimeOut => unreachable!(),
				SolverBug | UndescribedError | IOError | OutOfMemory => {
					panic!("an error occured in splr while adding a clause")
				}
			},
		}
	}

	fn new_var_range(&mut self, len: usize) -> VarRange {
		let mut new_var = || {
			let var = self.add_var();
			let var: i32 = var.try_into().expect("exhausted variable pool");
			Var(NonZeroI32::new(var).expect("variables cannot use the value zero"))
		};

		let start = new_var();
		let mut last = start;
		for _ in 1..len {
			let x = new_var();
			debug_assert_eq!(i32::from(last) + 1, i32::from(x));
			last = x;
		}
		VarRange::new(start, last)
	}
}

impl From<&Cnf> for Splr {
	fn from(cnf: &Cnf) -> Self {
		use splr::{
			types::{CNFDescription, Instantiate},
			Config,
		};
		let mut slv = Splr::instantiate(
			&Config::default(),
			&CNFDescription {
				num_of_variables: cnf.nvar.num_emitted_vars(),
				..CNFDescription::default()
			},
		);
		for cl in cnf.iter() {
			// Ignore early detected unsatisfiability
			let _ = ClauseDatabaseTools::add_clause(&mut slv, cl.iter().copied());
		}
		slv
	}
}

impl Solver for Splr {
	#[expect(
		refining_impl_trait,
		reason = "user can use more specific type if needed"
	)]
	fn solve(&mut self) -> SolveResult<Certificate, ()> {
		use splr::SolverError::*;

		match SolveIF::solve(self) {
			Ok(Certificate::UNSAT) => SolveResult::Unsatisfiable(()),
			Ok(cert @ Certificate::SAT(_)) => SolveResult::Satisfied(cert),
			Err(e) => match e {
				InvalidLiteral => panic!("clause referenced a non-existing variable"),
				Inconsistent => SolveResult::Unsatisfiable(()),
				RootLevelConflict(_) => SolveResult::Unsatisfiable(()),
				TimeOut | OutOfMemory => SolveResult::Unknown,
				_ => panic!("an error occurred within the splr solver"),
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	// use crate::{linear::LimitComp, solver::SolveResult, CardinalityOne, Encoder,
	// PairwiseEncoder};

	#[test]
	fn splr() {
		let mut _slv = splr::Solver::default();

		// TODO: Something weird is happening with the Variables
		// let a = slv.new_var().into();
		// let b = slv.new_var().into();
		// PairwiseEncoder::default()
		// 	.encode(
		// 		&mut slv,
		// 		&CardinalityOne {
		// 			lits: vec![a, b],
		// 			cmp: LimitComp::Equal,
		// 		},
		// 	)
		// 	.unwrap();
		// let SolveResult::Satisfied(solution) = slv.solve() else {
		// 	unreachable!()
		// };
		// assert!(
		// 	(solution.value(!a) && solution.value(b)) || (solution.value(a) &&
		// solution.value(!b)) );
	}
}
