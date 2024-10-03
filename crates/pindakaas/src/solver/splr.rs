use std::num::NonZeroI32;

pub use splr::Solver as Splr;
use splr::{Certificate, SatSolverIF, SolveIF, VERSION};

use crate::{
	helpers::const_concat,
	solver::{SolveResult, Solver},
	ClauseDatabase, Cnf, ConditionalDatabase, Lit, Valuation, Var,
};

impl ClauseDatabase for Splr {
	fn new_var(&mut self) -> Var {
		let var = self.add_var();
		let var: i32 = var.try_into().expect("exhausted variable pool");
		Var(NonZeroI32::new(var).expect("variables cannot use the value zero"))
	}
	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> crate::Result {
		use splr::SolverError::*;

		let cl: Vec<_> = cl.into_iter().map(Into::<i32>::into).collect();
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

	type CondDB = Self;
	fn with_conditions(&mut self, conditions: Vec<Lit>) -> ConditionalDatabase<Self::CondDB> {
		ConditionalDatabase {
			db: self,
			conditions,
		}
	}
}

impl Solver for Splr {
	type ValueFn = Certificate;

	fn signature(&self) -> &str {
		const SPLR_SIG: &str = const_concat!("SPLR-", VERSION);
		SPLR_SIG
	}

	fn solve<SolCb: FnOnce(&Self::ValueFn)>(&mut self, on_sol: SolCb) -> SolveResult {
		use splr::SolverError::*;

		match SolveIF::solve(self) {
			Ok(Certificate::UNSAT) => SolveResult::Unsat,
			Ok(cert @ Certificate::SAT(_)) => {
				on_sol(&cert);
				SolveResult::Sat
			}
			Err(e) => match e {
				InvalidLiteral => panic!("clause referenced a non-existing variable"),
				Inconsistent => SolveResult::Unsat,
				RootLevelConflict(_) => SolveResult::Unsat,
				TimeOut | OutOfMemory => SolveResult::Unknown,
				_ => panic!("an error occurred within the splr solver"),
			},
		}
	}
}

impl Valuation for Certificate {
	fn value(&self, lit: Lit) -> Option<bool> {
		if let Certificate::SAT(sol) = self {
			let var = lit.var();
			let v = Into::<i32>::into(var) as usize;
			if v <= sol.len() {
				debug_assert_eq!(sol[v - 1].abs(), lit.var().into());
				Some(sol[v - 1] == lit.into())
			} else {
				None
			}
		} else {
			panic!("value called on an unsatisfiable certificate")
		}
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
				num_of_variables: cnf.nvar.emited_vars(),
				..CNFDescription::default()
			},
		);
		for cl in cnf.iter() {
			// Ignore early detected unsatisfiability
			let _ = ClauseDatabase::add_clause(&mut slv, cl.iter().copied());
		}
		slv
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	// use crate::{linear::LimitComp, solver::SolveResult, CardinalityOne, Encoder, PairwiseEncoder};

	#[test]
	fn test_splr() {
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
		// let res = Solver::solve(&mut slv, |value| {
		// 	assert!(
		// 		(value(!a).unwrap() && value(b).unwrap())
		// 			|| (value(a).unwrap() && value(!b).unwrap()),
		// 	)
		// });
		// assert_eq!(res, SolveResult::Sat);
	}
}
