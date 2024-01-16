use std::num::NonZeroI32;

pub use splr::Solver as Splr;
use splr::{Certificate, SatSolverIF, SolveIF, SolverError::*, VERSION};

use super::{SolveResult, Solver};
use crate::{helpers::const_concat, ClauseDatabase, Cnf, Lit};

impl ClauseDatabase for Splr {
	fn new_var(&mut self) -> Lit {
		let var = self.add_var();
		let var: i32 = var.try_into().expect("exhausted variable pool");
		Lit(NonZeroI32::new(var).expect("variables cannot use the value zero"))
	}
	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> crate::Result {
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
}

impl Solver for Splr {
	fn signature(&self) -> &str {
		const SPLR_SIG: &str = const_concat!("SPLR-", VERSION);
		SPLR_SIG
	}

	fn solve<SolCb: FnOnce(&dyn crate::Valuation)>(&mut self, on_sol: SolCb) -> SolveResult {
		match SolveIF::solve(self) {
			Ok(Certificate::UNSAT) => SolveResult::Unsat,
			Ok(Certificate::SAT(sol)) => {
				let value = |l: Lit| {
					let abs: Lit = l.var().into();
					let v = Into::<i32>::into(abs) as usize;
					if v <= sol.len() {
						debug_assert_eq!(sol[v - 1].abs(), l.var().into());
						Some(sol[v - 1] == l.into())
					} else {
						None
					}
				};
				on_sol(&value);
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

impl From<Cnf> for Splr {
	fn from(cnf: Cnf) -> Self {
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
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{linear::LimitComp, solver::SolveResult, CardinalityOne, Encoder, PairwiseEncoder};

	#[test]
	fn test_splr() {
		let mut slv = splr::Solver::default();
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
		let res = Solver::solve(&mut slv, |value| {
			assert!(
				(value(!a).unwrap() && value(b).unwrap())
					|| (value(a).unwrap() && value(!b).unwrap()),
			)
		});
		assert_eq!(res, SolveResult::Sat);
	}
}
