use std::num::NonZeroI32;

pub use splr::Solver as SplrSolver;
use splr::{Certificate, SatSolverIF, SolveIF, SolverError::*, VERSION};

use super::{SolveResult, SolverAction};
use crate::{helpers::const_concat, ClauseDatabase, Cnf, Lit, Solver};

impl ClauseDatabase for SplrSolver {
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

impl Solver for SplrSolver {
	fn signature(&self) -> &str {
		const SPLR_SIG: &str = const_concat!("SPLR-", VERSION);
		SPLR_SIG
	}

	fn solve<SolCb: FnOnce(&dyn crate::Valuation), FailCb: FnOnce(&super::FailFn<'_>)>(
		&mut self,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult {
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
				RootLevelConflict((l, _)) => {
					let i: i32 = l.into();
					on_fail(&|x| i32::from(x.var()) == i.abs());
					SolveResult::Unsat
				}
				TimeOut | OutOfMemory => SolveResult::Unknown,
				_ => panic!("an error occurred within the splr solver"),
			},
		}
	}

	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&dyn crate::Valuation),
		FailCb: FnOnce(&super::FailFn<'_>),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult {
		let mut copy = self.clone();
		for l in assumptions {
			match copy.add_assignment(l.into()) {
				Ok(_) => {}
				Err(e) => match e {
					InvalidLiteral => panic!("clause referenced a non-existing variable"),
					Inconsistent => {
						let fail = |x| l == x;
						on_fail(&fail);
						return SolveResult::Unsat;
					}
					_ => unreachable!(),
				},
			}
		}
		Solver::solve(&mut copy, on_sol, on_fail)
	}

	fn set_terminate_callback<F: FnMut() -> SolverAction>(&mut self, _cb: Option<F>) {
		unimplemented!("SPLR does not support setting a callback that is checked to determine whether to terminate termination")
	}

	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>)>(
		&mut self,
		_max_len: usize,
		_cb: Option<F>,
	) {
		unimplemented!(
			"SPLR does not support setting a callback that is called when learning a new clause"
		)
	}
}

impl From<Cnf> for SplrSolver {
	fn from(cnf: Cnf) -> Self {
		use splr::{
			types::{CNFDescription, Instantiate},
			Config,
		};
		let mut slv = SplrSolver::instantiate(
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
		let res = Solver::solve(
			&mut slv,
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
