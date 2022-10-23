use splr::SatSolverIF;

use crate::ClauseDatabase;

#[cfg(feature = "splr")]
impl ClauseDatabase for splr::Solver {
	type Lit = i32;

	fn new_var(&mut self) -> Self::Lit {
		self.add_var()
			.try_into()
			.expect("unable to convert splr variable into literal")
	}

	fn add_clause(&mut self, cl: &[Self::Lit]) -> crate::Result {
		use splr::SolverError::*;
		match SatSolverIF::add_clause(self, cl) {
			Ok(_) => Ok(()),
			Err(e) => match e {
				OutOfRange => panic!("clause referenced a non-existing variable"),
				RootLevelConflict(_) | EmptyClause | Inconsistent => Err(crate::Unsatisfiable),
				TimeOut => unreachable!(),
				SolverBug | UndescribedError | IOError | OutOfMemory => {
					panic!("an error occured in splr while adding a clause")
				}
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{linear::LimitComp, CardinalityOne, Encoder, PairwiseEncoder};

	/// TODO: This breaks things, but I think it should be solved in SPLR 0.17
	#[cfg(feature = "splr")]
	#[test]
	fn test_splr() {
		use splr::{Certificate, SolveIF};

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
		let res = slv.solve().unwrap();
		assert!(res == Certificate::SAT(vec![-a, b]) || res == Certificate::SAT(vec![-a, b]))
	}
}
