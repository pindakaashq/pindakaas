use itertools::Itertools;
use num::{One, Zero};
use std::{ffi::c_int, ops::AddAssign};

use crate::{ClauseDatabase, Cnf, Literal};
pub struct IpasirSolver {
	slv: ipasir::ffi::Solver,
	last_var: Option<ipasir::Var>,
}
impl ClauseDatabase for IpasirSolver {
	type Lit = c_int; // FIXME: Should be ipasir::Lit, but that does not implement Hash
	fn new_var(&mut self) -> Self::Lit {
		match self.last_var {
			None => {
				self.last_var = Some(ipasir::Lit::try_from(1).unwrap().var());
				1
			}
			Some(x) => {
				let new_var = x.to_raw() + 1;
				self.last_var = Some(ipasir::Lit::try_from(new_var).unwrap().var());
				new_var
			}
		}
	}
	fn add_clause(&mut self, cl: &[Self::Lit]) -> crate::Result {
		use ipasir::IpasirSolver as SolverProtocol;
		self.slv.add_clause(
			cl.iter()
				.map(|lit| ipasir::Lit::try_from(*lit).unwrap())
				.collect_vec(),
		);
		Ok(())
	}
}
impl<Lit: Literal + Zero + One + AddAssign + Into<c_int>> From<Cnf<Lit>> for IpasirSolver {
	fn from(cnf: Cnf<Lit>) -> Self {
		use ipasir::IpasirSolver as SolverProtocol;
		let mut slv = IpasirSolver {
			slv: ipasir::ffi::Solver::init(),
			last_var: Some(
				ipasir::Lit::try_from(cnf.last_var.clone().into())
					.unwrap()
					.var(),
			),
		};
		for cl in cnf.iter() {
			slv.slv.add_clause(
				cl.iter()
					.map(|lit| {
						let lit: c_int = lit.clone().into();
						ipasir::Lit::try_from(lit).unwrap()
					})
					.collect_vec(),
			)
		}
		slv
	}
}
impl ipasir::IpasirSolver for IpasirSolver {
	fn signature(&self) -> &'static str {
		self.slv.signature()
	}
	fn init() -> Self {
		IpasirSolver {
			slv: ipasir::ffi::Solver::init(),
			last_var: None,
		}
	}
	fn add_clause<I: IntoIterator<Item = L>, L: Into<ipasir::Lit>>(&mut self, lits: I) {
		self.slv.add_clause(lits)
	}
	fn assume(&mut self, lit: ipasir::Lit) {
		self.slv.assume(lit)
	}
	fn solve(&mut self) -> ipasir::Result<ipasir::SolveResponse> {
		self.slv.solve()
	}
	fn val(&mut self, lit: ipasir::Lit) -> ipasir::Result<ipasir::LitValue> {
		self.slv.val(lit)
	}
	fn failed(&mut self, lit: ipasir::Lit) -> ipasir::Result<bool> {
		self.slv.failed(lit)
	}
	fn set_terminate<F: FnMut() -> ipasir::SolveControl + 'static>(&mut self, callback: F) {
		self.slv.set_terminate(callback)
	}
	fn set_learn<F: FnMut(ipasir::Clause) + 'static>(&mut self, max_len: usize, callback: F) {
		self.slv.set_learn(max_len, callback)
	}
}

#[cfg(feature = "minisat")]
pub use minisat::Solver as MiniSatSolver;
#[cfg(feature = "minisat")]
impl Literal for minisat::Lit {
	fn negate(&self) -> Self {
		!(*self)
	}
	fn is_negated(&self) -> bool {
		minisat::Lit::var(*self).1
	}
}
#[cfg(feature = "minisat")]
impl ClauseDatabase for MiniSatSolver {
	type Lit = minisat::Lit;
	fn new_var(&mut self) -> Self::Lit {
		self.new_lit()
	}
	fn add_clause(&mut self, cl: &[Self::Lit]) -> crate::Result {
		self.add_clause(cl.iter().cloned());
		Ok(())
	}
}
#[cfg(feature = "minisat")]
impl<Lit: Literal + Zero + One + Into<i32>> From<Cnf<Lit>> for MiniSatSolver {
	fn from(cnf: Cnf<Lit>) -> Self {
		let mut slv = minisat::Solver::new();
		let mut map = rustc_hash::FxHashMap::default();
		for cl in cnf.iter() {
			let cl = cl
				.iter()
				.map(|lit| {
					let ival: i32 = lit.clone().into();
					*map.entry(ival).or_insert_with(|| slv.new_var())
				})
				.collect_vec();
			slv.add_clause(cl)
		}
		slv
	}
}

#[cfg(feature = "splr")]
pub use splr::Solver as SplrSolver;
#[cfg(feature = "splr")]
impl ClauseDatabase for SplrSolver {
	type Lit = i32;
	fn new_var(&mut self) -> Self::Lit {
		use splr::SatSolverIF;
		self.add_var()
			.try_into()
			.expect("unable to convert splr variable into literal")
	}
	fn add_clause(&mut self, cl: &[Self::Lit]) -> crate::Result {
		use splr::{SatSolverIF, SolverError::*};
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
#[cfg(feature = "splr")]
impl<Lit: Literal + Zero + One + Into<i32>> From<Cnf<Lit>> for SplrSolver {
	fn from(cnf: Cnf<Lit>) -> Self {
		use splr::{
			types::{CNFDescription, Instantiate},
			Config,
		};
		let mut slv = SplrSolver::instantiate(
			&Config::default(),
			&CNFDescription {
				num_of_variables: cnf.last_var.clone().into() as usize,
				..CNFDescription::default()
			},
		);
		for cl in cnf.iter() {
			if slv
				.add_clause(&cl.iter().map(|lit| lit.clone().into()).collect_vec())
				.is_err()
			{
				// Ignore early detected unsatisfiability
			};
		}
		slv
	}
}

#[cfg(test)]
mod tests {
	/// TODO: This breaks things, but I think it should be solved in SPLR 0.17
	#[cfg(feature = "splr")]
	#[test]
	fn test_splr() {
		use super::*;
		use crate::{linear::LimitComp, CardinalityOne, Encoder, PairwiseEncoder};
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
