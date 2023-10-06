use std::num::NonZeroI32;

use crate::{ClauseDatabase, Cnf, Lit, Result, Var};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarFactory {
	pub(crate) next_var: Option<Var>,
}

impl VarFactory {
	const MAX_VARS: usize = NonZeroI32::MAX.get() as usize;

	pub fn emited_vars(&self) -> usize {
		if let Some(x) = self.next_var {
			x.0.get() as usize - 1
		} else {
			Self::MAX_VARS
		}
	}
}

impl Default for VarFactory {
	fn default() -> Self {
		Self {
			next_var: Some(Var(NonZeroI32::new(1).unwrap())),
		}
	}
}

impl Iterator for VarFactory {
	type Item = Var;

	fn next(&mut self) -> Option<Self::Item> {
		let var = self.next_var;
		if let Some(var) = var {
			self.next_var = var.next_var();
		}
		var
	}
}

pub struct IpasirSolver {
	slv: ipasir::ffi::Solver,
	nvar: VarFactory,
}
impl ClauseDatabase for IpasirSolver {
	fn new_var(&mut self) -> Lit {
		self.nvar.next().expect("variable pool exhausted").into()
	}
	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> Result {
		use ipasir::IpasirSolver as SolverProtocol;
		self.slv.add_clause(cl);
		Ok(())
	}
}
impl From<&Cnf> for IpasirSolver {
	fn from(cnf: &Cnf) -> Self {
		use ipasir::IpasirSolver as SolverProtocol;
		let mut slv = Self::init();
		slv.nvar = cnf.nvar.clone();
		for cl in cnf.iter() {
			// Ignore result from add_clause (known to be Ok in this case)
			let _ = ClauseDatabase::add_clause(&mut slv, cl.iter().copied());
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
			nvar: VarFactory::default(),
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

impl From<Lit> for ipasir::Lit {
	fn from(_val: Lit) -> Self {
		todo!()
	}
}

#[cfg(feature = "splr")]
pub use splr::Solver as SplrSolver;
#[cfg(feature = "splr")]
impl ClauseDatabase for SplrSolver {
	fn new_var(&mut self) -> Lit {
		use splr::SatSolverIF;
		let var = self.add_var();
		let var: i32 = var.try_into().expect("exhausted variable pool");
		Lit(NonZeroI32::new(var).expect("variables cannot use the value zero"))
	}
	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> crate::Result {
		use splr::{SatSolverIF, SolverError::*};
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
#[cfg(feature = "splr")]
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
			let _ = slv.add_clause(cl.iter().copied());
		}
		slv
	}
}

#[cfg(test)]
mod tests {
	#[cfg(all(feature = "trace", feature = "splr"))]
	// TODO: currently marked as unused when splr feature is not enabled
	use traced_test::test;

	/// TODO: This breaks things, but I think it should be solved in SPLR 0.17
	#[cfg(feature = "splr")]
	#[test]
	fn test_splr() {
		use splr::{Certificate, SolveIF};

		use super::*;
		use crate::{linear::LimitComp, CardinalityOne, Encoder, PairwiseEncoder};

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
		assert!(res == Certificate::SAT(vec![!a, b]) || res == Certificate::SAT(vec![-a, b]))
	}
}
