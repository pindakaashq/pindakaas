use crate::{ClauseDatabase, Literal, Result};

/// Encode the constraint lits[0] ⊕ ... ⊕ lits[n].
/// # Warning
/// Currently only defined for n ≤ 3.
#[derive(Default)]
pub struct XorEncoder {}

impl XorEncoder {
	pub fn encode<DB: ClauseDatabase>(&mut self, db: &mut DB, lits: &[DB::Lit]) -> Result {
		match lits {
			[a] => db.add_clause(&[a.clone()]),
			[a, b] => {
				db.add_clause(&[a.clone(), b.clone()])?;
				db.add_clause(&[a.negate(), b.negate()])
			}
			[a, b, c] => {
				db.add_clause(&[a.clone(), b.clone(), c.clone()])?;
				db.add_clause(&[a.clone(), b.negate(), c.negate()])?;
				db.add_clause(&[a.negate(), b.clone(), c.negate()])?;
				db.add_clause(&[a.negate(), b.negate(), c.clone()])
			}
			_ => panic!("Unexpected usage of XOR with more that three arguments"),
		}
	}
}

// TODO to be incorporated with labels feature
#[cfg(debug_assertions)]
#[macro_export]
macro_rules! new_var {
	($db:expr) => {
		$db.new_var()
	};
	($db:expr, $lbl:expr) => {
		// $db.new_var_with_label($lbl)
		$db.new_var()
	};
}

#[cfg(not(debug_assertions))]
#[macro_export]
macro_rules! new_var {
	($db:expr) => {
		$db.new_var()
	};
	($db:expr, $lbl:expr) => {
		// $db.new_var_with_label($lbl)
		$db.new_var()
	};
}

#[cfg(test)]
pub mod tests {
	use super::*;
	use crate::Unsatisfiable;

	use crate::{linear::LimitComp, CardinalityOne, Checker, Encoder, LadderEncoder};
	use splr::{
		types::{CNFDescription, Instantiate},
		Certificate, Config, SatSolverIF, SolveIF, Solver, SolverError,
	};
	use std::{
		collections::{HashMap, HashSet},
		thread::panicking,
	};

	macro_rules! assert_enc {
		($enc:expr, $max:expr, $arg:expr => $clauses:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
            assert_enc!(tdb => $enc, $arg => $clauses)
		};
		($tdb:ident => $enc:expr, $arg:expr => $clauses:expr) => {
			$tdb = $tdb.expect_clauses($clauses);
			$enc.encode(&mut $tdb, $arg)
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
		};
		($enc:expr, $max:expr, $($args:expr),+ => $clauses:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
            assert_enc!(tdb => $enc, $($args),+ => $clauses)
		};
		($tdb:ident => $enc:expr, $($args:expr),+ => $clauses:expr) => {
			$tdb = $tdb.expect_clauses($clauses);
			$enc.encode(&mut $tdb, ($($args),+))
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
		};
	}
	pub(crate) use assert_enc;

	macro_rules! assert_sol {
		($enc:expr, $max:expr, $arg:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
            assert_sol!(tdb => $enc, $arg)
		};
		($tdb:ident => $enc:expr, $arg:expr) => {
			$tdb = $tdb.with_check(|sol| $arg.check(sol).is_ok());
			$enc.encode(&mut $tdb, $arg)
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
		};
		($enc:expr, $max:expr, $($args:expr),+ => $solns:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
            assert_sol!(tdb => $enc, $($args),+ => $solns)
		};
		($tdb:ident => $enc:expr, $($args:expr),+ => $solns:expr) => {
			$tdb = $tdb.expect_solutions($solns);
			$enc.encode(&mut $tdb, ($($args),+))
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
        }
	}
	pub(crate) use assert_sol;

	macro_rules! assert_enc_sol {
		($enc:expr, $max:expr, $arg:expr => $clauses:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
            assert_enc_sol!(tdb => $enc, $arg => $clauses)
		};
		($tdb:ident => $enc:expr, $arg:expr => $clauses:expr) => {
			$tdb = $tdb.expect_clauses($clauses);
			$enc.encode(&mut $tdb, $arg)
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
		};
		($enc:expr, $max:expr, $($args:expr),+ => $clauses:expr, $solns:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
            assert_enc_sol!(tdb => $enc, $($args),+ => $clauses, $solns)
		};
        ($tdb:ident => $enc:expr, $($args:expr),+ => $clauses:expr, $solns:expr) => {
			$tdb = $tdb.expect_clauses($clauses);
			$tdb = $tdb.expect_solutions($solns);
			$enc.encode(&mut $tdb, ($($args),+))
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
		};
	}
	pub(crate) use assert_enc_sol;

	#[test]
	fn test_assert_macros() {
		#[derive(Default)]
		struct Negate {}
		impl Negate {
			fn encode<'a, DB: ClauseDatabase>(&mut self, db: &mut DB, lit: &DB::Lit) -> Result {
				db.add_clause(&[lit.negate()])
			}
		}

		// Test resulting encoding
		assert_enc!(Negate::default(), 1, &1 => vec![vec![-1]]);
		// Test possible solutions (using specification)
		assert_sol!(Negate::default(), 1, &1 => vec![vec![-1]]);
		// Test encoding and possible solutions
		assert_enc_sol!(Negate::default(), 1, &1 => vec![vec![-1]], vec![vec![-1]]);

		// Test resulting encoding for given TestDB instance
		let mut tdb = TestDB::new(2);
		tdb.add_clause(&[2]).unwrap();
		assert_enc!(tdb => Negate::default(), &1 => vec![vec![-1]]); // only clauses of encoder are checked against

		let mut tdb = TestDB::new(2);
		tdb.add_clause(&[2]).unwrap();
		assert_sol!(tdb => Negate::default(), &1 => vec![vec![-1,2]]);

		let mut tdb = TestDB::new(2);
		tdb.add_clause(&[2]).unwrap();
		assert_enc_sol!(tdb => Negate::default(), &1 => vec![vec![-1]], vec![vec![-1,2]]);
	}

	#[test]
	fn test_assert_macros_with_check() {
		let mut tdb = TestDB::new(3);
		tdb.add_clause(&[1]).unwrap();
		assert_sol!(tdb => LadderEncoder::default(), &CardinalityOne {
			lits: vec![2, 3],
			cmp: LimitComp::LessEq,
		});
	}

	#[test]
	fn test_xor() {
		assert_enc_sol!(
			XorEncoder::default(),
			2,
			&[1, 2] =>
			vec![vec![1, 2], vec![-1, -2]],
			vec![vec![-1, 2], vec![1, -2]]
		);
	}

	const OUTPUT_SPLR: bool = false;
	/// The maximum number of variable to generate expected solutions for
	const GENERATE_EXPECTED_SOLUTIONS: i32 = 0;

	pub(crate) struct TestDB {
		slv: Solver,
		/// Number of variables available when solver is created
		num_var: i32,
		/// Clauses expected by the test case
		clauses: Option<Vec<(bool, Vec<i32>)>>,
		/// Solutions expected by the test case
		solutions: Option<Vec<Vec<i32>>>,
		check: Option<fn(&[i32]) -> bool>,
		unchecked: bool,
		labels: HashMap<i32, String>,
	}

	impl TestDB {
		pub fn new(num_var: i32) -> TestDB {
			if OUTPUT_SPLR {
				eprintln!("let slv = Solver::instantiate( &Config::default(), &CNFDescription {{ num_of_variables: {} as usize, ..CNFDescription::default() }});", num_var);
			}
			TestDB {
				slv: Solver::instantiate(
					&Config::default(),
					&CNFDescription {
						num_of_variables: num_var as usize,
						..CNFDescription::default()
					},
				),
				num_var,
				clauses: None,
				solutions: None,
				check: None,
				unchecked: false,
				labels: HashMap::new(),
			}
		}

		pub fn expect_clauses(mut self, mut clauses: Vec<Vec<i32>>) -> TestDB {
			for cl in &mut clauses {
				cl.sort_by(|a, b| a.abs().cmp(&b.abs()));
			}
			clauses.sort();
			self.clauses = Some(clauses.into_iter().map(|cl| (false, cl)).collect());
			self.unchecked = true;
			self
		}

		pub fn expect_solutions(mut self, mut solutions: Vec<Vec<i32>>) -> TestDB {
			for sol in &mut solutions {
				sol.sort_by(|a, b| a.abs().cmp(&b.abs()));
			}
			solutions.sort();
			if let Some(self_solutions) = &self.solutions {
				assert_eq!(self_solutions, &solutions, "Previous (probably generated) solutions (left) differ from given solutions (right)" );
			}
			self.solutions = Some(solutions);
			self.unchecked = true;
			self
		}

		fn generate_solutions(&self, check: fn(&[i32]) -> bool) -> Vec<Vec<i32>> {
			let n = self.num_var;
			if n > 32 {
				unimplemented!(
					"Cannot generate solutions using binary shifts with more than 32 variables."
				);
			}
			let solutions = (0..((2_i32).pow(n as u32)))
				.map(|i| {
					(0..n)
						.map(|j| if ((i >> j) & 1) == 1 { j + 1 } else { -(j + 1) })
						.collect::<Vec<_>>()
				})
				.filter(|g| check(&g[..]))
				.collect();
			eprintln!("!vec[");
			for sol in &solutions {
				eprintln!("  !vec{sol:?},");
			}
			eprintln!("],");

			solutions
		}

		pub fn with_check(mut self, checker: fn(&[i32]) -> bool) -> TestDB {
			if self.solutions.is_none() && self.num_var <= GENERATE_EXPECTED_SOLUTIONS {
				let solutions = self.generate_solutions(checker);
				self.expect_solutions(solutions)
			} else {
				self.check = Some(checker);
				self.unchecked = true;
				self
			}
		}

		pub fn check_complete(&mut self) {
			self.unchecked = false;
			if let Some(clauses) = &self.clauses {
				let missing: Vec<Vec<i32>> = clauses
					.iter()
					.filter(|exp| exp.0 == false)
					.map(|exp| exp.1.clone())
					.collect();
				// assert!(false, "{:?} {:?}", clauses, missing);
				assert!(
					missing.is_empty(),
					"clauses are missing from the encoding: {:?}",
					missing
				);
			}
			if self.solutions.is_none() && self.check.is_none() {
				return;
			}
			if OUTPUT_SPLR {
				eprintln!("let result: Vec<Vec<i32>> = slv.iter().collect();");
			}
			let mut from_slv: Vec<Vec<i32>> = Vec::new();
			while let Ok(Certificate::SAT(model)) = self.slv.solve() {
				from_slv.push(
					model
						.into_iter()
						.filter(|l| l.abs() <= self.num_var)
						.collect(),
				);
				let nogood: Vec<i32> = from_slv.last().unwrap().iter().map(|l| -l).collect();
				match SatSolverIF::add_clause(&mut self.slv, nogood) {
					Err(SolverError::Inconsistent | SolverError::EmptyClause) => {
						break;
					}
					Err(e) => {
						panic!("unexpected solver error: {}", e);
					}
					Ok(_) => self.slv.reset(),
				}
			}
			for sol in &mut from_slv {
				sol.sort_by(|a, b| a.abs().cmp(&b.abs()));
			}
			if let Some(check) = &self.check {
				for sol in &mut from_slv {
					assert!(check(sol), "solution {:?} failed check", sol)
				}
			}
			if let Some(solutions) = &self.solutions {
				// we are only interested in literals present in the expected solutions (and not in auxiliary variables)
				let vars = HashSet::<i32>::from_iter(
					solutions
						.iter()
						.flat_map(|sol| sol.iter().map(|lit| lit.abs())),
				);

				let mut from_slv: Vec<Vec<i32>> = HashSet::<Vec<i32>>::from_iter(
					from_slv
						.into_iter()
						.map(|xs| xs.into_iter().filter(|x| vars.contains(&x.abs())).collect()),
				)
				.into_iter()
				.collect();
				from_slv.sort();

				assert_eq!(
					&from_slv, solutions,
					"solutions found by the solver do not match expected set of solutions"
				);
			}
		}
	}

	impl Drop for TestDB {
		fn drop(&mut self) {
			if self.unchecked && !panicking() {
				panic!("TestDB object was dropped without being checked!")
			}
		}
	}

	impl ClauseDatabase for TestDB {
		type Lit = i32;

		fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
			let mut cl = Vec::from(cl);

			#[cfg(debug_assertions)]
			{
				let lit_as_string = |lit: &Self::Lit| -> String {
					let polarity = if lit.is_positive() { "" } else { "-" };
					let var = lit.abs();
					format!(
						"{}{}, ",
						polarity,
						self.labels
							.get(&var)
							.unwrap_or(&format!("x_{}", var))
							.to_string()
					)
				};

				let out = cl.iter().map(lit_as_string).collect::<String>();
				println!("{}\t\t({:?})", out, cl);
			}

			cl.sort_by(|a, b| a.abs().cmp(&b.abs()));
			if let Some(clauses) = &mut self.clauses {
				let mut found = false;
				for exp in clauses {
					if cl == exp.1 {
						exp.0 = true;
						found = true;
						break;
					}
				}
				assert!(found, "unexpected clause: {:?}", cl);
			}

			if OUTPUT_SPLR {
				let list: Vec<String> = cl
					.iter()
					.map(|l| {
						if l.abs() <= self.num_var {
							l.to_string()
						} else {
							format!("{}x{}", if *l < 0 { "-" } else { "" }, l.abs())
						}
					})
					.collect();
				match cl.len() {
					0 => {}
					1 => {
						eprintln!(
						"slv.add_assignment({}).expect(\"unexpected error from add_assignment\");",
							list[0],
						)
					}
					_ => eprintln!(
						"slv.add_clause([{}]).expect(\"unexpected error from add_clause\");",
						list.join(", ")
					),
				}
			}

			match match cl.len() {
				0 => return Err(Unsatisfiable),
				1 => self.slv.add_assignment(cl[0]),
				_ => SatSolverIF::add_clause(&mut self.slv, cl),
			} {
				Ok(_) => Ok(()),
				Err(err) => match err {
					SolverError::EmptyClause => Ok(()),
					SolverError::RootLevelConflict(_) => Err(Unsatisfiable),
					err => {
						panic!("unexpected solver error: {:?}", err);
					}
				},
			}
		}

		fn new_var(&mut self) -> Self::Lit {
			let res = self.slv.add_var() as i32;
			if OUTPUT_SPLR {
				eprintln!("let x{} = slv.add_var() as i32;", res);
			}
			res
		}
	}
}
