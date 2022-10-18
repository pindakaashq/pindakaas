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
			tdb = tdb.expect_clauses($clauses);
			$enc.encode(&mut tdb, $arg)
				.expect("Encoding proved to be trivially unsatisfiable");
			tdb.check_complete()
		};
		($enc:expr, $max:expr, $($args:expr),+ => $clauses:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
			tdb = tdb.expect_clauses($clauses);
			$enc.encode(&mut tdb, ($($args),+))
				.expect("Encoding proved to be trivially unsatisfiable");
			tdb.check_complete()
		};
	}
	pub(crate) use assert_enc;

	macro_rules! assert_sol {
		($enc:expr, $max:expr, $arg:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
			tdb = tdb.with_check(|sol| $arg.check(sol).is_ok());
			$enc.encode(&mut tdb, $arg)
				.expect("Encoding proved to be trivially unsatisfiable");
			tdb.check_complete()
		};
		($enc:expr, $max:expr, $($args:expr),+ => $solns:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
			tdb = tdb.expect_solutions($solns);
			$enc.encode(&mut tdb, ($($args),+))
				.expect("Encoding proved to be trivially unsatisfiable");
			tdb.check_complete()
		};
	}
	pub(crate) use assert_sol;

	macro_rules! assert_enc_sol {
		($enc:expr, $max:expr, $arg:expr => $clauses:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
			tdb = tdb.expect_clauses($clauses);
			tdb = tdb.with_check(|sol| $arg.check(sol).is_ok());
			$enc.encode(&mut tdb, $arg)
				.expect("Encoding proved to be trivially unsatisfiable");
			tdb.check_complete()
		};
		($enc:expr, $max:expr, $($args:expr),+ => $clauses:expr, $solns:expr) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
			tdb = tdb.expect_clauses($clauses);
			tdb = tdb.expect_solutions($solns);
			$enc.encode(&mut tdb, ($($args),+))
				.expect("Encoding proved to be trivially unsatisfiable");
			tdb.check_complete()
		};
	}
	pub(crate) use assert_enc_sol;

	#[test]
	fn test_assert_macros() {
		#[derive(Default)]
		struct MakeFalse {}
		impl MakeFalse {
			fn encode<'a, DB: ClauseDatabase>(&mut self, db: &mut DB, lit: &DB::Lit) -> Result {
				db.add_clause(&[lit.negate()])
			}
		}

		// Test resulting encoding
		assert_enc!(MakeFalse::default(), 1, &1 => vec![vec![-1]]);
		// Test possible solutions (using specification)
		// TODO: num_var is really 1, but that crashes SPLR
		assert_sol!(MakeFalse::default(), 2, &1 => vec![vec![-1]]);
		// Test encoding and possible solutions
		// TODO: see above
		assert_enc_sol!(MakeFalse::default(), 2, &1 => vec![vec![-1]], vec![vec![-1]]);
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
			self.solutions = Some(solutions);
			self.unchecked = true;
			self
		}

		pub fn with_check(mut self, checker: fn(&[i32]) -> bool) -> TestDB {
			self.check = Some(checker);
			self.unchecked = true;
			self
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
				match self.slv.add_clause(nogood) {
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
					"solutions founds by the solver do not match expected set of solutions"
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
				_ => self.slv.add_clause(cl),
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
