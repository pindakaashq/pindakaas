use crate::{
	int::required_lits, linear::PosCoeff, trace::emit_clause, CheckError, Checker, ClauseDatabase,
	Coefficient, Encoder, LinExp, Literal, Result, Unsatisfiable,
};
use itertools::Itertools;
use std::collections::HashSet;

pub(crate) fn is_sorted<T: Ord>(xs: &[T]) -> bool {
	xs.windows(2).all(|x| x[0] <= x[1])
}

/// Given coefficients are powers of two multiplied by some value (1*c, 2*c, 4*c, 8*c, ..)
pub(crate) fn is_powers_of_two<C: Coefficient>(coefs: &[C]) -> bool {
	let mult = coefs[0];
	coefs
		.iter()
		.enumerate()
		.all(|(i, c)| c == &(num::pow(C::from(2).unwrap(), i) * mult))
}

/// Two's complement encoding range: -(2^(bits-1))..2^(bits-1)-1
pub(crate) fn two_comp_bounds<C: Coefficient>(bits: usize) -> (C, C) {
	let ub = C::one().shl(bits - 1); // value of most significant (sign) bit
	(
		-ub,           // just sign bit (1000..)
		ub - C::one(), // all except sign bits = most significant bit (10000..) - 1 = 01111..
	)
}

/// 2^bits - 1
pub(crate) fn unsigned_binary_range_ub<C: Coefficient>(bits: usize) -> Option<C> {
	num::checked_pow(C::from(2).unwrap(), bits).map(|c| c - C::one())
}

/// Convert `k` to unsigned binary in `bits`
pub(crate) fn as_binary<C: Coefficient>(k: PosCoeff<C>, bits: Option<usize>) -> Vec<bool> {
	let bits = bits.unwrap_or_else(|| required_lits(C::zero(), *k));
	// let range_ub = unsigned_binary_range_ub(bits).unwrap();
	// assert!(
	// 	*k <= range_ub,
	// 	"{} cannot be represented in {bits} bits, which can represent only up to {range_ub}",
	// 	*k,
	// );
	(0..bits)
		.map(|b| *k & (C::one() << b) != C::zero())
		.collect::<Vec<_>>()
}

const FILTER_TRIVIAL_CLAUSES: bool = false;
/// Adds clauses for a DNF formula (disjunction of conjunctions)
/// Ex. (a /\ -b) \/ c == a \/ c /\ -b \/ c
/// If any disjunction is empty, this satisfies the whole formula. If any element contains the empty conjunction, that element is falsified in the final clause.
pub(crate) fn add_clauses_for<DB: ClauseDatabase>(
	db: &mut DB,
	expression: Vec<Vec<Vec<DB::Lit>>>,
) -> Result {
	// TODO doctor out type of expression (clauses containing conjunctions?)

	for cls in expression.into_iter().multi_cartesian_product() {
		let cls = cls.concat(); // filter out [] (empty conjunctions?) of the clause
		if FILTER_TRIVIAL_CLAUSES {
			let mut lits = HashSet::<DB::Lit>::with_capacity(cls.len());
			if cls.iter().any(|lit| {
				if lits.contains(&lit.negate()) {
					true
				} else {
					lits.insert(lit.clone());
					false
				}
			}) {
				continue;
			}
		}
		emit_clause!(db, &cls)?
	}
	Ok(())
}

/// Negates CNF (flipping between empty clause and formula)
pub(crate) fn negate_cnf<Lit: Literal>(clauses: Vec<Vec<Lit>>) -> Vec<Vec<Lit>> {
	if clauses.is_empty() {
		vec![vec![]]
	} else if clauses.contains(&vec![]) {
		vec![]
	} else {
		assert!(clauses.len() == 1);
		clauses
			.into_iter()
			.map(|clause| clause.into_iter().map(|lit| lit.negate()).collect())
			.collect()
	}
}

/// Encode the constraint lits[0] ⊕ ... ⊕ lits[n].
/// # Warning
/// Currently only defined for n ≤ 3.
#[derive(Default)]
pub struct XorEncoder {}

impl<'a, DB: ClauseDatabase> Encoder<DB, XorConstraint<'a, DB::Lit>> for XorEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "xor_encoder", skip_all, fields(
			constraint = itertools::join(xor.lits.iter().map(crate::trace::trace_print_lit), " ⊻ ")
		))
	)]
	fn encode(&mut self, db: &mut DB, xor: &XorConstraint<DB::Lit>) -> Result {
		match xor.lits {
			[a] => emit_clause!(db, &[a.clone()]),
			[a, b] => {
				emit_clause!(db, &[a.clone(), b.clone()])?;
				emit_clause!(db, &[a.negate(), b.negate()])
			}
			[a, b, c] => {
				emit_clause!(db, &[a.clone(), b.clone(), c.clone()])?;
				emit_clause!(db, &[a.clone(), b.negate(), c.negate()])?;
				emit_clause!(db, &[a.negate(), b.clone(), c.negate()])?;
				emit_clause!(db, &[a.negate(), b.negate(), c.clone()])
			}
			_ => panic!("Unexpected usage of XOR with zero or more than three arguments"),
		}
	}
}

pub struct XorConstraint<'a, Lit: Literal> {
	pub(crate) lits: &'a [Lit],
}

impl<'a, Lit: Literal> XorConstraint<'a, Lit> {
	pub fn new(lits: &'a [Lit]) -> Self {
		Self { lits }
	}
}

impl<'a, Lit: Literal> Checker for XorConstraint<'a, Lit> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let count = LinExp::from_terms(
			self.lits
				.iter()
				.map(|l| (l.clone(), 1))
				.collect::<Vec<(Self::Lit, i32)>>()
				.as_slice(),
		)
		.assign(solution)?;
		if count % 2 == 1 {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

#[cfg(test)]
pub mod tests {
	type Lit = i32; // TODO replace all i32s for Lit

	use rand::distributions::Alphanumeric;
	use rand::{thread_rng, Rng};
	use splr::solver::SolverResult;
	use splr::{
		types::{CNFDescription, Instantiate},
		Certificate, Config, SatSolverIF, SolveIF, Solver, SolverError,
	};
	use std::{
		collections::{HashMap, HashSet},
		process::Command,
		thread::panicking,
	};
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{linear::LimitComp, CardinalityOne, Cnf, Encoder, LadderEncoder, Unsatisfiable};

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
			use $crate::Checker;
			$tdb = $tdb.with_check(|sol| $arg.check(sol).is_ok());
			$enc.encode(&mut $tdb, $arg)
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
		};
		($tdb:ident, $enc:expr, $max:expr, $arg:expr) => {
			use $crate::Checker;
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
			assert!(!$solns.is_empty(), "cannot using `assert_enc_sol!` with an empty solution set, use `assert_unsat!` or `assert_trivial_unsat!` instead.");
			$tdb = $tdb.expect_solutions($solns);
			$enc.encode(&mut $tdb, $($args),+)
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
			assert!(!$solns.is_empty(), "cannot using `assert_enc_sol!` with an empty solution set, use `assert_unsat!` or `assert_trivial_unsat!` instead.");
			$tdb = $tdb.expect_clauses($clauses);
			$tdb = $tdb.expect_solutions($solns);
			$enc.encode(&mut $tdb, ($($args),+))
				.expect("Encoding proved to be trivially unsatisfiable");
			$tdb.check_complete()
		};
	}
	pub(crate) use assert_enc_sol;

	macro_rules! assert_unsat {
		($enc:expr, $max:expr, $($args:expr),+) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
			assert_unsat!(tdb => $enc, $($args),+)
		};
		($tdb:ident => $enc:expr, $($args:expr),+) => {
			if ! $enc.encode(&mut $tdb, ($($args),+)).is_err() {
				$tdb = $tdb.expect_solutions(vec![]);
				$tdb.check_complete();
			}
		};
	}
	pub(crate) use assert_unsat;

	macro_rules! assert_trivial_unsat {
		($enc:expr, $max:expr, $($args:expr),+) => {
			let mut tdb = $crate::helpers::tests::TestDB::new($max);
			assert_trivial_unsat!(tdb => $enc, $($args),+)
		};
		($tdb:ident => $enc:expr, $($args:expr),+) => {
			assert_eq!($enc.encode(&mut $tdb, ($($args),+)), Err($crate::Unsatisfiable))
		};
		($res:expr) => {
			assert_eq!($res, Err($crate::Unsatisfiable))
		}
	}
	pub(crate) use assert_trivial_unsat;

	#[test]
	fn test_assert_macros() {
		#[derive(Default)]
		struct Negate {}
		impl Negate {
			#[cfg_attr(
				feature = "trace",
				tracing::instrument(name = "negate_encoder", skip_all)
			)]
			fn encode<'a, DB: ClauseDatabase>(&mut self, db: &mut DB, lit: &DB::Lit) -> Result {
				emit_clause!(db, &[lit.negate()])
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
			&XorConstraint::new(&[1,2]) =>
			vec![vec![1, 2], vec![-1, -2]],
			vec![vec![-1, 2], vec![1, -2]]
		);
	}

	#[test]
	fn test_expect_statistics() {
		let mut tdb = TestDB::new(3);
		tdb = tdb.expect_vars(2);
		tdb = tdb.expect_cls(3);
		tdb = tdb.expect_lits(5);
		tdb.add_clause(&[1, 2]).unwrap();
		tdb.new_var();
		tdb.add_clause(&[-3, -4]).unwrap();
		tdb.new_var();
		tdb.add_clause(&[5]).unwrap();
		tdb.check_complete();
	}

	const OUTPUT_SPLR: bool = false;
	/// The maximum number of variable to generate expected solutions for
	const GENERATE_EXPECTED_SOLUTIONS: i32 = 0;

	pub(crate) struct TestDB {
		slv: Solver,
		/// Number of variables available when solver is created
		pub(crate) num_var: i32,
		/// Clauses expected by the test case
		clauses: Option<Vec<(bool, Vec<i32>)>>,
		/// Solutions expected by the test case
		solutions: Option<Vec<Vec<i32>>>,
		check: Option<fn(&[i32]) -> bool>,
		unchecked: bool,
		cnf: Cnf<Lit>,
		expected_vars: Option<usize>,
		expected_cls: Option<usize>,
		expected_lits: Option<usize>,
		expecting_no_unit_clauses: bool,
		expecting_no_equivalences: Option<HashMap<Lit, Lit>>,
	}

	const ONLY_OUTPUT: bool = true;

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
				cnf: Cnf::new(num_var),
				clauses: None,
				solutions: None,
				check: None,
				unchecked: false,
				expected_vars: None,
				expected_cls: None,
				expected_lits: None,
				expecting_no_unit_clauses: false,
				expecting_no_equivalences: None,
			}
		}

		pub fn expect_clauses(mut self, mut clauses: Vec<Vec<i32>>) -> TestDB {
			for cl in &mut clauses {
				cl.sort_by_key(|a| a.abs());
			}
			clauses.sort();
			self.clauses = Some(clauses.into_iter().map(|cl| (false, cl)).collect());
			self.unchecked = true;
			self
		}

		pub fn expect_vars(mut self, vars: usize) -> TestDB {
			self.expected_vars = Some(vars);
			self
		}

		pub fn expect_cls(mut self, cls: usize) -> TestDB {
			self.expected_cls = Some(cls);
			self
		}

		pub fn expect_lits(mut self, lits: usize) -> TestDB {
			self.expected_lits = Some(lits);
			self
		}

		pub fn expect_solutions(mut self, mut solutions: Vec<Vec<i32>>) -> TestDB {
			for sol in &mut solutions {
				sol.sort_by_key(|a| a.abs());
			}
			solutions.sort();
			if let Some(self_solutions) = &self.solutions {
				assert_eq!(self_solutions, &solutions, "Previous (probably generated) solutions (left) differ from given solutions (right)" );
			}
			self.solutions = Some(solutions);
			self.unchecked = true;
			self
		}

		pub fn brute_force_solve(&self, check: impl Fn(&[i32]) -> bool, n: i32) -> Vec<Vec<i32>> {
			if n > 32 {
				unimplemented!(
					"Cannot generate solutions using binary shifts with more than 32 variables."
				);
			}

			(0..((2_i32).pow(n as u32)))
				.map(|i| {
					(0..n)
						.map(|j| if ((i >> j) & 1) == 1 { j + 1 } else { -(j + 1) })
						.collect::<Vec<_>>()
				})
				.filter(|g| check(&g[..]))
				.collect()
		}

		pub fn _print_solutions(sols: &Vec<Vec<i32>>) -> String {
			format!(
				"vec![
{}
]",
				sols.iter()
					.map(|sol| format!(
						"\tvec![{}]",
						(*sol)
							.iter()
							.map(|lit| lit.to_string())
							.collect::<Vec<_>>()
							.join(", ")
					))
					.collect::<Vec<_>>()
					.join(",\n")
			)
			.to_string()
		}

		pub fn with_check(mut self, checker: fn(&[i32]) -> bool) -> TestDB {
			if self.solutions.is_none() && self.num_var <= GENERATE_EXPECTED_SOLUTIONS {
				let solutions = self.brute_force_solve(checker, self.num_var);
				self.expect_solutions(solutions)
			} else {
				self.check = Some(checker);
				self.unchecked = true;
				self
			}
		}

		pub fn cadical(&mut self) -> SolverResult {
			let mut status: Option<SolverResult> = None;

			let dimacs = {
				let rng = thread_rng();
				let dimacs = format!(
					"./tmp/{}.dimacs",
					rng.sample_iter(&Alphanumeric)
						.take(7)
						.map(char::from)
						.collect::<String>()
				);
				std::fs::write(&dimacs, format!("{}", self.cnf)).unwrap();
				dimacs
			};

			let output = Command::new(format!("../../../cadical/build/cadical"))
				.arg(dimacs)
				.arg("-t")
				.arg("10")
				.output()
				.unwrap();

			let out = String::from_utf8(output.stdout.clone()).unwrap();
			let err = String::from_utf8(output.stderr.clone()).unwrap();
			if output.status.code().unwrap_or(-1) == -1 {
				panic!("CADICAL {}\n{}\n", out, err);
			}

			for line in String::from_utf8(output.stdout.clone()).unwrap().lines() {
				let mut tokens = line.split_whitespace();
				match tokens.next() {
					None | Some("c") => {
						if let Some("UNKNOWN") = tokens.next() {
							panic!("CADICAL unknown!")
						} else {
							continue;
						}
					}
					Some("s") => match tokens.next() {
						Some("SATISFIABLE") => {
							status = Some(SolverResult::Ok(Certificate::SAT(vec![])))
						}
						Some("UNSATISFIABLE") => {
							status = Some(SolverResult::Ok(Certificate::UNSAT))
						}
						Some("UNKNOWN") | Some("INDETERMINATE") => panic!("CADICAL unknown"),
						status => panic!("CADICAL Unknown status: {status:?}"),
					},
					Some("v") => {
						tokens
							.flat_map(|t| t.parse::<Lit>())
							.filter(|t| {
								let var = t.abs();
								0 < var && t.abs() <= self.num_var
							})
							.for_each(|lit| {
								if let Some(SolverResult::Ok(Certificate::SAT(solution))) =
									&mut status
								{
									solution.push(lit);
								} else {
									panic!("CADICAL ERR")
								}
							});
					}
					line => panic!("CADICAL Unexpected slv output: {:?}", line),
				}
			}
			status.unwrap_or_else(|| {
				panic!(
					"CADICAL No status set in SAT output:\n{}",
					String::from_utf8(output.stdout).unwrap()
				)
			})
		}

		fn call_solver(&mut self) -> SolverResult {
			const USE_SPLR: bool = false;
			if USE_SPLR {
				self.slv.solve()
			} else {
				self.cadical()
			}
		}

		pub fn solve(&mut self) -> Vec<Vec<i32>> {
			let mut from_slv: Vec<Vec<i32>> = Vec::new();

			while let Ok(Certificate::SAT(model)) = self.call_solver() {
				let solution = if ONLY_OUTPUT {
					model
						.clone()
						.into_iter()
						.filter(|l| l.abs() <= self.num_var)
						.collect()
				} else {
					model
				};

				from_slv.push(solution.clone());

				let nogood: Vec<i32> = solution.iter().map(|l| -l).collect();
				self.cnf.add_clause(&nogood).unwrap();
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
				sol.sort_by_key(|a| a.abs());
			}
			from_slv
		}

		pub fn check_complete(&mut self) {
			self.unchecked = false;
			if let Some(clauses) = &self.clauses {
				let missing: Vec<Vec<i32>> = clauses
					.iter()
					.filter(|exp| !exp.0)
					.map(|exp| exp.1.clone())
					.collect();
				assert!(
					missing.is_empty(),
					"clauses are missing from the encoding: {:?}",
					missing
				);
			}
			if self.solutions.is_none()
				&& self.check.is_none()
				&& self.expected_vars.is_none()
				&& self.expected_cls.is_none()
				&& self.expected_lits.is_none()
			{
				return;
			}
			if OUTPUT_SPLR {
				eprintln!("let result: Vec<Vec<i32>> = slv.iter().collect();");
			}

			let mut from_slv = self.solve();

			if let Some(check) = &self.check {
				for sol in &mut from_slv {
					assert!(check(sol), "solution {:?} failed check", sol)
				}
			}
			if let Some(solutions) = &self.solutions {
				// solutions only contain principal variables; so we might have to filter from_slv if it contains aux vars
				from_slv.sort();

				let from_slv_output = if ONLY_OUTPUT {
					from_slv.clone()
				} else {
					from_slv
						.iter()
						.map(|sol| {
							sol.iter()
								.filter(|l| l.abs() <= self.num_var)
								.cloned()
								.collect::<Vec<_>>()
						})
						.collect()
				};

				let misses = solutions
					.iter()
					.filter(|s| !from_slv_output.contains(s))
					.collect::<Vec<_>>();

				if !misses.is_empty() {
					println!("Missing solutions ({})", misses.len());
					for s in misses {
						println!("  -{s:?}");
					}
				}

				let extras = from_slv
					.iter()
					.zip(from_slv_output)
					.filter_map(|(sol, out)| (!solutions.contains(&out)).then_some(sol))
					.collect::<Vec<_>>();

				if !extras.is_empty() {
					println!("Extra solutions ({})", extras.len());
					for s in extras {
						println!("  +{s:?}");
					}
				}

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
			assert!(
				(self.expected_vars.is_none() || self.expected_vars.unwrap() == 0)
					&& (self.expected_cls.is_none() || self.expected_cls.unwrap() == 0)
					&& (self.expected_lits.is_none() || self.expected_lits.unwrap() == 0),
				"Missing {} var(s), {} clause(s) and {} literal(s)",
				self.expected_vars.unwrap_or(0),
				self.expected_cls.unwrap_or(0),
				self.expected_lits.unwrap_or(0)
			);
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
			self.cnf.add_clause(cl)?;
			let mut cl = Vec::from(cl);

			cl.sort_by_key(|a| a.abs());
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

			if self.expecting_no_unit_clauses {
				assert!(
					cl.len() > 1 || cl[0] <= self.num_var,
					"Unexpected unit clause on aux var {:?}",
					cl
				);
			}

			if let Some(equivalences) = &mut self.expecting_no_equivalences {
				let mut cl = cl.clone();
				cl.sort_by_key(|l| l.abs());
				if match cl[..] {
					[a, b] => {
						if !a.is_negated() && !b.is_negated() {
							let (a, b) = (a.var(), b.var());
							// a \/ b = ~a -> b
							equivalences.insert(a.negate(), b);
							// do we have b -> ~a = ~b \/ ~a = a -> ~b?
							equivalences.get(&a) == Some(&b.negate())
						} else if a.is_negated() && !b.is_negated() {
							let (a, b) = (a.var(), b.var());
							// ~a \/ b = a -> b
							equivalences.insert(a, b);
							// do we have b -> a = ~b \/ a = ~a -> ~b?
							equivalences.get(&a.negate()) == Some(&b.negate())
						} else if !a.is_negated() && b.is_negated() {
							let (a, b) = (a.var(), b.var());
							// a \/ ~b = ~a -> ~b
							equivalences.insert(a.negate(), b.negate());
							// do we have ~b -> ~a = b \/ ~a = a -> b?
							equivalences.get(&a) == Some(&b)
						} else if a.is_negated() && b.is_negated() {
							let (a, b) = (a.var(), b.var());
							// ~a \/ ~b = a -> ~b
							equivalences.insert(a.negate(), b.negate());
							// do we have ~b -> a = b \/ a = ~a -> b?
							equivalences.get(&a.negate()) == Some(&b)
						} else {
							unreachable!("{:?}", cl);
						}
					}
					_ => false,
				} {
					//panic!("Unexpected equivalence by adding {cl:?}");
					println!("Unexpected equivalence by adding {cl:?}");
				}
			}

			if let Some(num) = &mut self.expected_cls {
				assert!(*num > 0, "unexpected number of new clauses");
				*num -= 1;
			}
			if let Some(num) = &mut self.expected_lits {
				assert!(*num >= cl.len(), "unexpected number of new literals");
				*num -= cl.len();
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

			let res = match match cl.len() {
				0 => return Err(Unsatisfiable),
				1 => self.slv.add_assignment(cl[0]),
				_ => SatSolverIF::add_clause(&mut self.slv, cl),
			} {
				Ok(_) => {
					const FIND_UNSAT: bool = false;
					if FIND_UNSAT {
						if let SolverResult::Ok(Certificate::UNSAT) = self.call_solver() {
							return Err(Unsatisfiable);
						}
					}

					Ok(())
				}
				Err(err) => match err {
					SolverError::EmptyClause => Ok(()),
					SolverError::RootLevelConflict(_) => Err(Unsatisfiable),
					err => {
						panic!("unexpected solver error: {:?}", err);
					}
				},
			};

			res
		}

		fn new_var(&mut self) -> Self::Lit {
			let res = self.slv.add_var() as i32;
			self.cnf.new_var();

			if let Some(num) = &mut self.expected_vars {
				assert!(*num > 0, "unexpected number of new variables");
				*num -= 1;
			}

			if OUTPUT_SPLR {
				eprintln!("let x{} = slv.add_var() as i32;", res);
			}
			res
		}
	}
}
