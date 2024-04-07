use std::{
	cmp::max,
	collections::HashSet,
	iter::FusedIterator,
	num::NonZeroI32,
	ops::{Bound, RangeBounds, RangeInclusive},
};

use itertools::Itertools;

use crate::{
	int::IntVar, linear::PosCoeff, trace::emit_clause, CheckError, Checker, ClauseDatabase, Coeff,
	Encoder, LinExp, Lit, Result, Unsatisfiable, Valuation, Var,
};

#[allow(unused_macros)]
macro_rules! maybe_std_concat {
	($e:literal) => {
		concat!($e)
	};
	($e:expr) => {
		$e
	};
}
#[allow(unused_imports)]
pub(crate) use maybe_std_concat;

#[allow(unused_macros)]
macro_rules! concat_slices {
    ([$init:expr; $T:ty]: $($s:expr),+ $(,)?) => {{
        $(
            const _: &[$T] = $s; // require constants
        )*
        const LEN: usize = $( $s.len() + )* 0;
        const ARR: [$T; LEN] = {
            let mut arr: [$T; LEN] = [$init; LEN];
            let mut base: usize = 0;
            $({
                let mut i = 0;
                while i < $s.len() {
                    arr[base + i] = $s[i];
                    i += 1;
                }
                base += $s.len();
            })*
            if base != LEN { panic!("invalid length"); }
            arr
        };
        &ARR
    }};

    ([$T:ty]: $($s:expr),+ $(,)?) => {
        $crate::helpers::concat_slices!([0; $T]: $($s),+)
    };
}
#[allow(unused_imports)]
pub(crate) use concat_slices;

#[allow(unused_macros)]
macro_rules! const_concat {
	() => { "" };

	($($e:expr),+) => {{
			$crate::helpers::const_concat!(@impl $($crate::helpers::maybe_std_concat!($e)),+)
	}};

	(@impl $($e:expr),+) => {{
			$(
					const _: &str = $e;
			)*
			let slice: &[u8] = $crate::helpers::concat_slices!([u8]: $($e.as_bytes()),+);
			unsafe { std::str::from_utf8_unchecked(slice) }
	}};
}
#[allow(unused_imports)]
pub(crate) use const_concat;

/// Given coefficients are powers of two multiplied by some value (1*c, 2*c, 4*c, 8*c, ..)
pub(crate) fn is_powers_of_two<I: IntoIterator<Item = Coeff>>(coefs: I) -> bool {
	let mut it = coefs.into_iter().enumerate();
	if let Some((_, mult)) = it.next() {
		const TWO: Coeff = 2;
		it.all(|(i, c)| c == (TWO.pow(i as u32) * mult))
	} else {
		false
	}
}

pub(crate) fn unsigned_binary_range_ub(bits: u32) -> Coeff {
	const TWO: Coeff = 2;
	(0u32..bits).fold(0, |sum, i| sum + TWO.pow(i))
}
/// Convert `k` to unsigned binary in `bits`
pub(crate) fn as_binary(k: PosCoeff, bits: Option<u32>) -> Vec<bool> {
	let bits = bits.unwrap_or_else(|| IntVar::required_bits(0, *k));
	assert!(
		*k <= unsigned_binary_range_ub(bits),
		"{k} cannot be represented in {bits} bits"
	);
	(0..bits).map(|b| *k & (1 << b) != 0).collect()
}

const FILTER_TRIVIAL_CLAUSES: bool = false;
/// Adds clauses for a DNF formula (disjunction of conjunctions)
/// Ex. (a /\ -b) \/ c == a \/ c /\ -b \/ c
/// If any disjunction is empty, this satisfies the whole formula. If any element contains the empty conjunction, that element is falsified in the final clause.
pub(crate) fn add_clauses_for<DB: ClauseDatabase>(
	db: &mut DB,
	expression: Vec<Vec<Vec<Lit>>>,
) -> Result {
	// TODO doctor out type of expression (clauses containing conjunctions?)

	for cls in expression
		.into_iter()
		.map(|cls| cls.into_iter())
		.multi_cartesian_product()
	{
		let cls = cls.concat(); // filter out [] (empty conjunctions?) of the clause
		if FILTER_TRIVIAL_CLAUSES {
			let mut lits = HashSet::<Lit>::with_capacity(cls.len());
			if cls.iter().any(|lit| {
				if lits.contains(&(!lit)) {
					true
				} else {
					lits.insert(*lit);
					false
				}
			}) {
				continue;
			}
		}
		emit_clause!(db, cls)?
	}
	Ok(())
}

/// Negates CNF (flipping between empty clause and formula)
pub(crate) fn negate_cnf(clauses: Vec<Vec<Lit>>) -> Vec<Vec<Lit>> {
	if clauses.is_empty() {
		vec![vec![]]
	} else if clauses.contains(&vec![]) {
		vec![]
	} else {
		assert!(clauses.len() == 1);
		clauses
			.into_iter()
			.map(|clause| clause.into_iter().map(|lit| !lit).collect())
			.collect()
	}
}

/// Encode the constraint lits[0] ⊕ ... ⊕ lits[n].
/// # Warning
/// Currently only defined for n ≤ 3.
#[derive(Default)]
pub struct XorEncoder {}

impl<'a, DB: ClauseDatabase> Encoder<DB, XorConstraint<'a>> for XorEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "xor_encoder", skip_all, fields(
			constraint = itertools::join(xor.lits.iter().map(crate::trace::trace_print_lit), " ⊻ ")
		))
	)]
	fn encode(&self, db: &mut DB, xor: &XorConstraint) -> Result {
		match *xor.lits {
			[a] => emit_clause!(db, [a]),
			[a, b] => {
				emit_clause!(db, [a, b])?;
				emit_clause!(db, [!a, !b])
			}
			[a, b, c] => {
				emit_clause!(db, [a, b, c])?;
				emit_clause!(db, [a, !b, !c])?;
				emit_clause!(db, [!a, b, !c])?;
				emit_clause!(db, [!a, !b, c])
			}
			_ => panic!("Unexpected usage of XOR with zero or more than three arguments"),
		}
	}
}

pub struct XorConstraint<'a> {
	pub(crate) lits: &'a [Lit],
}

impl<'a> XorConstraint<'a> {
	pub fn new(lits: &'a [Lit]) -> Self {
		Self { lits }
	}
}

impl<'a> Checker for XorConstraint<'a> {
	fn check<F: Valuation>(&self, value: F) -> Result<(), CheckError> {
		let count = LinExp::from_terms(self.lits.iter().map(|&l| (l, 1)).collect_vec().as_slice())
			.value(value)?;
		if count % 2 == 1 {
			Ok(())
		} else {
			Err(Unsatisfiable.into())
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct VarRange {
	start: Var,
	end: Var,
}

impl VarRange {
	/// Create a range starting from [`start`] and ending at [`end`] (inclusive)
	pub fn new(start: Var, end: Var) -> Self {
		Self { start, end }
	}

	pub fn empty() -> Self {
		Self {
			start: Var(NonZeroI32::new(2).unwrap()),
			end: Var(NonZeroI32::new(1).unwrap()),
		}
	}

	/// Performs the indexing operation into the variable range
	pub fn index(&self, index: usize) -> Var {
		if index >= self.len() {
			panic!("out of bounds access");
		}
		if index == 0 {
			self.start
		} else {
			let index = NonZeroI32::new(index as i32).unwrap();
			self.start.checked_add(index).unwrap()
		}
	}

	/// Find the index of a variable within the range
	pub fn find(&self, var: Var) -> Option<usize> {
		if !self.contains(&var) {
			None
		} else {
			let offset = (var.0.get() - self.start.0.get()) as usize;
			debug_assert!(offset <= self.len());
			Some(offset)
		}
	}
}

impl Iterator for VarRange {
	type Item = Var;

	fn next(&mut self) -> Option<Self::Item> {
		if self.start <= self.end {
			let item = self.start;
			self.start = self.start.next_var().unwrap();
			Some(item)
		} else {
			None
		}
	}
	fn size_hint(&self) -> (usize, Option<usize>) {
		let size = max(self.end.0.get() - self.start.0.get() + 1, 0) as usize;
		(size, Some(size))
	}
	fn count(self) -> usize {
		let (lower, upper) = self.size_hint();
		debug_assert_eq!(upper, Some(lower));
		lower
	}
}
impl FusedIterator for VarRange {}
impl ExactSizeIterator for VarRange {
	fn len(&self) -> usize {
		let (lower, upper) = self.size_hint();
		debug_assert_eq!(upper, Some(lower));
		lower
	}
}
impl DoubleEndedIterator for VarRange {
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.start <= self.end {
			let item = self.end;
			if let Some(prev) = self.end.prev_var() {
				self.end = prev;
			} else {
				*self = VarRange::empty();
			}
			Some(item)
		} else {
			None
		}
	}
}
impl RangeBounds<Var> for VarRange {
	fn start_bound(&self) -> Bound<&Var> {
		Bound::Included(&self.start)
	}

	fn end_bound(&self) -> Bound<&Var> {
		Bound::Included(&self.end)
	}
}
impl From<RangeInclusive<Var>> for VarRange {
	fn from(value: RangeInclusive<Var>) -> Self {
		VarRange::new(*value.start(), *value.end())
	}
}

#[cfg(test)]
pub mod tests {
	use std::{
		collections::{HashMap, HashSet},
		num::NonZeroI32,
		thread::panicking,
	};

	use splr::{
		types::{CNFDescription, Instantiate},
		Certificate, Config, SatSolverIF, SolveIF, Solver, SolverError,
	};
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{linear::LimitComp, CardinalityOne, Encoder, LadderEncoder, Unsatisfiable, Var};

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

	macro_rules! lits {
		() => (
			std::vec::Vec::new()
		);
		($($x:expr),+ $(,)?) => (
			<[Lit]>::into_vec(
				std::boxed::Box::new([$($crate::Lit::from($x)),+])
			)
		);
	}
	pub(crate) use lits;
	#[test]
	fn test_assert_macros() {
		#[derive(Default)]
		struct Negate {}
		impl Negate {
			#[cfg_attr(
				feature = "trace",
				tracing::instrument(name = "negate_encoder", skip_all)
			)]
			fn encode<'a, DB: ClauseDatabase>(&mut self, db: &mut DB, lit: Lit) -> Result {
				emit_clause!(db, [!lit])
			}
		}

		// Test resulting encoding
		assert_enc!(Negate::default(), 1, 1.into() => vec![lits![-1]]);
		// Test possible solutions (using specification)
		assert_sol!(Negate::default(), 1, 1.into() => vec![lits![-1]]);
		// Test encoding and possible solutions
		assert_enc_sol!(Negate::default(), 1, 1.into() => vec![lits![-1]], vec![lits![-1]]);

		// Test resulting encoding for given TestDB instance
		let mut tdb = TestDB::new(2);
		tdb.add_clause(lits![2]).unwrap();
		assert_enc!(tdb => Negate::default(), 1.into() => vec![lits![-1]]); // only clauses of encoder are checked against

		let mut tdb = TestDB::new(2);
		tdb.add_clause(lits![2]).unwrap();
		assert_sol!(tdb => Negate::default(), 1.into() => vec![lits![-1,2]]);

		let mut tdb = TestDB::new(2);
		tdb.add_clause(lits![2]).unwrap();
		assert_enc_sol!(tdb => Negate::default(), 1.into() => vec![lits![-1]], vec![lits![-1,2]]);
	}

	#[test]
	fn test_assert_macros_with_check() {
		let mut tdb = TestDB::new(3);
		tdb.add_clause(lits![1]).unwrap();
		assert_sol!(tdb => LadderEncoder::default(), &CardinalityOne {
			lits: lits![2, 3],
			cmp: LimitComp::LessEq,
		});
	}

	#[test]
	fn test_xor() {
		assert_enc_sol!(
			XorEncoder::default(),
			2,
			&XorConstraint::new(&lits![1,2]) =>
			vec![lits![1, 2], lits![-1, -2]],
			vec![lits![-1, 2], lits![1, -2]]
		);
	}

	#[test]
	fn test_expect_statistics() {
		let mut tdb = TestDB::new(3);
		tdb = tdb.expect_vars(2);
		tdb = tdb.expect_cls(3);
		tdb = tdb.expect_lits(5);
		tdb.add_clause(lits![1, 2]).unwrap();
		tdb.new_var();
		tdb.add_clause(lits![-3, -4]).unwrap();
		tdb.new_var();
		tdb.add_clause(lits![5]).unwrap();
		tdb.check_complete();
	}

	pub(crate) fn make_valuation<L: Into<Lit> + Copy>(g: &[L]) -> impl Valuation + '_ {
		|l: Lit| {
			let abs: Lit = l.var().into();
			let v = Into::<i32>::into(abs) as usize;
			if v <= g.len() {
				debug_assert_eq!(g[v - 1].into().var(), l.var());
				Some(g[v - 1].into() == l)
			} else {
				None
			}
		}
	}

	const OUTPUT_SPLR: bool = false;
	/// The maximum number of variable to generate expected solutions for
	const GENERATE_EXPECTED_SOLUTIONS: i32 = 0;

	pub(crate) struct TestDB {
		slv: Solver,
		/// Number of variables available when solver is created
		pub(crate) num_var: i32,
		/// Clauses expected by the test case
		clauses: Option<Vec<(bool, Vec<Lit>)>>,
		/// Solutions expected by the test case
		solutions: Option<Vec<Vec<Lit>>>,
		check: Option<fn(&dyn Valuation) -> bool>,
		unchecked: bool,
		expected_vars: Option<usize>,
		expected_cls: Option<usize>,
		expected_lits: Option<usize>,
		expecting_no_unit_clauses: bool,
		expecting_no_equivalences: Option<HashMap<Lit, Lit>>,
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
				expected_vars: None,
				expected_cls: None,
				expected_lits: None,
				expecting_no_unit_clauses: false,
				expecting_no_equivalences: None,
			}
		}

		pub fn expect_clauses(mut self, mut clauses: Vec<Vec<Lit>>) -> TestDB {
			for cl in &mut clauses {
				cl.sort();
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

		pub fn expect_solutions(mut self, mut solutions: Vec<Vec<Lit>>) -> TestDB {
			for sol in &mut solutions {
				sol.sort();
			}
			solutions.sort();
			if let Some(self_solutions) = &self.solutions {
				assert_eq!(self_solutions, &solutions, "Previous (probably generated) solutions (left) differ from given solutions (right)" );
			}
			self.solutions = Some(solutions);
			self.unchecked = true;
			self
		}

		#[allow(dead_code)]
		pub fn generate_solutions(
			&self,
			check: impl Fn(&dyn Valuation) -> bool,
			n: i32,
		) -> Vec<Vec<Lit>> {
			if n > 32 {
				unimplemented!(
					"Cannot generate solutions using binary shifts with more than 32 variables."
				);
			}

			(0..((2_i32).pow(n as u32)))
				.map(|i| {
					(0..n)
						.map(|j| if ((i >> j) & 1) == 1 { j + 1 } else { -(j + 1) }.into())
						.collect_vec()
				})
				.filter(|g| check(&make_valuation(g)))
				.collect()
		}

		pub fn _print_solutions(sols: &[Vec<Lit>]) -> String {
			format!(
				"vec![\n{}\n]",
				sols.iter()
					.map(|sol| format!(
						"\tvec![{}]",
						(*sol)
							.iter()
							.map(|&lit| Into::<i32>::into(lit).to_string())
							.join(", ")
					))
					.join(",\n")
			)
		}

		pub fn with_check(mut self, checker: fn(&dyn Valuation) -> bool) -> TestDB {
			if self.solutions.is_none() && self.num_var <= GENERATE_EXPECTED_SOLUTIONS {
				let solutions = self.generate_solutions(checker, self.num_var);
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
				let missing: Vec<Vec<Lit>> = clauses
					.iter()
					.filter_map(|(found, cl)| if *found { None } else { Some(cl.clone()) })
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
			const ONLY_OUTPUT: bool = true;
			let mut from_slv: Vec<Vec<Lit>> = Vec::new();
			while let Ok(Certificate::SAT(model)) = self.slv.solve() {
				let solution: Vec<Lit> = if ONLY_OUTPUT {
					model
						.iter()
						.filter(|l| l.abs() <= self.num_var)
						.map(|&l| l.into())
						.collect()
				} else {
					model.iter().map(|&l| l.into()).collect()
				};

				from_slv.push(solution.clone());

				let nogood: Vec<i32> = solution.iter().map(|l| (!l).into()).collect();
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
				sol.sort();
			}
			if let Some(check) = &self.check {
				for sol in &mut from_slv {
					assert!(
						check(&make_valuation(sol)),
						"solution {:?} failed check",
						sol
					)
				}
			}
			if let Some(solutions) = &self.solutions {
				// we are only interested in literals present in the expected solutions (and not in auxiliary variables)
				from_slv.sort();

				let from_slv_output = if ONLY_OUTPUT {
					from_slv.clone()
				} else {
					from_slv
						.iter()
						.map(|sol| {
							sol.iter()
								.filter(|l| Into::<i32>::into(l.var()) <= self.num_var)
								.cloned()
								.collect_vec()
						})
						.collect()
				};

				let misses = solutions
					.iter()
					.filter(|s| !from_slv_output.contains(s))
					.collect_vec();

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
					.collect_vec();

				if !extras.is_empty() {
					println!("Extra solutions ({})", extras.len());
					for s in extras {
						println!("  +{s:?}");
					}
				}

				let vars: HashSet<Var> = solutions
					.iter()
					.flat_map(|sol| sol.iter().map(|lit| lit.var()))
					.collect();

				let mut from_slv: Vec<Vec<Lit>> = HashSet::<Vec<Lit>>::from_iter(
					from_slv
						.into_iter()
						.map(|xs| xs.into_iter().filter(|x| vars.contains(&x.var())).collect()),
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
		fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> Result {
			let cl = cl.into_iter().sorted().collect_vec();

			if let Some(clauses) = &mut self.clauses {
				let mut found = false;
				for (f, x) in clauses {
					if &cl == x {
						*f = true;
						found = true;
						break;
					}
				}
				assert!(found, "unexpected clause: {:?}", cl);
			}

			if self.expecting_no_unit_clauses {
				assert!(
					cl.len() > 1 || Into::<i32>::into(cl[0]) <= self.num_var,
					"Unexpected unit clause on aux var {:?}",
					cl
				);
			}

			if let Some(equivalences) = &mut self.expecting_no_equivalences {
				let mut cl = cl.clone();
				cl.sort();
				if match cl[..] {
					[a, b] => {
						let (a, b): (Lit, Lit) = (a.var().into(), b.var().into());
						if !a.is_negated() && !b.is_negated() {
							// a \/ b = ~a -> b
							equivalences.insert(!a, b);
							// do we have b -> ~a = ~b \/ ~a = a -> ~b?
							equivalences.get(&a) == Some(&!b)
						} else if a.is_negated() && !b.is_negated() {
							// ~a \/ b = a -> b
							equivalences.insert(a, b);
							// do we have b -> a = ~b \/ a = ~a -> ~b?
							equivalences.get(&!a) == Some(&!b)
						} else if !a.is_negated() && b.is_negated() {
							// a \/ ~b = ~a -> ~b
							equivalences.insert(!a, !b);
							// do we have ~b -> ~a = b \/ ~a = a -> b?
							equivalences.get(&a) == Some(&b)
						} else if a.is_negated() && b.is_negated() {
							// ~a \/ ~b = a -> ~b
							equivalences.insert(!a, !b);
							// do we have ~b -> a = b \/ a = ~a -> b?
							equivalences.get(&!a) == Some(&b)
						} else {
							unreachable!("{:?}", cl);
						}
					}
					_ => false,
				} {
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
						let v: i32 = l.var().into();
						if v <= self.num_var {
							l.to_string()
						} else {
							format!("{}x{}", if l.is_negated() { "-" } else { "" }, v)
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
				1 => self.slv.add_assignment(cl[0].into()),
				_ => SatSolverIF::add_clause(
					&mut self.slv,
					cl.iter().map(|&l| l.into()).collect_vec(),
				),
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

		fn new_var(&mut self) -> Var {
			let res = self.slv.add_var() as i32;

			if let Some(num) = &mut self.expected_vars {
				assert!(*num > 0, "unexpected number of new variables");
				*num -= 1;
			}

			if OUTPUT_SPLR {
				eprintln!("let x{} = slv.add_var() as i32;", res);
			}
			Var(NonZeroI32::new(res).unwrap())
		}
	}
}
