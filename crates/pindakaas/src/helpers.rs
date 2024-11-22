#[allow(unused_macros)]
#[cfg(feature = "splr")]
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

#[cfg(feature = "splr")]
macro_rules! const_concat {
	($($e:expr),+) => {{
			$crate::helpers::const_concat!(@impl $($crate::helpers::maybe_std_concat!($e)),+)
	}};

	(@impl $($e:expr),+) => {{
			$(
					const _: &str = $e;
			)*
			let slice: &[u8] = $crate::helpers::concat_slices!([u8]: $($e.as_bytes()),+);
			// SAFETY: the slice is constructed from string literals, so it is valid UTF-8
			unsafe { std::str::from_utf8_unchecked(slice) }
	}};
}

pub(crate) fn pow2(k: u32) -> Coeff {
	Coeff::from(2).pow(k)
}

// Copied from num library
pub const fn div_ceil(a: Coeff, b: Coeff) -> Coeff {
	let d = a / b;
	let r = a % b;
	if (r > 0 && b > 0) || (r < 0 && b < 0) {
		d + 1
	} else {
		d
	}
}

pub const fn div_floor(a: Coeff, b: Coeff) -> Coeff {
	let d = a / b;
	let r = a % b;
	if (r > 0 && b < 0) || (r < 0 && b > 0) {
		d - 1
	} else {
		d
	}
}

/// Given coefficients are powers of two multiplied by some value (1*c, 2*c, 4*c, 8*c, ..)
pub(crate) fn is_powers_of_two<I: IntoIterator<Item = Coeff>>(coefs: I) -> bool {
	let mut it = coefs.into_iter().enumerate();
	if let Some((_, mult)) = it.next() {
		it.all(|(i, c)| c == (mult << i))
	} else {
		false
	}
}

const FILTER_TRIVIAL_CLAUSES: bool = false;
/// Adds clauses for a DNF formula (disjunction of conjunctions)
/// Ex. (a /\ -b) \/ c == a \/ c /\ -b \/ c
/// If any disjunction is empty, this satisfies the whole formula. If any element contains the empty conjunction, that element is falsified in the final clause.
pub(crate) fn add_clauses_for<DB: ClauseDatabase>(
	db: &mut DB,
	expression: Vec<Vec<Vec<Lit>>>,
) -> Result {
	// TODO Move cnf: Vec<Vec<Lit>> functions into Cnf
	for cls in expression.into_iter().multi_cartesian_product() {
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

/// 2^bits - 1
pub(crate) fn unsigned_binary_range(bits: usize) -> (PosCoeff, PosCoeff) {
	(PosCoeff::new(0), PosCoeff::new(pow2(bits as u32) - 1))
}

/// Convert `k` to unsigned binary in `bits`
pub(crate) fn as_binary(k: PosCoeff, bits: Option<usize>) -> Vec<bool> {
	let bits = bits.unwrap_or_else(|| crate::int::required_lits(0, *k));
	assert!(
		k <= unsigned_binary_range(bits).1,
		"{k} cannot be represented in {bits} bits"
	);
	(0..bits).map(|b| *k & (1 << b) != 0).collect()
}
#[cfg(not(any(feature = "tracing", test)))]
macro_rules! emit_clause {
	($db:expr, $cl:expr) => {
		$db.add_clause($cl)
	};
}

/// Helper marco to emit a clause from within an encoder
#[cfg(any(feature = "tracing", test))]
macro_rules! emit_clause {
	($db:expr, $cl:expr) => {{
		let slice = $cl.into_iter().collect::<Vec<_>>();
		let res = $db.add_clause(slice.iter().copied());
		tracing::info!(clause = ?&slice, fail = matches!(res, Err($crate::Unsatisfiable)), "emit clause");
		res
	}};
}

#[cfg(feature = "splr")]
macro_rules! maybe_std_concat {
	($e:literal) => {
		concat!($e)
	};
	($e:expr) => {
		$e
	};
}
#[cfg(not(any(feature = "tracing", test)))]
macro_rules! new_var {
	($db:expr) => {
		$crate::Lit::from($db.new_var())
	};
	($db:expr, $lbl:expr) => {
		$crate::Lit::from($db.new_var())
	};
}

/// Helper marco to create a new variable within an Encoder
#[cfg(any(feature = "tracing", test))]
macro_rules! new_var {
	($db:expr) => {{
		let var = $db.new_var();
		tracing::info!(var = ?var, "new variable");
		$crate::Lit::from(var)
	}};
	($db:expr, $lbl:expr) => {{
		let var = $db.new_var();
		tracing::info!(var = ?var, label = $lbl, "new variable");
		$crate::Lit::from(var)
	}};
}

use std::collections::HashSet;

pub(crate) use emit_clause;
use itertools::Itertools;
pub(crate) use new_var;
#[cfg(feature = "splr")]
pub(crate) use {concat_slices, const_concat, maybe_std_concat};

use crate::{bool_linear::PosCoeff, int::enc::LitOrConst, ClauseDatabase, Coeff, Lit, Result};

pub(crate) fn emit_filtered_clause<DB: ClauseDatabase, I: IntoIterator<Item = LitOrConst>>(
	db: &mut DB,
	lits: I,
) -> Result {
	if let Ok(clause) = lits
		.into_iter()
		.filter_map(|lit| match lit {
			LitOrConst::Lit(lit) => Some(Ok(lit)),
			LitOrConst::Const(true) => Some(Err(())), // clause satisfied
			LitOrConst::Const(false) => None,         // literal falsified
		})
		.collect::<std::result::Result<Vec<_>, ()>>()
	{
		emit_clause!(db, clause)
	} else {
		Ok(())
	}
}

/// Negates CNF (flipping between empty clause and formula)
pub(crate) fn negate_cnf(clauses: Vec<Vec<Lit>>) -> Vec<Vec<Lit>> {
	if clauses.is_empty() {
		vec![vec![]]
	} else if clauses.contains(&vec![]) {
		vec![]
	} else if clauses.len() == 1 {
		clauses
			.into_iter()
			.map(|clause| clause.into_iter().map(|lit| !lit).collect())
			.collect()
	} else if clauses.iter().all(|c| c.len() == 1) {
		vec![clauses
			.into_iter()
			.flat_map(|clause| clause.into_iter().map(|lit| !lit))
			.collect()]
	} else {
		unimplemented!("Negating CNF {clauses:?} leads to complex expression")
	}
}

pub(crate) fn subscript_number(num: usize) -> impl Iterator<Item = char> {
	num.to_string()
		.chars()
		.map(|d| d.to_digit(10).unwrap())
		.map(|d| char::from_u32(0x2080 + d).unwrap())
		.collect_vec()
		.into_iter()
}

pub(crate) fn unsigned_binary_range_ub(bits: usize) -> Coeff {
	const TWO: Coeff = 2;
	(0..bits).fold(0, |sum, i| sum + TWO.pow(i as u32))
}

#[cfg(test)]
pub(crate) mod tests {
	#[cfg(test)]
	macro_rules! expect_file {
		($rel_path:expr) => {
			expect_test::expect_file!(format!(
				"{}/corpus/{}",
				env!("CARGO_MANIFEST_DIR"),
				$rel_path
			))
		};
	}

	use std::fmt::Display;

	#[cfg(test)]
	pub(crate) use expect_file;

	use expect_test::ExpectFile;
	use itertools::Itertools;

	use crate::{
		bool_linear::BoolLinExp,
		int::enc::IntVarEnc,
		solver::{cadical::Cadical, SolveResult, Solver},
		Checker, ClauseDatabase, Cnf, Lit, Valuation,
	};

	/// Helper functions to ensure that the possible solutions of a formula
	/// abide by the given checker.
	pub(crate) fn assert_checker(formula: &Cnf, checker: &impl Checker) {
		let mut slv = Cadical::from(formula);
		let vars = formula.get_variables();
		while let SolveResult::Satisfied(value) = slv.solve() {
			assert_eq!(checker.check(&value), Ok(()));
			let no_good: Vec<Lit> = vars
				.clone()
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			slv.add_clause(no_good).unwrap();
		}
	}

	/// Simple helper function to assert the generated formula against an expect
	/// block.
	pub(crate) fn assert_encoding(formula: &impl Display, expect: &ExpectFile) {
		expect.assert_eq(&formula.to_string());
	}

	#[allow(dead_code, reason = "TODO: prepare for checking integer encodings")]
	/// Helper function that asserts that the integer solutions of a formula are
	/// as contained in the expect block.
	pub(crate) fn assert_integer_solutions<V, I>(formula: &Cnf, vars: I, expect: &ExpectFile)
	where
		V: Into<IntVarEnc>,
		I: IntoIterator<Item = V> + Clone,
	{
		let mut slv = Cadical::from(formula);
		let vars = vars
			.into_iter()
			.map(|x| BoolLinExp::from(&x.into()))
			.collect_vec();
		let bool_vars = formula.get_variables();
		let mut solutions: Vec<Vec<i64>> = Vec::new();
		// while let SolveResult::Satisfied(value) = slv.solve() {
		// 	// Collect integer solution
		// 	solutions.push(
		// 		vars.clone()
		// 			.into_iter()
		// 			.map(|x| x.value(&value).unwrap())
		// 			.collect(),
		// 	);
		// 	// Add nogood clause
		// 	let nogood: Vec<Lit> = bool_vars
		// 		.clone()
		// 		.map(|v| {
		// 			let l = v.into();
		// 			if value.value(l) {
		// 				!l
		// 			} else {
		// 				l
		// 			}
		// 		})
		// 		.collect();
		// 	slv.add_clause(nogood).unwrap();
	}

	/// Helper functions to ensure that the possible solutions of a formula, with
	/// relation to a set of variables, match the expected solutions string.
	pub(crate) fn assert_solutions<V, I>(formula: &Cnf, vars: I, expect: &ExpectFile)
	where
		V: Into<Lit>,
		I: IntoIterator<Item = V> + Clone,
	{
		let mut slv = Cadical::from(formula);
		let mut solutions: Vec<Vec<Lit>> = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			solutions.push(
				vars.clone()
					.into_iter()
					.map(|v| {
						let l = v.into();
						if value.value(l) {
							l
						} else {
							!l
						}
					})
					.collect(),
			);
			slv.add_clause(solutions.last().unwrap().iter().map(|l| !l))
				.unwrap();
		}
		solutions.sort();
		let sol_str = format!(
			"{}",
			solutions
				.into_iter()
				.map(|sol| sol.into_iter().map(i32::from).format(" "))
				.format("\n")
		);
		expect.assert_eq(&sol_str);
	}

	/// Helper function to quickly create a valuation from a slice of literals.
	///
	/// ### Warning
	/// This function assumes that the literal slice contains all literals
	/// starting from the first variable, and that the literals are in order of
	/// the variables.
	pub(crate) fn make_valuation<L: Into<Lit> + Copy>(solution: &[L]) -> impl Valuation + '_ {
		|l: Lit| {
			let abs: Lit = l.var().into();
			let v = Into::<i32>::into(abs) as usize;
			if v <= solution.len() {
				debug_assert_eq!(solution[v - 1].into().var(), l.var());
				solution[v - 1].into() == l
			} else {
				false
			}
		}
	}
}
