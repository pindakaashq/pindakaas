use std::{
	cmp::max,
	collections::HashSet,
	iter::FusedIterator,
	num::NonZeroI32,
	ops::{Bound, RangeBounds, RangeInclusive},
};

use itertools::Itertools;

use crate::{int::IntVar, linear::PosCoeff, ClauseDatabase, Coeff, Lit, Result, Var};

#[cfg(feature = "splr")]
macro_rules! maybe_std_concat {
	($e:literal) => {
		concat!($e)
	};
	($e:expr) => {
		$e
	};
}
#[cfg(feature = "splr")]
pub(crate) use maybe_std_concat;

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
pub(crate) use concat_slices;

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
#[cfg(feature = "splr")]
pub(crate) use const_concat;

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
#[cfg(not(any(feature = "tracing", test)))]
macro_rules! new_var {
	($db:expr) => {
		$crate::Lit::from($db.new_var())
	};
	($db:expr, $lbl:expr) => {
		$crate::Lit::from($db.new_var())
	};
}
pub(crate) use new_var;

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
#[cfg(not(any(feature = "tracing", test)))]
macro_rules! emit_clause {
	($db:expr, $cl:expr) => {
		$db.add_clause($cl)
	};
}
pub(crate) use emit_clause;

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
	(0_u32..bits).fold(0, |sum, i| sum + TWO.pow(i))
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

pub(crate) fn subscript_number(num: usize) -> impl Iterator<Item = char> {
	num.to_string()
		.chars()
		.map(|d| d.to_digit(10).unwrap())
		.map(|d| char::from_u32(0x2080 + d).unwrap())
		.collect_vec()
		.into_iter()
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
					let _ = lits.insert(*lit);
					false
				}
			}) {
				continue;
			}
		}
		emit_clause!(db, cls)?;
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

	/// Returns the lower bound of the variable range (inclusive).
	///
	/// Note: the value returned by this method is unspecified after the range
	/// has been iterated to exhaustion.
	pub fn start(&self) -> Var {
		self.start
	}

	/// Returns the upper bound of the variable range (inclusive).
	///
	/// Note: the value returned by this method is unspecified after the range
	/// has been iterated to exhaustion.
	pub fn end(&self) -> Var {
		self.end
	}

	/// Create an empty variable range
	pub fn empty() -> Self {
		Self {
			start: Var(NonZeroI32::new(2).unwrap()),
			end: Var(NonZeroI32::new(1).unwrap()),
		}
	}

	/// Returns `true` if the range contains no items.
	///
	/// # Examples
	///
	/// ```
	/// # use pindakaas::solver::VarRange;
	/// assert!(VarRange::empty().is_empty());
	/// ```
	pub fn is_empty(&self) -> bool {
		self.start > self.end
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

	pub fn iter_lits(&mut self) -> impl Iterator<Item = Lit> + '_ {
		self.map(Lit::from)
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
pub(crate) mod tests {
	use std::{fmt::Display, mem};

	use expect_test::ExpectFile;

	use super::*;
	use crate::{
		int::IntVarEnc,
		solver::{cadical::Cadical, SolveResult, Solver},
		Checker, Cnf, LinExp, Valuation,
	};

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
			.map(|x| LinExp::from(&x.into()))
			.collect_vec();
		let bool_vars = formula.get_variables();
		let mut solutions = Vec::new();
		let mut nogood: Vec<Lit> = Vec::new();
		while slv.solve(|value| {
			nogood = bool_vars
				.clone()
				.filter_map(|v| {
					let l = v.into();
					value.value(l).map(|b| if b { !l } else { l })
				})
				.collect();
			let sol: Vec<i64> = vars
				.clone()
				.into_iter()
				.map(|x| x.value(value).unwrap())
				.collect();
			solutions.push(sol);
		}) != SolveResult::Unsat
		{
			slv.add_clause(mem::take(&mut nogood)).unwrap();
		}
		solutions.sort();
		let sol_str = format!(
			"{}",
			solutions
				.into_iter()
				.map(|sol| sol.into_iter().format(" "))
				.format("\n")
		);
		expect.assert_eq(&sol_str);
	}

	/// Helper functions to ensure that the possible solutions of a formula, with
	/// relation to a set of variables, match the expected solutions string.
	pub(crate) fn assert_solutions<V, I>(formula: &Cnf, vars: I, expect: &ExpectFile)
	where
		V: Into<Lit>,
		I: IntoIterator<Item = V> + Clone,
	{
		let mut slv = Cadical::from(formula);
		let mut solutions = Vec::new();
		while slv.solve(|value| {
			let sol: Vec<Lit> = vars
				.clone()
				.into_iter()
				.filter_map(|v| {
					let l = v.into();
					value.value(l).map(|b| if b { l } else { !l })
				})
				.collect();
			solutions.push(sol);
		}) != SolveResult::Unsat
		{
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

	/// Helper functions to ensure that the possible solutions of a formula
	/// abide by the given checker.
	pub(crate) fn assert_checker(formula: &Cnf, checker: &impl Checker) {
		let mut slv = Cadical::from(formula);
		let vars = formula.get_variables();
		let mut sol = Vec::new();
		while slv.solve(|value| {
			assert_eq!(checker.check(value), Ok(()));
			sol = vars
				.clone()
				.filter_map(|v| {
					let l = v.into();
					value.value(l).map(|b| if b { l } else { !l })
				})
				.collect();
		}) != SolveResult::Unsat
		{
			slv.add_clause(sol.iter().map(|l| !l)).unwrap();
		}
	}

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
	#[cfg(test)]
	pub(crate) use expect_file;

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
				Some(solution[v - 1].into() == l)
			} else {
				None
			}
		}
	}
}
