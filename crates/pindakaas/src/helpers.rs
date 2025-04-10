macro_rules! as_dyn_trait {
	($as_dyn_name:ident, $trait_name:ident) => {
		/// Helper trait that allows the creation of a dynamic reference to a trait
		/// object. This trait is automatically implemented for all sized types that
		/// implement the trait, and for the trait object itself.
		pub trait $as_dyn_name {
			/// Cast the object reference to a dynamic trait object reference.
			fn as_dyn(&self) -> &dyn $trait_name;
			/// Cast the object mutable reference to a mutable dynamic trait object
			/// reference.
			fn as_mut_dyn(&mut self) -> &mut dyn $trait_name;
		}
		impl<T: $trait_name> $as_dyn_name for T {
			fn as_dyn(&self) -> &dyn $trait_name {
				self
			}
			fn as_mut_dyn(&mut self) -> &mut dyn $trait_name {
				self
			}
		}
		impl $as_dyn_name for dyn $trait_name {
			fn as_dyn(&self) -> &dyn $trait_name {
				self
			}
			fn as_mut_dyn(&mut self) -> &mut dyn $trait_name {
				self
			}
		}
	};
}

as_dyn_trait!(AsDynClauseDatabase, ClauseDatabase);

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
/// Helper marco to create a new named literal within the library independent of
/// whether `tracing` is enabled.
macro_rules! new_named_lit {
	($db:expr, $lbl:expr) => {
		$crate::ClauseDatabaseTools::new_lit($db)
	};
}

#[cfg(any(feature = "tracing", test))]
/// Helper marco to create a new named literal within the library independent of
/// whether `tracing` is enabled.
macro_rules! new_named_lit {
	($db:expr, $lbl:expr) => {{
		$crate::ClauseDatabaseTools::new_named_lit($db, &$lbl)
	}};
}

use std::collections::HashSet;

use itertools::Itertools;
pub(crate) use new_named_lit;
#[cfg(feature = "splr")]
pub(crate) use {concat_slices, const_concat, maybe_std_concat};

use crate::{
	bool_linear::PosCoeff, integer::IntVar, ClauseDatabase, ClauseDatabaseTools, Coeff, Lit, Result,
};

const FILTER_TRIVIAL_CLAUSES: bool = false;

/// Adds clauses for a DNF formula (disjunction of conjunctions)
/// Ex. (a /\ -b) \/ c == a \/ c /\ -b \/ c
/// If any disjunction is empty, this satisfies the whole formula. If any element contains the empty conjunction, that element is falsified in the final clause.
pub(crate) fn add_clauses_for<DB: ClauseDatabase + ?Sized>(
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
			if cls.iter().any(|&lit| {
				if lits.contains(&(!lit)) {
					true
				} else {
					let _ = lits.insert(lit);
					false
				}
			}) {
				continue;
			}
		}
		db.add_clause(cls)?;
	}
	Ok(())
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

pub(crate) fn subscript_number(num: usize) -> impl Iterator<Item = char> {
	num.to_string()
		.chars()
		.map(|d| d.to_digit(10).unwrap())
		.map(|d| char::from_u32(0x2080 + d).unwrap())
		.collect_vec()
		.into_iter()
}

pub(crate) fn unsigned_binary_range_ub(bits: u32) -> Coeff {
	const TWO: Coeff = 2;
	(0_u32..bits).fold(0, |sum, i| sum + TWO.pow(i))
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
		integer::IntVarEnc,
		solver::{cadical::Cadical, SolveResult, Solver},
		Checker, ClauseDatabaseTools, Cnf, Lit, Unsatisfiable, Valuation,
	};

	/// Helper functions to ensure that the possible solutions of a formula
	/// abide by the given checker.
	pub(crate) fn assert_checker(formula: &Cnf, checker: &impl Checker) {
		let mut slv = Cadical::from(formula);
		let vars = formula.get_variables();
		while let SolveResult::Satisfied(value) = slv.solve() {
			assert_eq!(checker.check(&value), Ok(()));
			let no_good: Vec<Lit> = vars
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
		while let SolveResult::Satisfied(value) = slv.solve() {
			// Collect integer solution
			solutions.push(
				vars.clone()
					.into_iter()
					.map(|x| x.value(&value).unwrap())
					.collect(),
			);
			// Add nogood clause
			let nogood: Vec<Lit> = bool_vars
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			slv.add_clause(nogood).unwrap();
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
			if let Err(Unsatisfiable) =
				slv.add_clause(solutions.last().unwrap().iter().map(|&l| !l))
			{
				break;
			};
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
