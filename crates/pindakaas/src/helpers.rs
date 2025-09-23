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

pub(crate) mod opt_field;

use itertools::Itertools;
pub(crate) use new_named_lit;

use crate::{bool_linear::PosCoeff, integer::IntVar, ClauseDatabase, Coeff};

/// Convert `k` to unsigned binary in `bits`
pub(crate) fn as_binary(k: PosCoeff, bits: Option<u32>) -> Vec<bool> {
	let bits = bits.unwrap_or_else(|| IntVar::required_bits(0, *k));
	assert!(
		*k <= unsigned_binary_range_ub(bits),
		"{k} cannot be represented in {bits} bits"
	);
	(0..bits).map(|b| *k & (1 << b) != 0).collect()
}

/// Given coefficients are powers of two multiplied by some value (1*c, 2*c,
/// 4*c, 8*c, ..)
pub(crate) fn is_powers_of_two<I: IntoIterator<Item = Coeff>>(coefs: I) -> bool {
	let mut it = coefs.into_iter().enumerate();
	if let Some((_, mult)) = it.next() {
		const TWO: Coeff = 2;
		it.all(|(i, c)| c == (TWO.pow(i as u32) * mult))
	} else {
		false
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

	/// Helper functions to ensure that the possible solutions of a formula,
	/// with relation to a set of variables, match the expected solutions
	/// string.
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
