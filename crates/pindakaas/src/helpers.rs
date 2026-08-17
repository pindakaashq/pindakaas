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
		impl $as_dyn_name for dyn $trait_name + '_ {
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
	($db:expr, $label:expr) => {
		$crate::ClauseDatabaseTools::new_lit($db)
	};
}

#[cfg(any(feature = "tracing", test))]
/// Helper marco to create a new named literal within the library independent of
/// whether `tracing` is enabled.
macro_rules! new_named_lit {
	($db:expr, $label:expr) => {{
		$crate::ClauseDatabaseTools::new_named_lit($db, &$label)
	}};
}

#[cfg(not(any(feature = "tracing", test)))]
/// Helper macro to create a consecutive range of Boolean variables, naming each
/// of them independently of whether `tracing` is enabled.
///
/// The name is produced by a closure over the index within the range, and is
/// not evaluated at all when `tracing` is disabled.
macro_rules! new_named_var_range {
	($db:expr, $len:expr, $name:expr) => {
		$crate::ClauseDatabase::new_var_range($db, $len)
	};
}

#[cfg(any(feature = "tracing", test))]
/// Helper macro to create a consecutive range of Boolean variables, naming each
/// of them independently of whether `tracing` is enabled.
///
/// The name is produced by a closure over the index within the range, and is
/// not evaluated at all when `tracing` is disabled.
macro_rules! new_named_var_range {
	($db:expr, $len:expr, $name:expr) => {{
		let range = $crate::ClauseDatabase::new_var_range($db, $len);
		// Naming is separate from allocation, so the variables can be handed
		// out in one block and still show up named in a trace.
		for (i, var) in range.enumerate() {
			tracing::info!(var = ?i32::from(var), label = ($name)(i), "new variable");
		}
		range
	}};
}

pub(crate) mod opt_field;
pub(crate) mod scm;

use itertools::Itertools;
pub(crate) use new_named_lit;
pub(crate) use new_named_var_range;

use crate::{
	bool_linear::PosCoeff, integer::BinaryEncoding, BoolVal, ClauseDatabase, Coeff, Valuation,
};

/// The value of a binary encoding under an assignment.
pub(crate) fn binary_value<F: Valuation + ?Sized>(x: &[BoolVal], value: &F) -> Coeff {
	x.iter()
		.enumerate()
		.filter(|(_, b)| match b {
			BoolVal::Const(b) => *b,
			BoolVal::Lit(l) => value.value(*l),
		})
		.map(|(i, _)| 1 << i)
		.sum()
}

/// The `i`'th bit of a binary encoding, where bits beyond the encoding's width
/// are zero.
pub(crate) fn bit(x: &[BoolVal], i: usize) -> BoolVal {
	x.get(i).copied().unwrap_or(BoolVal::Const(false))
}

/// A bit vector multiplied by a power of two, which only moves its bits up.
pub(crate) fn shifted(bits: &[BoolVal], shift: u32) -> Vec<BoolVal> {
	std::iter::repeat_n(BoolVal::Const(false), shift as usize)
		.chain(bits.iter().copied())
		.collect()
}

/// Convert `k` to unsigned binary in `bits`
pub(crate) fn as_binary(k: PosCoeff, bits: Option<u32>) -> Vec<bool> {
	let bits = bits.unwrap_or_else(|| BinaryEncoding::required_bits(*k) as u32);
	assert!(
		*k <= BinaryEncoding::largest_in(bits),
		"{k} cannot be represented in {bits} bits"
	);
	(0..bits).map(|b| *k & (1 << b) != 0).collect()
}

/// Divide rounding towards positive infinity.
// `Coeff::div_ceil` is still unstable for signed integers.
pub(crate) const fn div_ceil(a: Coeff, b: Coeff) -> Coeff {
	let (d, r) = (a / b, a % b);
	if (r > 0) == (b > 0) && r != 0 {
		d + 1
	} else {
		d
	}
}

/// Divide rounding towards negative infinity.
// `Coeff::div_floor` is still unstable for signed integers.
pub(crate) const fn div_floor(a: Coeff, b: Coeff) -> Coeff {
	let (d, r) = (a / b, a % b);
	if (r > 0) != (b > 0) && r != 0 {
		d - 1
	} else {
		d
	}
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
		helpers::binary_value,
		solver::{cadical::Cadical, SolveResult, Solver},
		BoolVal, Checker, ClauseDatabaseTools, Cnf, Coeff, Lit, Unsatisfiable, Valuation,
	};

	/// Every model of `cnf`, each decoded into the values of the given binary
	/// encodings.
	pub(crate) fn all_binary_solutions(cnf: &Cnf, xs: &[&[BoolVal]]) -> Vec<Vec<Coeff>> {
		let mut slv = Cadical::from(cnf);
		let vars = cnf.get_variables();
		let mut solutions = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			solutions.push(xs.iter().map(|x| binary_value(x, &value)).collect());
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
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		solutions.sort();
		solutions
	}

	/// A fresh binary encoding of `bits` free bits.
	pub(crate) fn binary_literals(cnf: &mut Cnf, bits: usize) -> Vec<BoolVal> {
		(0..bits).map(|_| BoolVal::Lit(cnf.new_lit())).collect()
	}

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
}
