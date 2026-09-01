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
	constraint::bool_linear::PosCoeff, decision::integer::BinaryEncoding, BoolVal, ClauseDatabase,
	Coeff, Valuation,
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
		constraint::{bool_linear::PosCoeff, int_linear::Term},
		helpers::binary_value,
		solver::{cadical::Cadical, SolveResult, Solver},
		BoolVal, Checker, ClauseDatabaseTools, Cnf, Coeff, Lit, Unsatisfiable, Valuation,
	};

	macro_rules! linear_test_suite {
		($module:ident, $encoder:expr) => {
			mod $module {
				use traced_test::test;

				use crate::helpers::tests::prelude::*;

				#[test]
				fn small_le_1() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 2), (b, 3), (c, 5)]),
						LimitComp::LessEq,
						PosCoeff::new(6),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_le_1.sol"],
					);
				}

				#[test]
				fn small_le_2() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let d = cnf.new_lit();
					let e = cnf.new_lit();
					let f = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(
							&mut cnf,
							&[(!a, 3), (!b, 6), (!c, 1), (!d, 2), (!e, 3), (!f, 6)],
						),
						LimitComp::LessEq,
						PosCoeff::new(19),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d, e, f],
						&expect_file!["linear/test_small_le_2.sol"],
					);
				}

				#[test]
				fn small_le_3() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 1), (b, 2), (c, 4)]),
						LimitComp::LessEq,
						PosCoeff::new(5),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_le_3.sol"],
					);
				}

				#[test]
				fn small_le_4() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 4), (b, 6), (c, 7)]),
						LimitComp::LessEq,
						PosCoeff::new(10),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_le_4.sol"],
					);
				}

				#[test]
				fn small_eq_1() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 1), (b, 2), (c, 4)]),
						LimitComp::Equal,
						PosCoeff::new(5),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_eq_1.sol"],
					);
				}

				#[test]
				fn small_eq_2() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 1), (b, 2), (c, 3)]),
						LimitComp::Equal,
						PosCoeff::new(3),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_eq_2.sol"],
					);
				}

				#[test]
				fn small_eq_3() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let d = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 2), (b, 3), (c, 5), (d, 7)]),
						LimitComp::Equal,
						PosCoeff::new(10),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_small_eq_3.sol"],
					);
				}

				#[test]
				fn small_eq_4() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let d = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 2), (b, 1), (c, 2), (d, 2)]),
						LimitComp::Equal,
						PosCoeff::new(4),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_small_eq_4.sol"],
					);
				}

				/// Encode the at-most-one constraint over each of the `groups`, so
				/// that the solutions of the formula can be compared against those
				/// of encoders that ignore the grouping of the terms.
				fn amo(cnf: &mut Cnf, groups: &[&[Lit]]) {
					for lits in groups {
						PairwiseEncoder::default()
							.encode(
								cnf,
								&CardinalityOne {
									lits: lits.to_vec(),
									cmp: LimitComp::LessEq,
								},
							)
							.unwrap();
					}
				}

				#[test]
				fn choice_le() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b], &[c, d]]);
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[(a, PosCoeff::new(3)), (b, PosCoeff::new(5))],
								"x0",
								false,
							)
							.unwrap(),
							Term::from_at_most_one(
								&mut cnf,
								&[(c, PosCoeff::new(2)), (d, PosCoeff::new(4))],
								"x1",
								false,
							)
							.unwrap(),
						],
						LimitComp::LessEq,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_le.sol"],
					);
				}

				#[test]
				fn choice_eq() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b], &[c, d]]);
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[(a, PosCoeff::new(3)), (b, PosCoeff::new(5))],
								"x0",
								true,
							)
							.unwrap(),
							Term::from_at_most_one(
								&mut cnf,
								&[(c, PosCoeff::new(2)), (d, PosCoeff::new(4))],
								"x1",
								true,
							)
							.unwrap(),
						],
						LimitComp::Equal,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_eq.sol"],
					);
				}

				#[test]
				fn choice_shared_coefficient() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b, c]]);
					// Two of the mutually exclusive terms share a coefficient.
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[
									(a, PosCoeff::new(3)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(5)),
								],
								"x0",
								false,
							)
							.unwrap(),
							Term::from_at_most_one(&mut cnf, &[(d, PosCoeff::new(4))], "x1", false)
								.unwrap(),
						],
						LimitComp::LessEq,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_shared_coefficient.sol"],
					);
				}

				#[test]
				fn choice_shared_coefficient_eq() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b, c]]);
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[
									(a, PosCoeff::new(3)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(5)),
								],
								"x0",
								true,
							)
							.unwrap(),
							Term::from_at_most_one(&mut cnf, &[(d, PosCoeff::new(4))], "x1", true)
								.unwrap(),
						],
						LimitComp::Equal,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_shared_coefficient_eq.sol"],
					);
				}

				#[test]
				fn chain_le() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					// The literal of each term is implied by the literal of the next.
					for (x, y) in [(a, b), (b, c)] {
						cnf.add_clause([!y, x]).unwrap();
					}
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_implication_chain(
								&mut cnf,
								&[
									(a, PosCoeff::new(2)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(4)),
								],
								"x0",
							)
							.unwrap(),
							Term::from_at_most_one(&mut cnf, &[(d, PosCoeff::new(5))], "x1", false)
								.unwrap(),
						],
						LimitComp::LessEq,
						PosCoeff::new(8),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_chain_le.sol"],
					);
				}

				#[test]
				fn issue_177() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 3), (b, 9)]),
						LimitComp::Equal,
						PosCoeff::new(10),
					);
					let res = $encoder.encode(&mut cnf, &con);
					if res.is_ok() {
						assert_solutions(
							&cnf,
							vec![a, b],
							&expect_file!["linear/test_issue_177.sol"],
						);
					}
				}
			}
		};
	}
	pub(crate) use linear_test_suite;

	/// A term that nothing else constrains is an integer worth its coefficient
	/// when its literal holds, which is a group of one.
	pub(crate) fn construct_terms<L: Into<Lit> + Clone>(
		db: &mut Cnf,
		terms: &[(L, Coeff)],
	) -> Vec<Term> {
		terms
			.iter()
			.enumerate()
			.map(|(i, (lit, coef))| {
				let group = [(lit.clone().into(), PosCoeff::new(*coef))];
				Term::from_at_most_one(db, &group, &format!("x{i}"), false).unwrap()
			})
			.collect()
	}

	/// Everything the test-suite macros need in scope where they expand.
	///
	/// The macros are invoked from other modules, so any path written inside
	/// one has to resolve at the call site rather than where it was written.
	/// Naming them here instead means a module can move without four macro
	/// bodies having to hear about it.
	pub(crate) mod prelude {
		pub(crate) use itertools::Itertools;

		pub(crate) use crate::{
			constraint::{
				bool_linear::{
					AdderEncoder, BddEncoder, Comparator, LimitComp, LinExp, Linear, PosCoeff,
					SwcEncoder, TotalizerEncoder,
				},
				cardinality::{tests::card_test_suite, Cardinality, SortingNetworkEncoder},
				cardinality_one::{tests::card1_test_suite, CardinalityOne, PairwiseEncoder},
				int_linear::{NormalizedIntLinear, Term},
				linear::{BoolLinAggregator, LinVariant, LinearEncoder, StaticLinEncoder},
				sorted::{SortedEncoder, SortedStrategy},
			},
			helpers::tests::{
				all_binary_solutions, assert_checker, assert_encoding, assert_solutions,
				binary_literals, construct_terms, expect_file,
			},
			BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Encoder, Lit, Unsatisfiable,
		};
	}

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
