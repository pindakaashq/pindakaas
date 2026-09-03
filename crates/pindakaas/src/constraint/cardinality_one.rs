//! The constraint that exactly one, or at most one, of a set of literals holds.
//!
//! The commonest constraint there is, and the one with the most encodings: the
//! four below trade clauses against variables differently, so which suits
//! depends on how many literals there are.

pub use crate::encoder::{
	bitwise::BitwiseEncoder, ladder::LadderEncoder, pairwise::PairwiseEncoder,
	product::ProductEncoder,
};
use rustc_hash::FxHashSet;

use crate::{
	constraint::{
		linear::{Comparator, LimitComp},
		cardinality::Cardinality,
	},
	Checker, ClauseDatabase, ClauseDatabaseTools, Lit, Result, Valuation,
};

#[derive(Debug, Clone)]
/// Linear constraint that enforces that ∑ litᵢ ≷ 1.
///
/// Compared to a [`Cardinality`](super::cardinality::Cardinality) constraint,
/// the right hand side constant is always 1.
///
/// All literals in the constraint are guaranteed to be from distinct Boolean
/// variables.
pub struct CardinalityOne {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
}

pub(crate) fn at_least_one_clause<Db>(db: &mut Db, card1: &CardinalityOne) -> Result
where
	Db: ClauseDatabase + ?Sized,
{
	debug_assert_eq!(card1.cmp, LimitComp::Equal);
	db.add_clause(card1.lits.iter().copied())
}

impl CardinalityOne {
	/// The constraint that one of `lits` holds, or at most one of them.
	///
	/// # Panics
	///
	/// If two of `lits` are over the same variable, which no encoding here
	/// expects.
	///
	/// # Examples
	///
	/// ```rust
	/// # use pindakaas::{
	/// #     constraint::{linear::LimitComp,
	/// #                  cardinality_one::{CardinalityOne, PairwiseEncoder}},
	/// #     ClauseDatabaseTools, Cnf, Encoder,
	/// # };
	/// let mut f = Cnf::default();
	/// let (a, b, c) = f.new_lits();
	///
	/// // Exactly one of the three.
	/// let con = CardinalityOne::new(vec![a, b, c], LimitComp::Equal);
	/// PairwiseEncoder::default().encode(&mut f, &con)?;
	/// # Ok::<(), pindakaas::Unsatisfiable>(())
	/// ```
	pub fn new(lits: Vec<Lit>, cmp: LimitComp) -> Self {
		assert!(
			lits.iter().map(|l| l.var()).collect::<FxHashSet<_>>().len() == lits.len(),
			"an at-most-one constraint is over distinct variables"
		);
		Self { lits, cmp }
	}

	/// Get the comparator of the cardinality constraint.
	pub fn comparator(&self) -> Comparator {
		self.cmp.clone().into()
	}

	/// Iterate over the literals of the cardinality constraint.
	pub fn iter_lits(&self) -> impl Iterator<Item = Lit> + '_ {
		self.lits.iter().copied()
	}

	#[cfg(any(feature = "tracing", test))]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(self.lits.iter().map(trace_print_lit), " + ");
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} 1")
	}
}

impl Checker for CardinalityOne {
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<()> {
		Cardinality::from(self.clone()).check(value)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	#[test]
	#[should_panic = "distinct variables"]
	fn a_repeated_variable_is_not_an_at_most_one_constraint() {
		use crate::{
			constraint::{linear::LimitComp, cardinality_one::CardinalityOne},
			ClauseDatabaseTools, Cnf,
		};
		let mut f = Cnf::default();
		let a = f.new_lit();
		let _ = CardinalityOne::new(vec![a, !a], LimitComp::Equal);
	}

	macro_rules! card1_test_suite {
		($mod_name:ident, $encoder:expr) => {
			mod $mod_name {
				use itertools::Itertools;

				use crate::helpers::tests::prelude::*;

				const LARGE_N: usize = 50;
				// ------ At Most One testing ------
				#[test]
				fn amo_pair() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_amo_pair.sol"],
					);
				}
				#[test]
				fn amo_one_neg() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, !b],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_amo_one_neg.sol"],
					);
				}
				#[test]
				fn amo_neg_only() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![!a, !b],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_amo_neg_only.sol"],
					);
				}
				#[test]
				fn amo_triple() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b, c],
								cmp: LimitComp::LessEq,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["cardinality_one/test_amo_triple.sol"],
					);
				}
				#[test]
				fn amo_large() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone(),
						cmp: LimitComp::LessEq,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn amo_large_neg() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone().into_iter().map(|l| !l).collect_vec(),
						cmp: LimitComp::LessEq,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn amo_large_mix() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();

					let con = CardinalityOne {
						lits: vars
							.clone()
							.into_iter()
							.enumerate()
							.map(|(i, l)| if i % 2 == 0 { l } else { !l })
							.collect_vec(),
						cmp: LimitComp::LessEq,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				// ------ Exactly One testing ------
				#[test]
				fn eo_pair() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_eo_pair.sol"],
					);
				}
				#[test]
				fn eo_one_neg() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, !b],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_eo_one_neg.sol"],
					);
				}
				#[test]
				fn eo_neg_only() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![!a, !b],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b],
						&expect_file!["cardinality_one/test_eo_neg_only.sol"],
					);
				}
				#[test]
				fn eo_triple() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&CardinalityOne {
								lits: vec![a, b, c],
								cmp: LimitComp::Equal,
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["cardinality_one/test_eo_triple.sol"],
					);
				}
				#[test]
				fn eo_large() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone(),
						cmp: LimitComp::Equal,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn eo_large_neg() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars.clone().iter().map(|&l| !l).collect_vec(),
						cmp: LimitComp::Equal,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
				#[test]
				fn eo_large_mix() {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(LARGE_N).iter_lits().collect_vec();
					let con = CardinalityOne {
						lits: vars
							.clone()
							.into_iter()
							.enumerate()
							.map(|(i, l)| if i % 2 == 0 { l } else { !l })
							.collect_vec(),
						cmp: LimitComp::Equal,
					};
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_checker(&cnf, &con);
				}
			}
		};
	}

	pub(crate) use card1_test_suite;
	use itertools::Itertools;

	use crate::{
		constraint::{
			linear::LimitComp,
			cardinality_one::{
				BitwiseEncoder, CardinalityOne, LadderEncoder, PairwiseEncoder, ProductEncoder,
			},
		},
		helpers::tests::{assert_encoding, assert_solutions, expect_file},
		ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder, Unsatisfiable,
	};

	/// Seven literals is the smallest number that is laid out on a grid, here a
	/// full three by three one with two positions to spare.
	///
	/// The shared encoder test suite only enumerates solutions for two and
	/// three literals, which the product encoding hands to the pairwise
	/// encoding, so the grid itself is only reached from tests like this one.
	#[test]
	fn amo_product() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(7).iter_lits().collect_vec();
		ProductEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["cardinality_one/product/test_amo_product.sol"],
		);
	}

	/// The smallest usable cutoff splits the literals as far as they go, so the
	/// same ten literals now reach the pairwise encoding only after two rounds
	/// of grids. The solutions must not change.
	#[test]
	fn amo_product_minimum_cutoff() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(10).iter_lits().collect_vec();
		let mut encoder = ProductEncoder::default();
		let _ = encoder.with_pairwise_cutoff(2);
		encoder
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["cardinality_one/product/test_amo_product_partial_row.sol"],
		);
	}

	/// A cutoff at or above the number of literals bypasses the grid, leaving a
	/// plain pairwise encoding.
	#[test]
	fn amo_product_cutoff_above_size() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(10).iter_lits().collect_vec();
		let mut encoder = ProductEncoder::default();
		let _ = encoder.with_pairwise_cutoff(10);
		encoder
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["cardinality_one/product/test_amo_product_partial_row.sol"],
		);
	}

	/// Every correct encoding allows the same solutions, so the tests above
	/// would still pass if the cutoff never reached the encoder. Compare the
	/// formulas themselves: a cutoff above the number of literals leaves a
	/// plain pairwise encoding, while the smallest one splits the literals over
	/// grids and introduces selectors.
	///
	/// Note that the smallest cutoff is not the smallest encoding. Ten literals
	/// split all the way down cost more clauses than encoding them pairwise,
	/// since every grid adds selectors to tie back to their literals, which is
	/// what the default cutoff is there to avoid.
	#[test]
	fn amo_product_cutoff_changes_encoding() {
		let sizes = |cutoff: usize| {
			let mut encoder = ProductEncoder::default();
			let _ = encoder.with_pairwise_cutoff(cutoff);
			let mut cnf = Cnf::default();
			let vars = cnf.new_var_range(10).iter_lits().collect_vec();
			encoder
				.encode(
					&mut cnf,
					&CardinalityOne {
						lits: vars,
						cmp: LimitComp::LessEq,
					},
				)
				.unwrap();
			(cnf.num_clauses(), cnf.num_vars() - 10)
		};

		let (pairwise_clauses, pairwise_selectors) = sizes(10);
		let (grid_clauses, grid_selectors) = sizes(2);
		assert_eq!((pairwise_clauses, pairwise_selectors), (45, 0));
		assert!(grid_selectors > 0);
		assert_ne!(grid_clauses, pairwise_clauses);
	}

	/// A pair of literals is laid out as a single row of two columns, so a
	/// cutoff below two would hand the column dimension a group just as large
	/// as the one it came from, and the encoder would never finish. A release
	/// build raises the cutoff rather than looping.
	#[test]
	#[should_panic(expected = "unable to make progress")]
	fn amo_product_cutoff_below_minimum() {
		let _ = ProductEncoder::default().with_pairwise_cutoff(1);
	}

	/// Ten literals need a three by four grid, leaving the last row partly
	/// filled, so not every row and column combination carries a literal.
	#[test]
	fn amo_product_partial_row() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(10).iter_lits().collect_vec();
		ProductEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["cardinality_one/product/test_amo_product_partial_row.sol"],
		);
	}

	/// Fifty literals recurse: the eight column selectors are themselves laid
	/// out on a grid rather than encoded pairwise.
	#[test]
	fn amo_product_nested() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(50).iter_lits().collect_vec();
		ProductEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["cardinality_one/product/test_amo_product_nested.sol"],
		);
	}

	/// The "at least one" half is expressed per row, so a grid whose final row
	/// is only partly filled has to pair each row selector with just the
	/// literals actually placed in it. Here the last row holds two of the ten.
	#[test]
	fn eo_product_partial_row() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(10).iter_lits().collect_vec();
		ProductEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["cardinality_one/product/test_eo_product_partial_row.sol"],
		);
	}

	/// The same grid as [`amo_product`], with the row clauses that keep the
	/// all-false assignment out.
	#[test]
	fn eo_product() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(7).iter_lits().collect_vec();
		ProductEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["cardinality_one/product/test_eo_product.sol"],
		);
	}

	#[test]
	fn amo_pairwise() {
		// AMO on two literals
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise1.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise1.sol"],
		);
		// AMO on a negated literals
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, !b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise2.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise2.sol"],
		);
		// AMO on three literals
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		let c = cnf.new_lit();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b, c],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise3.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b, c],
			&expect_file!["cardinality_one/pairwise/test_amo_pairwise3.sol"],
		);
	}

	#[test]
	fn eo_bitwise() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		BitwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/bitwise/test_eo_bitwise.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/bitwise/test_eo_bitwise.sol"],
		);
	}

	/// The ends of the ladder are known for an Exactly One constraint, so they
	/// are constants rather than literals introduced only to be fixed by a unit
	/// clause. Neither end should appear in the encoding.
	#[test]
	fn eo_ladder_has_no_fixed_literals() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(4).iter_lits().collect_vec();
		LadderEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vars,
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();

		// Three ladder steps for four literals, of which the first and the last
		// are constants, leaving four literals and three steps.
		assert_eq!(cnf.num_vars(), 7);
		assert!(
			cnf.iter().all(|clause| clause.len() > 1),
			"the encoding should not contain a unit clause"
		);
	}

	/// An Exactly One constraint over no literals cannot be satisfied, which
	/// the ladder reports rather than silently accepting.
	#[test]
	fn eo_ladder_empty() {
		let mut cnf = Cnf::default();
		assert_eq!(
			LadderEncoder::default().encode(
				&mut cnf,
				&CardinalityOne {
					lits: Vec::new(),
					cmp: LimitComp::Equal,
				},
			),
			Err(Unsatisfiable)
		);
	}

	#[test]
	fn eo_ladder() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		LadderEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();

		assert_encoding(
			&cnf,
			&expect_file!["cardinality_one/ladder/test_eo_ladder.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/ladder/test_eo_ladder.sol"],
		);
	}

	card1_test_suite! {
			bitwise_encoder,
			crate::constraint::cardinality_one::BitwiseEncoder::default()
	}
	card1_test_suite! {
			ladder_encoder,
			crate::constraint::cardinality_one::LadderEncoder::default()
	}
	card1_test_suite! {
			pairwise_encoder,
			PairwiseEncoder::default()
	}
	card1_test_suite! {
			product_encoder,
			crate::constraint::cardinality_one::ProductEncoder::default()
	}
}
