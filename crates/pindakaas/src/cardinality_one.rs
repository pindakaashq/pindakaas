//! This module contains representations and encoding algorithms for Boolean
//! cardinality constraints counting to 1.
//!
//! These cardinality constraints can be represented using the
//! [`CardinalityOne`] type. In this module specialized [`Encoder`]
//! implementations are available, such as [`BitwiseEncoder`],
//! [`LadderEncoder`], [`PairwiseEncoder`], and [`ProductEncoder`]. However,
//! other [`Encoder`] implementations for
//! [`Cardinality`](crate::cardinality::Cardinality) and
//! [`NormalizedBoolLinear`] can also be used.

use std::{borrow::Cow, cmp::max};

use itertools::Itertools;

use crate::{
	bool_linear::{Comparator, LimitComp, NormalizedBoolLinear},
	BoolVal, Checker, ClauseDatabase, ClauseDatabaseTools, Encoder, Lit, Result, Valuation,
};

/// An encoder for [`CardinalityOne`] constraints that uses a logarithm
/// encoded selector variable to ensure the selection of at most one of
/// the given literals
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct BitwiseEncoder {}

#[derive(Debug, Clone)]

/// Linear constraint that enforces that ∑ litᵢ ≷ 1.
///
/// Compared to [`Cardinality`](crate::cardinality::Cardinality), the right hand
/// side constant is always 1.
///
/// All literals in the constraint are guaranteed to be from distinct Boolean
/// variables.
pub struct CardinalityOne {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
}

/// An encoder for an At Most One constraints that TODO
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LadderEncoder {}

/// An encoder for an At Most One constraints that for every pair of literals
/// states that one of the literals has to be `false`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PairwiseEncoder {}

/// An encoder for an At Most One constraint that arranges the literals in a
/// grid, giving every row and every column a selector literal.
///
/// Since a literal can only be `true` when both its row and its column are
/// selected, two `true` literals would always select two rows or two columns.
/// The constraint is therefore reduced to an At Most One constraint over the
/// row selectors and one over the column selectors, which are encoded the same
/// way. This uses roughly `2·√n` additional literals, sitting between the
/// quadratic number of clauses of the [`PairwiseEncoder`] and the weaker
/// propagation of the [`BitwiseEncoder`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProductEncoder {
	pairwise_cutoff: usize,
}

pub(crate) fn at_least_one_clause<Db>(db: &mut Db, card1: &CardinalityOne) -> Result
where
	Db: ClauseDatabase + ?Sized,
{
	debug_assert_eq!(card1.cmp, LimitComp::Equal);
	db.add_clause(card1.lits.iter().copied())
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for BitwiseEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "bitwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		let size = card1.lits.len();
		let bits = (usize::BITS - (size - 1).leading_zeros()) as usize;

		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?;
		}

		// Create a log encoded selection variable
		let signals = (0..bits).map(|_| db.new_lit()).collect_vec();

		// Enforce that literal can only be true when selected
		for (i, &lit) in card1.lits.iter().enumerate() {
			for (j, &sig) in signals.iter().enumerate() {
				if i & (1 << j) != 0 {
					db.add_clause([!lit, sig])?;
				} else {
					db.add_clause([!lit, !sig])?;
				}
			}
		}

		Ok(())
	}
}

impl CardinalityOne {
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
		NormalizedBoolLinear::from(self.clone()).check(value)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for LadderEncoder {
	#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "ladder_encoder", skip_all, fields(constraint = card1.trace_print()))
)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		// For an Exactly One constraint the ladder is known to start out `true`
		// and to have come down by the end, so both ends are constants rather
		// than literals that would only be fixed by a unit clause.
		let equal = card1.cmp == LimitComp::Equal;
		let mut a: BoolVal = if equal {
			true.into()
		} else {
			db.new_lit().into()
		}; // y_v-1
		for (i, &x) in card1.lits.iter().enumerate() {
			let last = i + 1 == card1.lits.len();
			let b: BoolVal = if equal && last {
				false.into()
			} else {
				db.new_lit().into()
			}; // y_v
			db.add_clause([!b, a])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			db.add_clause([(!x).into(), a])?; // x_v -> y_v-1
			db.add_clause([(!x).into(), !b])?; // x_v -> ¬y_v
			db.add_clause([!a, b, x.into()])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		// The ladder has to have come down by the end of an Exactly One
		// constraint. Its final step is already the constant `false` whenever
		// there was at least one literal, so this only has an effect when there
		// were none at all, where it reports that nothing can be selected.
		if equal {
			db.add_clause([!a])?;
		}
		Ok(())
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for PairwiseEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "pairwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?;
		}
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for [a, b] in card1.lits.iter().copied().array_combinations() {
			db.add_clause([!a, !b])?;
		}
		Ok(())
	}
}

impl ProductEncoder {
	/// The number of literals up to which the pairwise encoding is used when no
	/// other cutoff is set.
	///
	/// The pairwise encoding takes `n·(n-1)/2` clauses and no additional
	/// literals, which remains the cheaper of the two until around seven
	/// literals.
	const DEFAULT_PAIRWISE_CUTOFF: usize = 6;

	/// The smallest cutoff at which the encoder still makes progress.
	///
	/// Two literals are laid out as a single row of two columns, so the column
	/// dimension would be just as large as the group it came from. The pairwise
	/// encoding has to take over at or below that size.
	const MINIMUM_PAIRWISE_CUTOFF: usize = 2;

	/// Set the number of literals up to which the pairwise encoding is used
	/// instead of splitting the literals over a grid.
	///
	/// Raising the cutoff trades additional clauses for fewer additional
	/// literals.
	///
	/// The cutoff must be at least two, since a group of two literals is laid
	/// out as a single row of two columns and would not get any smaller. Lower
	/// values are a mistake on the part of the caller, and are raised to two so
	/// that the encoder still terminates.
	pub fn with_pairwise_cutoff(&mut self, cutoff: usize) -> &mut Self {
		assert!(
			cutoff >= Self::MINIMUM_PAIRWISE_CUTOFF,
			"a pairwise cutoff of {cutoff} would leave the encoder unable to \
			 make progress on a group of two literals"
		);
		self.pairwise_cutoff = max(cutoff, Self::MINIMUM_PAIRWISE_CUTOFF);
		self
	}
}

impl Default for ProductEncoder {
	fn default() -> Self {
		Self {
			pairwise_cutoff: Self::DEFAULT_PAIRWISE_CUTOFF,
		}
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for ProductEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "product_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?;
		}
		let mut to_constain: Vec<Cow<[Lit]>> = vec![(&card1.lits).into()];
		while let Some(lits) = to_constain.pop() {
			if lits.len() <= self.pairwise_cutoff {
				PairwiseEncoder::default().encode(
					db,
					&CardinalityOne {
						lits: lits.to_vec(),
						cmp: LimitComp::LessEq,
					},
				)?;
				continue;
			}

			// Lay the literals out in a grid that is as square as possible, filling
			// it row by row. The final row is allowed to be partially filled.
			let cols = {
				let root = lits.len().isqrt();
				if root * root < lits.len() {
					root + 1
				} else {
					root
				}
			};
			let rows = lits.len().div_ceil(cols);

			let row_lits = (0..rows).map(|_| db.new_lit()).collect_vec();
			let col_lits = (0..cols).map(|_| db.new_lit()).collect_vec();

			// A literal implies the selection of both the row and the column it was
			// placed in.
			for (i, &lit) in lits.iter().enumerate() {
				db.add_clause([!lit, row_lits[i / cols]])?;
				db.add_clause([!lit, col_lits[i % cols]])?;
			}

			// Two distinct literals differ in their row or in their column, so
			// constraining both dimensions constrains the literals themselves.
			to_constain.push(row_lits.into());
			to_constain.push(col_lits.into());
		}
		Ok(())
	}
}

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! card1_test_suite {
		($mod_name:ident, $encoder:expr) => {
			mod $mod_name {
				use itertools::Itertools;

				use crate::{
					bool_linear::LimitComp,
					cardinality_one::CardinalityOne,
					helpers::tests::{assert_checker, assert_solutions, expect_file},
					ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder,
				};

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
		bool_linear::LimitComp,
		cardinality_one::{
			BitwiseEncoder, CardinalityOne, LadderEncoder, PairwiseEncoder, ProductEncoder,
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
	/// plain pairwise encoding, while the smallest one splits the literals
	/// over grids, trading clauses for selector literals.
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
		assert!(grid_clauses < pairwise_clauses);
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

	/// The same grid as [`amo_product`], with the additional clause that keeps
	/// the all-false assignment out.
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
			crate::cardinality_one::BitwiseEncoder::default()
	}
	card1_test_suite! {
			ladder_encoder,
			crate::cardinality_one::LadderEncoder::default()
	}
	card1_test_suite! {
			pairwise_encoder,
			crate::cardinality_one::PairwiseEncoder::default()
	}
	card1_test_suite! {
			product_encoder,
			crate::cardinality_one::ProductEncoder::default()
	}
}
