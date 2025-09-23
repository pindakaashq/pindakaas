//! This module contains representations and encoding algorithms for Boolean
//! cardinality constraints counting to 1.
//!
//! These cardinality constraints can be represented using the
//! [`CardinalityOne`] type. In this module specialized [`Encoder`]
//! implementations are available, such as [`BitwiseEncoder`],
//! [`LadderEncoder`], and [`PairwiseEncoder`]. However, other [`Encoder`]
//! implementations for [`Cardinality`](crate::cardinality::Cardinality) and
//! [`NormalizedBoolLinear`] can also be used.

use itertools::Itertools;

use crate::{
	bool_linear::{Comparator, LimitComp, NormalizedBoolLinear},
	Checker, ClauseDatabase, ClauseDatabaseTools, Encoder, Lit, Result, Valuation,
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
		// TODO could be slightly optimised to not introduce fixed lits
		let mut a = db.new_lit(); // y_v-1
		if card1.cmp == LimitComp::Equal {
			db.add_clause([a])?;
		}
		for &x in card1.lits.iter() {
			let b = db.new_lit(); // y_v
			db.add_clause([!b, a])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			db.add_clause([!x, a])?; // x_v -> y_v-1
			db.add_clause([!x, !b])?; // x_v -> ¬y_v
			db.add_clause([!a, b, x])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		if card1.cmp == LimitComp::Equal {
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
		for (a, b) in card1.lits.iter().copied().tuple_combinations() {
			db.add_clause([!a, !b])?;
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

	use crate::{
		bool_linear::LimitComp,
		cardinality_one::{BitwiseEncoder, CardinalityOne, LadderEncoder, PairwiseEncoder},
		helpers::tests::{assert_encoding, assert_solutions, expect_file},
		ClauseDatabaseTools, Cnf, Encoder,
	};

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
}
