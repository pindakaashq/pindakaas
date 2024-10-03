use itertools::Itertools;

use super::at_least_one_clause;
use crate::{
	linear::LimitComp, trace::emit_clause, CardinalityOne, ClauseDatabase, Encoder, Result,
};

/// An encoder for an At Most One constraints that for every pair of literals
/// states that one of the literals has to be `false`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PairwiseEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne> for PairwiseEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "pairwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut DB, card1: &CardinalityOne) -> Result {
		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?
		}
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in card1.lits.iter().tuple_combinations() {
			emit_clause!(db, [!a, !b])?
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use itertools::Itertools;
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		cardinality_one::tests::card1_test_suite,
		helpers::tests::{assert_checker, assert_encoding, assert_solutions, expect_file},
		linear::LimitComp,
		Cnf, NextVarRange,
	};

	card1_test_suite!(PairwiseEncoder::default());

	#[test]
	fn test_amo_pairwise() {
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
}
