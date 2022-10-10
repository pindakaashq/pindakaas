use itertools::Itertools;

use crate::{linear::LimitComp, CardinalityOne, ClauseDatabase, Encoder, Literal, Result};

use super::at_least_one_clause;

/// An encoder for an At Most One constraints that for every pair of literals
/// states that one of the literals has to be `false`.
#[derive(Default)]
pub struct PairwiseEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne<DB::Lit>> for PairwiseEncoder {
	fn encode(&mut self, db: &mut DB, card1: &CardinalityOne<DB::Lit>) -> Result {
		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?
		}
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in card1.lits.iter().tuple_combinations() {
			db.add_clause(&[a.negate(), b.negate()])?
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use crate::{
		cardinality_one::tests::card1_test_suite,
		helpers::tests::{assert_enc_sol, assert_sol},
		linear::LimitComp,
		Checker,
	};

	card1_test_suite!(PairwiseEncoder::default());

	#[test]
	fn test_amo_pairwise() {
		// AMO on two literals
		assert_enc_sol!(
			PairwiseEncoder::default(),
			2,
			&CardinalityOne { lits: vec![1, 2], cmp: LimitComp::LessEq }
			=> vec![vec![-1, -2]],
			vec![vec![-1, -2], vec![1, -2], vec![-1, 2]]
		);
		// AMO on a negated literals
		assert_enc_sol!(
			PairwiseEncoder::default(),
			2,
			&CardinalityOne { lits: vec![-1, 2], cmp: LimitComp::LessEq }
			=> vec![vec![1, -2]],
			vec![vec![1, -2], vec![-1, -2], vec![1, 2]]
		);
		// AMO on three literals
		assert_enc_sol!(
			PairwiseEncoder::default(),
			3,
			&CardinalityOne { lits: vec![1, 2, 3], cmp: LimitComp::LessEq }
			=> vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]]
		);
	}
}
