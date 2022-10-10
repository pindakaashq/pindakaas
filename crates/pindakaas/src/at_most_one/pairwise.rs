use itertools::Itertools;

use crate::{AtMostOne, ClauseDatabase, Encoder, Literal, Result};

/// An encoder for an At Most One constraints that for every pair of literals
/// states that one of the literals has to be `false`.
#[derive(Default)]
pub struct PairwiseEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, AtMostOne<DB::Lit>> for PairwiseEncoder {
	fn encode(&mut self, db: &mut DB, amo: &AtMostOne<DB::Lit>) -> Result {
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in amo.lits.iter().tuple_combinations() {
			db.add_clause(&[a.negate(), b.negate()])?
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use crate::{
		at_most_one::tests::amo_test_suite,
		helpers::tests::{assert_enc_sol, assert_sol},
		Checker,
	};

	amo_test_suite!(PairwiseEncoder::default());

	#[test]
	fn test_amo_pairwise() {
		// AMO on two literals
		assert_enc_sol!(
			PairwiseEncoder::default(),
			2,
			&AtMostOne { lits: vec![1, 2] }
			=> vec![vec![-1, -2]],
			vec![vec![-1, -2], vec![1, -2], vec![-1, 2]]
		);
		// AMO on a negated literals
		assert_enc_sol!(
			PairwiseEncoder::default(),
			2,
			&AtMostOne { lits: vec![-1, 2] }
			=> vec![vec![1, -2]],
			vec![vec![1, -2], vec![-1, -2], vec![1, 2]]
		);
		// AMO on three literals
		assert_enc_sol!(
			PairwiseEncoder::default(),
			3,
			&AtMostOne {
				lits: vec![1, 2, 3]
			}
			=> vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]]
		);
	}
}
