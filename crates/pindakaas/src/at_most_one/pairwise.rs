use itertools::Itertools;

use crate::{AtMostOne, ClauseDatabase, Encoder, Literal, Result};

/// An encoder for an At Most One constraints that for every pair of literals
/// states that one of the literals has to be `false`.
pub struct PairwiseEncoder<'a, Lit: Literal> {
	amo: &'a AtMostOne<Lit>,
}

impl<'a, Lit: Literal> PairwiseEncoder<'a, Lit> {
	pub fn new(amo: &'a AtMostOne<Lit>) -> Self {
		Self { amo }
	}
}

impl<'a, Lit: Literal> Encoder for PairwiseEncoder<'a, Lit> {
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result {
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in self.amo.lits.iter().tuple_combinations() {
			db.add_clause(&[a.negate(), b.negate()])?
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use crate::{helpers::tests::assert_enc_sol, Checker};

	#[test]
	fn test_amo_pairwise() {
		// AMO on two literals
		assert_enc_sol!(
			PairwiseEncoder,
			2,
			&AtMostOne { lits: vec![1, 2] },
			vec![vec![-1, -2]],
			vec![vec![-1, -2], vec![1, -2], vec![-1, 2]]
		);
		// AMO on a negated literals
		assert_enc_sol!(
			PairwiseEncoder,
			2,
			&AtMostOne { lits: vec![-1, 2] },
			vec![vec![1, -2]],
			vec![vec![1, -2], vec![-1, -2], vec![1, 2]]
		);
		// AMO on three literals
		assert_enc_sol!(
			PairwiseEncoder,
			3,
			&AtMostOne {
				lits: vec![1, 2, 3]
			},
			vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]]
		);
	}
}
