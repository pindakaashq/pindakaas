use itertools::Itertools;

use super::at_least_one_clause;
use crate::{
	linear::LimitComp, trace::emit_clause, CardinalityOne, ClauseDatabase, Encoder, Result,
};

/// An encoder for [`CardinalityOne`] constraints that uses a logarithm
/// encoded selector variable to ensure the selection of at most one of
/// the given literals
#[derive(Default)]
pub struct BitwiseEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne> for BitwiseEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "bitwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut DB, card1: &CardinalityOne) -> Result {
		let size = card1.lits.len();
		let bits = (usize::BITS - (size - 1).leading_zeros()) as usize;

		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?
		}

		// Create a log encoded selection variable
		let signals = (0..bits).map(|_| db.new_var()).collect_vec();

		// Enforce that literal can only be true when selected
		for (i, lit) in card1.lits.iter().enumerate() {
			for (j, sig) in signals.iter().enumerate() {
				if i & (1 << j) != 0 {
					emit_clause!(db, [!lit, *sig])?;
				} else {
					emit_clause!(db, [!lit, !sig])?;
				}
			}
		}

		Ok(())
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		cardinality_one::tests::card1_test_suite,
		helpers::tests::{assert_enc_sol, assert_sol, lits},
		linear::LimitComp,
		Lit,
	};

	card1_test_suite!(BitwiseEncoder::default());

	#[test]
	fn test_eo_bitwise() {
		assert_enc_sol!(
			BitwiseEncoder::default(),
			2,
			&CardinalityOne { lits: lits![1, 2], cmp: LimitComp::Equal }
			=> vec![
				lits![1, 2],
				lits![-1, -3],
				lits![-2, 3],
			],
			vec![
				lits![1, -2],
				lits![-1, 2],
			]
		);
	}
}
