use super::at_least_one_clause;
use crate::{
	linear::LimitComp, trace::emit_clause, CardinalityOne, ClauseDatabase, Encoder, Literal, Result,
};

/// An encoder for [`CardinalityOne`] constraints that uses a logarithm
/// encoded selector variable to ensure the selection of at most one of
/// the given literals
#[derive(Default)]
pub struct BitwiseEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne<DB::Lit>> for BitwiseEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "bitwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, card1: &CardinalityOne<DB::Lit>) -> Result {
		let size = card1.lits.len();
		let bits = (usize::BITS - (size - 1).leading_zeros()) as usize;

		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?
		}

		// Create a log encoded selection variable
		let signals = (0..bits).map(|_| db.new_var()).collect::<Vec<_>>();

		// Enforce that literal can only be true when selected
		for (i, lit) in card1.lits.iter().enumerate() {
			for (j, sig) in signals.iter().enumerate() {
				if i & (1 << j) != 0 {
					emit_clause!(db, &[lit.negate(), sig.clone()])?;
				} else {
					emit_clause!(db, &[lit.negate(), sig.negate()])?;
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
		helpers::tests::{assert_enc_sol, assert_sol},
		linear::LimitComp,
	};

	card1_test_suite!(BitwiseEncoder::default());

	#[test]
	fn test_eo_bitwise() {
		assert_enc_sol!(
			BitwiseEncoder::default(),
			2,
			&CardinalityOne { lits: vec![1, 2], cmp: LimitComp::Equal }
			=> vec![
				vec![1, 2],
				vec![-1, -3],
				vec![-2, 3],
			],
			vec![
				vec![1, -2],
				vec![-1, 2],
			]
		);
	}
}
