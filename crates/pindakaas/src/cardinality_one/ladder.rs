use crate::{
	linear::LimitComp,
	trace::{emit_clause, new_var},
	CardinalityOne, ClauseDatabase, Encoder, Result,
};

/// An encoder for an At Most One constraints that TODO
#[derive(Default)]
pub struct LadderEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne> for LadderEncoder {
	#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "ladder_encoder", skip_all, fields(constraint = card1.trace_print()))
)]
	fn encode(&self, db: &mut DB, card1: &CardinalityOne) -> Result {
		// TODO could be slightly optimised to not introduce fixed lits
		let mut a = new_var!(db); // y_v-1
		if card1.cmp == LimitComp::Equal {
			emit_clause!(db, [a])?;
		}
		for x in card1.lits.iter() {
			let b = new_var!(db); // y_v
			emit_clause!(db, [!b, a])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			emit_clause!(db, [!x, a])?; // x_v -> y_v-1
			emit_clause!(db, [!x, !b])?; // x_v -> ¬y_v
			emit_clause!(db, [!a, b, *x])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		if card1.cmp == LimitComp::Equal {
			emit_clause!(db, [!a])?;
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

	card1_test_suite!(LadderEncoder::default());

	#[test]
	fn test_eo_ladder() {
		assert_enc_sol!(
			LadderEncoder::default(),
			2,
			&CardinalityOne { lits: lits![1, 2], cmp: LimitComp::Equal }
			=> vec![
				lits![-1, 3],
				lits![1, -3, 4],
				lits![-1, -4],
				lits![-2, -5],
				lits![-2, 4],
				lits![3],
				lits![-4, 3],
				lits![-4, 5, 2],
				lits![-5, 4],
				lits![-5],
			],
			vec![
				lits![1, -2],
				lits![-1, 2],
			]
		);
	}
}
