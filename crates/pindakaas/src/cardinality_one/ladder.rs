use crate::{
	linear::LimitComp, trace::emit_clause, CardinalityOne, ClauseDatabase, Encoder, Literal, Result,
};

/// An encoder for an At Most One constraints that TODO
#[derive(Default)]
pub struct LadderEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne<DB::Lit>> for LadderEncoder {
	#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "ladder_encoder", skip_all, fields(constraint = card1.trace_print()))
)]
	fn encode(&mut self, db: &mut DB, card1: &CardinalityOne<DB::Lit>) -> Result {
		// TODO could be slightly optimised to not introduce fixed lits
		let mut a = db.new_var(); // y_v-1
		if card1.cmp == LimitComp::Equal {
			emit_clause!(db, &[a.clone()])?;
		}
		for x in card1.lits.iter() {
			let b = db.new_var(); // y_v
			emit_clause!(db, &[b.negate(), a.clone()])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			emit_clause!(db, &[x.negate(), a.clone()])?; // x_v -> y_v-1
			emit_clause!(db, &[x.negate(), b.negate()])?; // x_v -> ¬y_v
			emit_clause!(db, &[a.negate(), b.clone(), x.clone()])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		if card1.cmp == LimitComp::Equal {
			emit_clause!(db, &[a.negate()])?;
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
		Checker,
	};

	card1_test_suite!(LadderEncoder::default());

	#[test]
	fn test_eo_ladder() {
		assert_enc_sol!(
			LadderEncoder::default(),
			2,
			&CardinalityOne { lits: vec![1, 2], cmp: LimitComp::Equal }
			=> vec![
				vec![-1, 3],
				vec![1, -3, 4],
				vec![-1, -4],
				vec![-2, -5],
				vec![-2, 4],
				vec![3],
				vec![-4, 3],
				vec![-4, 5, 2],
				vec![-5, 4],
				vec![-5],
			],
			vec![
				vec![1, -2],
				vec![-1, 2],
			]
		);
	}
}
