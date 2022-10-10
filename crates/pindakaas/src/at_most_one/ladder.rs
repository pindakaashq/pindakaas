use crate::{AtMostOne, ClauseDatabase, Encoder, Literal, Result};

/// An encoder for an At Most One constraints that TODO
#[derive(Default)]
pub struct LadderEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, AtMostOne<DB::Lit>> for LadderEncoder {
	fn encode(&mut self, db: &mut DB, amo: &AtMostOne<DB::Lit>) -> Result {
		// TODO could be slightly optimised to not introduce fixed lits
		let mut a = db.new_var(); // y_v-1
		db.add_clause(&[a.clone()])?;
		for x in amo.lits.iter() {
			let b = db.new_var(); // y_v
			db.add_clause(&[b.negate(), a.clone()])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			db.add_clause(&[x.negate(), a.clone()])?; // x_v -> y_v-1
			db.add_clause(&[x.negate(), b.negate()])?; // x_v -> ¬y_v
			db.add_clause(&[a.negate(), b.clone(), x.clone()])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		db.add_clause(&[a.negate()])?;
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{helpers::tests::assert_enc_sol, Checker};

	// TODO: Ladder is ExactlyOne, not AtMostOne
	// amo_test_suite!(LadderEncoder::default());

	#[test]
	fn test_amo_ladder() {
		assert_enc_sol!(
			LadderEncoder::default(),
			2,
			&AtMostOne { lits: vec![1, 2] }
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
			]
		);
	}
}
