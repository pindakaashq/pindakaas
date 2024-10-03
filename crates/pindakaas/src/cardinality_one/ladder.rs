use crate::{
	helpers::{emit_clause, new_var},
	linear::LimitComp,
	CardinalityOne, ClauseDatabase, Encoder, Result,
};

/// An encoder for an At Most One constraints that TODO
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LadderEncoder {}

impl<DB: ClauseDatabase> Encoder<DB, CardinalityOne> for LadderEncoder {
	#[cfg_attr(
	any(feature = "tracing", test),
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
	use itertools::Itertools;
	use traced_test::test;

	use crate::{
		cardinality_one::tests::card1_test_suite,
		helpers::tests::{assert_checker, assert_encoding, assert_solutions, expect_file},
		linear::LimitComp,
		CardinalityOne, ClauseDatabase, Cnf, Encoder, LadderEncoder, NextVarRange,
	};

	card1_test_suite!(LadderEncoder::default());

	#[test]
	fn test_eo_ladder() {
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
}
