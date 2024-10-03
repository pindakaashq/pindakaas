use itertools::Itertools;

use super::at_least_one_clause;
use crate::{
	linear::LimitComp,
	trace::{emit_clause, new_var},
	CardinalityOne, ClauseDatabase, Encoder, Result,
};

/// An encoder for [`CardinalityOne`] constraints that uses a logarithm
/// encoded selector variable to ensure the selection of at most one of
/// the given literals
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
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
		let signals = (0..bits).map(|_| new_var!(db)).collect_vec();

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

	card1_test_suite!(BitwiseEncoder::default());

	#[test]
	fn test_eo_bitwise() {
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let b = cnf.new_lit();
		BitwiseEncoder::default()
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
			&expect_file!["cardinality_one/bitwise/test_eo_bitwise.cnf"],
		);
		assert_solutions(
			&cnf,
			vec![a, b],
			&expect_file!["cardinality_one/bitwise/test_eo_bitwise.sol"],
		);
	}
}
