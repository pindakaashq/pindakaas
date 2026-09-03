//! At-most-one by giving each literal the bit pattern of its index, which
//! needs `⌈log₂ n⌉` new literals and propagates weakly.

use itertools::Itertools;

use crate::{
	constraint::{
		linear::LimitComp,
		cardinality_one::{at_least_one_clause, CardinalityOne},
	},
	ClauseDatabase, ClauseDatabaseTools, Encoder, Result,
};

/// An encoder for [`CardinalityOne`] constraints that uses a logarithm
/// encoded selector variable to ensure the selection of at most one of
/// the given literals
#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct BitwiseEncoder {}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for BitwiseEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "bitwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		let size = card1.lits.len();
		let bits = (usize::BITS - (size - 1).leading_zeros()) as usize;

		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?;
		}

		// Create a log encoded selection variable
		let signals = (0..bits).map(|_| db.new_lit()).collect_vec();

		// Enforce that literal can only be true when selected
		for (i, &lit) in card1.lits.iter().enumerate() {
			for (j, &sig) in signals.iter().enumerate() {
				if i & (1 << j) != 0 {
					db.add_clause([!lit, sig])?;
				} else {
					db.add_clause([!lit, !sig])?;
				}
			}
		}

		Ok(())
	}
}
