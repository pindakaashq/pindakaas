//! At-most-one by forbidding every pair, which needs no new literals and
//! `n(n-1)/2` clauses.

use itertools::Itertools;

use crate::{
	constraint::{
		linear::LimitComp,
		cardinality_one::{at_least_one_clause, CardinalityOne},
	},
	ClauseDatabase, ClauseDatabaseTools, Encoder, Result,
};

/// An encoder for an At Most One constraints that for every pair of literals
/// states that one of the literals has to be `false`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PairwiseEncoder {}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for PairwiseEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "pairwise_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		// Add clause to ensure "at least one" literal holds
		if card1.cmp == LimitComp::Equal {
			at_least_one_clause(db, card1)?;
		}
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for [a, b] in card1.lits.iter().copied().array_combinations() {
			db.add_clause([!a, !b])?;
		}
		Ok(())
	}
}
