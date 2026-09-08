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

/// At-most-one encoding using the binary representation of each literal's index.
///
/// Exact-one adds the original literals as one clause; the index bits still
/// encode only the at-most-one part.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{
///     constraint::{cardinality_one::CardinalityOne, linear::LimitComp},
///     encoder::bitwise::BitwiseEncoder, ClauseDatabase, Cnf, Encoder,
/// };
/// let mut cnf = Cnf::default();
/// let lits = cnf.new_var_range(4).map(Into::into).collect();
/// let constraint = CardinalityOne::new(lits, LimitComp::LessEq);
/// BitwiseEncoder::default().encode(&mut cnf, &constraint)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
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
