//! At-most-one along a monotone chain (the ladder encoding) [^1].
//!
//! Taking a value is reaching it without reaching the next. Size is linear in
//! the number of literals. Exactly-one fixes both ends of the chain.
//!
//! [^1]: I. P. Gent, P. Nightingale, "A New Encoding of AllDifferent into SAT",
//! ModRef 2004.

use crate::{
	constraint::{linear::LimitComp, cardinality_one::CardinalityOne},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Encoder, Result,
};

/// Ladder at-most-one encoding.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{
///     constraint::{cardinality_one::CardinalityOne, linear::LimitComp},
///     encoder::ladder::LadderEncoder, ClauseDatabase, Cnf, Encoder,
/// };
/// let mut cnf = Cnf::default();
/// let lits = cnf.new_var_range(4).map(Into::into).collect();
/// let constraint = CardinalityOne::new(lits, LimitComp::LessEq);
/// LadderEncoder::default().encode(&mut cnf, &constraint)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LadderEncoder {}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for LadderEncoder {
	#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "ladder_encoder", skip_all, fields(constraint = card1.trace_print()))
)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		// Exactly-one fixes both ends, so constants avoid two unit clauses.
		let equal = card1.cmp == LimitComp::Equal;
		let mut a: BoolVal = if equal {
			true.into()
		} else {
			db.new_lit().into()
		};
		for (i, &x) in card1.lits.iter().enumerate() {
			let last = i + 1 == card1.lits.len();
			let b: BoolVal = if equal && last {
				false.into()
			} else {
				db.new_lit().into()
			};
			db.add_clause([!b, a])?;
			db.add_clause([(!x).into(), a])?;
			db.add_clause([(!x).into(), !b])?;
			db.add_clause([!a, b, x.into()])?;
			a = b;
		}
		// With no literals, the final step is still true and must contradict.
		if equal {
			db.add_clause([!a])?;
		}
		Ok(())
	}
}
