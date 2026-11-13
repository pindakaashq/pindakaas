//! At-most-one along a monotone chain (the ladder encoding) [^1].
//!
//! Taking a value is reaching it without reaching the next. Size is linear in
//! the number of literals. Exactly-one fixes both ends of the chain.
//!
//! [^1]: I. P. Gent, P. Nightingale, "A New Encoding of AllDifferent into SAT",
//! ModRef 2004.

use crate::{
	constraint::{
		cardinality_one::CardinalityOne,
		implied::{negated, Implied},
		linear::LimitComp,
	},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Encoder, Lit, Result,
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

impl LadderEncoder {
	/// The ladder for `card1`, where under a `condition` only the clauses that
	/// state the constraint take its negation.
	///
	/// Each step `a` holds exactly where a literal from here on does, which
	/// defines it; that a literal rules out every later one, and under `=` that
	/// some literal holds, state the constraint.
	fn ladder<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		card1: &CardinalityOne,
		condition: Option<Lit>,
	) -> Result {
		let negated = negated(condition);
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
			db.add_clause([(!x).into(), !b, negated])?;
			// Under `=` the first step is true, so its clause states that some
			// literal holds.
			let states = if equal && i == 0 {
				negated
			} else {
				false.into()
			};
			db.add_clause([!a, b, x.into(), states])?;
			a = b;
		}
		// With no literals, the final step is still the first one, which no
		// literal can make true.
		if equal {
			db.add_clause([!a])?;
		}
		Ok(())
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for LadderEncoder {
	#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "ladder_encoder", skip_all, fields(constraint = card1.trace_print()))
)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		Self::ladder(db, card1, None)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Implied<CardinalityOne, Lit>> for LadderEncoder {
	fn encode(&self, db: &mut Db, con: &Implied<CardinalityOne, Lit>) -> Result {
		con.encode_with(db, |db, con, r| Self::ladder(db, con, Some(r)))
	}
}
