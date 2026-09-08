//! At-most-one along a monotone chain, so that taking a value is reaching it
//! without reaching the next.

use crate::{
	constraint::{linear::LimitComp, cardinality_one::CardinalityOne},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Encoder, Result,
};

/// Encoder for an at-most-one constraint, as a ladder of commander literals.
///
/// One literal per position saying whether the chain has come down by there,
/// so a literal taking its value is that step and no other. Linear in the
/// number of literals, where the pairwise encoding is quadratic.
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
		// For an Exactly One constraint the ladder is known to start out `true`
		// and to have come down by the end, so both ends are constants rather
		// than literals that would only be fixed by a unit clause.
		let equal = card1.cmp == LimitComp::Equal;
		let mut a: BoolVal = if equal {
			true.into()
		} else {
			db.new_lit().into()
		}; // y_v-1
		for (i, &x) in card1.lits.iter().enumerate() {
			let last = i + 1 == card1.lits.len();
			let b: BoolVal = if equal && last {
				false.into()
			} else {
				db.new_lit().into()
			}; // y_v
			db.add_clause([!b, a])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			db.add_clause([(!x).into(), a])?; // x_v -> y_v-1
			db.add_clause([(!x).into(), !b])?; // x_v -> ¬y_v
			db.add_clause([!a, b, x.into()])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		// The ladder has to have come down by the end of an Exactly One
		// constraint. Its final step is already the constant `false` whenever
		// there was at least one literal, so this only has an effect when there
		// were none at all, where it reports that nothing can be selected.
		if equal {
			db.add_clause([!a])?;
		}
		Ok(())
	}
}
