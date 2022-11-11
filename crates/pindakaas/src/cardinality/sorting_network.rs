use crate::{
	linear::LimitComp,
	trace::{emit_clause, new_var},
	Cardinality, ClauseDatabase, Coefficient, Encoder, Literal, Result,
};

use itertools::{Itertools, Position};

/// Encoder for the linear constraints that ∑ litsᵢ ≷ k using a sorting network
#[derive(Default)]
pub struct SortingNetworkEncoder {}

use crate::sorted::{Sorted, SortedEncoder};

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> Encoder<DB, Cardinality<DB::Lit, C>>
	for SortingNetworkEncoder
{
	fn encode(&mut self, db: &mut DB, card: &Cardinality<DB::Lit, C>) -> Result {
		let ys = card
			.lits
			.iter()
			.take((*card.k + C::one()).to_usize().unwrap())
			.map(|_x| new_var!(db, format!("y_{_x:?}"))) // TODO: Use label of _x
			.collect::<Vec<_>>();
		let sorted = Sorted::new(card.lits.as_slice(), LimitComp::Equal, &ys);
		SortedEncoder::default().encode(db, &sorted)?;

		if card.cmp == LimitComp::Equal {
			for y in ys.into_iter().with_position() {
				match y {
					Position::First(y) | Position::Middle(y) => emit_clause!(db, &[y])?,
					Position::Only(y) | Position::Last(y) => emit_clause!(db, &[y.negate()])?,
				}
			}
		} else {
			emit_clause!(db, &[ys[ys.len() - 1].negate()])?;
		}
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		cardinality::tests::card_test_suite, helpers::tests::assert_sol, linear::LimitComp,
		Cardinality, Encoder,
	};
	card_test_suite!(SortingNetworkEncoder::default());
}
