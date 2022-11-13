use crate::{
	linear::LimitComp,
	trace::{emit_clause, new_var},
	Cardinality, ClauseDatabase, Coefficient, Encoder, Literal, Result,
};

use itertools::{Itertools, Position};

/// Encoder for the linear constraints that ∑ litsᵢ ≷ k using a sorting network
#[derive(Default)]
pub struct SortingNetworkEncoder {
	add_consistency: bool,
}

impl SortingNetworkEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
}

use crate::sorted::{Sorted, SortedEncoder};

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Cardinality<DB::Lit, C>>
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
		SortedEncoder::default()
			.add_consistency(self.add_consistency)
			.encode(db, &sorted)?;

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
		cardinality::tests::card_test_suite, cardinality_one::tests::card1_test_suite,
		helpers::tests::assert_sol, linear::LimitComp, Cardinality, CardinalityOne, Encoder,
	};
	card1_test_suite!(SortingNetworkEncoder::default());
	card_test_suite!(SortingNetworkEncoder::default());
}
