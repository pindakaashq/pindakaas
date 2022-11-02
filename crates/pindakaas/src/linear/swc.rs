use crate::{
	int::{IntVarOrd, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
};
use iset::IntervalMap;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
#[derive(Clone, Default)]
pub struct SwcEncoder {
	add_consistency: bool,
}

impl SwcEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
}

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> Encoder<DB, Linear<DB::Lit, C>>
	for SwcEncoder
{
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)]
		let xs = lin.terms
			.iter()
			.map(|part| Box::new(IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone())))
			.collect::<Vec<_>>();
		xs.into_iter().enumerate().reduce(|(i, prev), (_, leaf)| {
			let dom = num::iter::range_inclusive(C::one(), *lin.k)
				.map(|j| (j..(j + C::one()), None))
				.collect::<IntervalMap<_, _>>();

			let next = IntVarOrd::new(db, dom, format!("w_{}", i + 1));
			if self.add_consistency {
				next.consistent(db).unwrap();
			}
			let next = Box::new(next);

			TernLeEncoder::default()
				.encode(
					db,
					&TernLeConstraint::new(
						prev.as_ref(),
						leaf.as_ref(),
						LimitComp::LessEq,
						next.as_ref(),
					),
				)
				.unwrap();

			(i + 1, next)
		});
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Checker, Encoder,
	};

	linear_test_suite!(SwcEncoder::default());
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
