use crate::{
	int::{ord_plus_ord_le_x, IntVar},
	new_var, ClauseDatabase, Coefficient, Encoder, Linear, Result,
};

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

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for SwcEncoder {
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)]
		let xs = lin.terms
			.iter()
			.map(|part| IntVar::from_part_using_le_ord(db, part, lin.k.clone()))
			.collect::<Vec<_>>();
		xs.into_iter().enumerate().reduce(|(i, prev), (_, leaf)| {
			let next = IntVar::from_terms(
				num::iter::range_inclusive(C::one(), *lin.k)
					.map(|j| (j.into(), new_var!(db, format!("w_{}>={:?}", i + 1, j))))
					.collect(),
				C::zero().into(),
				lin.k.clone(),
			);

			if self.add_consistency {
				next.encode_consistency(db);
			}

			ord_plus_ord_le_x(db, &prev, &leaf, &next);
			(i + 1, next)
		});
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Checker,
		Encoder,
	};

	linear_test_suite!(SwcEncoder::default());
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
