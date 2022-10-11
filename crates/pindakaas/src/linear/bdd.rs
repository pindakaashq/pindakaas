use crate::{
	int::{ord_plus_ord_le_ord, ord_plus_ord_le_ord_sparse_dom, IntVar},
	linear::LimitComp,
	new_var, ClauseDatabase, Coefficient, Encoder, Linear, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
#[derive(Default, Clone)]
pub struct BddEncoder {
	add_consistency: bool,
}

impl BddEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for BddEncoder {
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		assert!(lin.cmp == LimitComp::LessEq);
		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)]
		let xs = lin.terms
			.iter()
			.map(|part| IntVar::from_part_using_le_ord(db, part, lin.k.clone()))
			.collect::<Vec<_>>();
		xs.into_iter().enumerate().reduce(|(i, v_i), (_, x_i)| {
			let parent = IntVar::new(
				ord_plus_ord_le_ord_sparse_dom(
					v_i.iter().map(|(_, c)| *c).collect(),
					x_i.iter().map(|(_, c)| *c).collect(),
					C::zero(),
					*lin.k,
				)
				.into_iter()
				.map(|c| (c.into(), new_var!(db, format!("w_{}>={:?}", i + 1, c))))
				.collect(),
				C::zero().into(),
				lin.k.clone(),
			);

			if self.add_consistency {
				parent.encode_consistency(db);
			}

			ord_plus_ord_le_ord(db, &v_i, &x_i, &parent);
			(i + 1, parent)
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
	linear_test_suite!(BddEncoder::default());
	// FIXME: BDD does not support LimitComp::Equal
	// card1_test_suite!(BddEncoder::default());
}
