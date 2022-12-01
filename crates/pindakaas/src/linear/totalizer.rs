use crate::{
	int::{ord_plus_ord_le_ord, ord_plus_ord_le_ord_sparse_dom, IntVar},
	linear::LimitComp,
	trace::new_var,
	ClauseDatabase, Coefficient, Encoder, Linear, PosCoeff, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
#[derive(Clone, Default)]
pub struct TotalizerEncoder {
	add_consistency: bool,
}

impl TotalizerEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for TotalizerEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		assert!(lin.cmp == LimitComp::LessEq);
		let xs = lin
			.terms
			.iter()
			.map(|part| IntVar::from_part_using_le_ord(db, part, lin.k.clone()))
			.collect::<Vec<_>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		build_totalizer(
			xs,
			db,
			C::zero().into(),
			lin.k.clone(),
			true,
			self.add_consistency,
		);
		Ok(())
	}
}

fn build_totalizer<DB: ClauseDatabase + ?Sized, C: Coefficient>(
	mut layer: Vec<IntVar<DB::Lit, C>>,
	db: &mut DB,
	l: PosCoeff<C>,
	u: PosCoeff<C>,
	limit_root: bool,
	add_consistency: bool,
) -> IntVar<DB::Lit, C> {
	if layer.len() == 1 {
		let root = layer.pop().unwrap();
		if limit_root {
			let zero = IntVar::constant(C::zero().into());
			let parent = IntVar::constant(u);
			ord_plus_ord_le_ord(db, &root, &zero, &parent);
		}
		root
	} else if limit_root && layer.len() == 2 {
		let parent = IntVar::constant(u);
		ord_plus_ord_le_ord(db, &layer[0], &layer[1], &parent);
		parent
	} else {
		build_totalizer(
			layer
				.chunks(2)
				.enumerate()
				.map(|(_node, children)| match children {
					[x] => x.clone(),
					[left, right] => {
						let l = if layer.len() > 2 {
							C::zero().into()
						} else {
							l.clone()
						};
						let parent = IntVar::from_terms(
							ord_plus_ord_le_ord_sparse_dom(
								left.iter().map(|(_, c)| *c).collect(),
								right.iter().map(|(_, c)| *c).collect(),
								*l,
								*u,
							)
							.into_iter()
							.map(|c| {
								(
									c.into(),
									new_var!(db, format!("w_{}_{}>={c:?}", level + 1, _node + 1)),
								)
							})
							.collect(),
							l,
							u.clone(),
						);

						if add_consistency {
							parent.encode_consistency(db);
						}

						ord_plus_ord_le_ord(db, left, right, &parent);
						parent
					}
					_ => panic!(),
				})
				.collect(),
			db,
			l,
			u,
			limit_root,
			add_consistency,
		)
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

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

	linear_test_suite!(TotalizerEncoder::default());
	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
}
