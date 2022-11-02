use crate::{
	int::{ord_plus_ord_le_ord_sparse_dom, IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	trace::new_var,
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
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
			.map(|part| IntVarEnc::Ord(IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone())))
			.collect::<Vec<_>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		build_totalizer(xs, db, C::zero(), *lin.k.clone(), self.add_consistency, 0)
	}
}

#[allow(clippy::only_used_in_recursion)]
fn build_totalizer<DB: ClauseDatabase, C: Coefficient>(
	mut layer: Vec<IntVarEnc<DB::Lit, C>>,
	db: &mut DB,
	l: C,
	u: C,
	add_consistency: bool,
	// level is only used for output variable name output
	level: u32,
) -> Result {
	if layer.len() == 1 {
		let root = layer.pop().unwrap();
		let zero = IntVarEnc::Const(C::zero());
		let parent = IntVarEnc::Const(u);
		TernLeEncoder::default().encode(
			db,
			&TernLeConstraint::new(&root, &zero, LimitComp::LessEq, &parent),
		)
	} else {
		let next_layer = layer
			.chunks(2)
			.enumerate()
			.map(|(_node, children)| match children {
				[x] => x.clone(),
				[left, right] => {
					let l = if layer.len() > 2 { C::zero() } else { l };
					let dom = ord_plus_ord_le_ord_sparse_dom(
						left.dom().into_iter(..).map(|c| c.end - C::one()).collect(),
						right
							.dom()
							.into_iter(..)
							.map(|c| c.end - C::one())
							.collect(),
						l,
						u,
					)
					.into_iter(..)
					.map(|interval| {
						let var =
							new_var!(db, format!("w_{}_{}>={:?}", level + 1, _node + 1, interval));
						(interval, Some(var))
					})
					.collect();

					let parent = IntVarEnc::Ord(IntVarOrd::new(db, dom));

					// if add_consistency {
					// 	encode_consistency(db, &parent).unwrap();
					// }

					TernLeEncoder::default()
						.encode(
							db,
							&TernLeConstraint::new(left, right, LimitComp::LessEq, &parent),
						)
						.unwrap();
					parent
				}
				_ => panic!(),
			})
			.collect();
		build_totalizer(next_layer, db, l, u, add_consistency, level + 1)
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
