use crate::{
	int::{
		ord_plus_ord_le_ord_sparse_dom, Constant, IntVarEnc, IntVarOrd, TernLeConstraint,
		TernLeEncoder,
	},
	linear::LimitComp,
	new_var, ClauseDatabase, Coefficient, Encoder, Linear, Result,
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

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> Encoder<DB, Linear<DB::Lit, C>>
	for TotalizerEncoder
{
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		assert!(lin.cmp == LimitComp::LessEq);

		let xs = lin
			.terms
			.iter()
			.map(|part| -> Box<dyn IntVarEnc<DB::Lit, C>> {
				Box::new(IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone()))
			})
			.collect::<Vec<_>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		build_totalizer(
			// xs.iter().map(Box::as_ref).collect(),
			xs,
			db,
			C::zero(),
			*lin.k.clone(),
			self.add_consistency,
			0,
		)
	}
}

fn build_totalizer<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
	mut layer: Vec<Box<dyn IntVarEnc<DB::Lit, C>>>,
	db: &mut DB,
	l: C,
	u: C,
	add_consistency: bool,
	level: u32,
) -> Result {
	if layer.len() == 1 {
		let root = layer.pop().unwrap();
		let zero = Constant::new(C::zero());
		let parent = Constant::new(u);
		TernLeEncoder::default().encode(
			db,
			&TernLeConstraint::new(root.as_ref(), &zero, LimitComp::LessEq, &parent),
		)
	} else {
		let next_layer = layer
			.chunks(2)
			.enumerate()
			.map(|(_node, children)| -> Box<dyn IntVarEnc<DB::Lit, C>> {
				match children {
					[x] => x.clone_dyn(),
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
							#[cfg(debug_assertions)]
							let lbl = format!("w_{}_{}>={:?}", level + 1, _node + 1, interval);
							(interval, Some(new_var!(db, lbl)))
						})
						.collect();

						let parent: Box<dyn IntVarEnc<DB::Lit, C>> =
							Box::new(IntVarOrd::new(db, dom));

						// if add_consistency {
						// 	encode_consistency(db, parent.as_ref()).unwrap();
						// }

						TernLeEncoder::default()
							.encode(
								db,
								&TernLeConstraint::new(
									left.as_ref(),
									right.as_ref(),
									LimitComp::LessEq,
									parent.as_ref(),
								),
							)
							.unwrap();
						parent
					}
					_ => panic!(),
				}
			})
			.collect();
		build_totalizer(next_layer, db, l, u, add_consistency, level + 1)
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

	linear_test_suite!(TotalizerEncoder::default());
	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
}
