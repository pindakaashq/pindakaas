use crate::{
	int::{
		next_int_var, ord_plus_ord_le_ord_sparse_dom, Constant, IntVarEnc, IntVarOrd,
		TernLeConstraint, TernLeEncoder,
	},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
#[derive(Clone, Default)]
pub struct TotalizerEncoder<C: Coefficient> {
	add_consistency: bool,
	cutoff: C,
}

impl<C: Coefficient> TotalizerEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: C) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> Encoder<DB, Linear<DB::Lit, C>>
	for TotalizerEncoder<C>
{
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		assert!(lin.cmp == LimitComp::LessEq);

		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| -> Box<dyn IntVarEnc<DB::Lit, C>> {
				Box::new(IntVarOrd::from_part_using_le_ord(
					db,
					part,
					lin.k.clone(),
					format!("x_{i}"),
				))
			})
			.collect::<Vec<_>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		self.build_totalizer(
			// xs.iter().map(Box::as_ref).collect(),
			xs,
			db,
			C::zero(),
			*lin.k.clone(),
			0,
		)
	}
}

impl<C: Coefficient + 'static> TotalizerEncoder<C> {
	fn build_totalizer<DB: ClauseDatabase + 'static>(
		&self,
		mut layer: Vec<Box<dyn IntVarEnc<DB::Lit, C>>>,
		db: &mut DB,
		l: C,
		u: C,
		level: u32,
	) -> Result {
		if layer.len() == 1 {
			TernLeEncoder::default().encode(
				db,
				&TernLeConstraint::new(
					layer.pop().unwrap().as_ref(),
					&Constant::new(C::zero()),
					LimitComp::LessEq,
					&Constant::new(u),
				),
			)
		} else {
			let next_layer = layer
				.chunks(2)
				.enumerate()
				.map(|(node, children)| -> Box<dyn IntVarEnc<DB::Lit, C>> {
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
							);

							let parent = next_int_var(
								db,
								dom,
								self.cutoff,
								self.add_consistency,
								format!("gt_{level}_{node}"),
							);

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
			self.build_totalizer(next_layer, db, l, u, level + 1)
		}
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
