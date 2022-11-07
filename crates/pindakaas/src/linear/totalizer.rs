use crate::{
	int::{
		next_int_var, ord_plus_ord_le_ord_sparse_dom, IntVarEnc, IntVarOrd, TernLeConstraint,
		TernLeEncoder,
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

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for TotalizerEncoder<C> {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		assert!(lin.cmp == LimitComp::LessEq);

		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone(), format!("x_{i}")).into()
			})
			.collect::<Vec<_>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		let root = build_totalizer(
			xs,
			db,
			C::zero(),
			*lin.k.clone(),
			0,
			self.add_consistency,
			self.cutoff,
		);

		TernLeEncoder::default().encode(
			db,
			&TernLeConstraint::new(
				&root,
				&IntVarEnc::Const(C::zero()),
				LimitComp::LessEq,
				&IntVarEnc::Const(*lin.k),
			),
		)
	}
}

pub(crate) fn build_totalizer<DB: ClauseDatabase, C: Coefficient>(
	mut layer: Vec<IntVarEnc<DB::Lit, C>>,
	db: &mut DB,
	l: C,
	u: C,
	level: u32,
	add_consistency: bool,
	cutoff: C,
) -> IntVarEnc<DB::Lit, C> {
	if layer.len() == 1 {
		layer.pop().unwrap()
	} else {
		let next_layer = layer
			.chunks(2)
			.enumerate()
			.map(|(node, children)| match children {
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
					);

					let parent = next_int_var(
						db,
						dom,
						cutoff,
						add_consistency,
						format!("gt_{level}_{node}"),
					);

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
		build_totalizer(next_layer, db, l, u, level + 1, add_consistency, cutoff)
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
