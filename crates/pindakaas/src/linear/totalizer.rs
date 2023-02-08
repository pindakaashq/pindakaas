//use iset::{interval_set, IntervalSet};
use itertools::Itertools;

use crate::{
	int::{
		next_int_var, IntVarEnc, IntVarOrd, TernLeConstraint,
		TernLeEncoder,
	},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
#[derive(Clone, Default)]
pub struct TotalizerEncoder<C: Coefficient> {
	add_consistency: bool,
	cutoff: Option<C>,
}

impl<C: Coefficient> TotalizerEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<C>) -> &mut Self {
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

		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone(), format!("x_{i}")).into()
			})
			.collect::<Vec<_>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		build_totalizer(
			xs,
			db,
			&lin.cmp,
			C::zero(),
			0,
			self.add_consistency,
			None,
			IntVarEnc::Const(*lin.k),
		);
		Ok(())
	}
}

pub(crate) fn build_totalizer<DB: ClauseDatabase, C: Coefficient>(
	layer: Vec<IntVarEnc<DB::Lit, C>>,
	db: &mut DB,
	cmp: &LimitComp,
	l: C,
	level: u32,
	add_consistency: bool,
	cutoff: Option<C>,
	root: IntVarEnc<DB::Lit, C>,
) -> IntVarEnc<DB::Lit, C> {
	if layer.len() == 1 {
		root
	} else {
		let next_layer = layer
			.chunks(2)
			.enumerate()
			.map(|(node, children)| {
				let doms = match &children.iter().map(|x| x.dom().clone()).collect::<Vec<_>>()[..] {
					[x] => x.clone(),
					[left, right] => {
						if layer.len() > 2 {
							left.iter(..)
								.cartesian_product(right.iter(..))
								.map(|(a, b)| a.end - C::one() + b.end - C::one())
                                .filter(|&d| d <= root.ub())
								.sorted()
                                .dedup()
								.tuple_windows()
								.map(|(a, b)| (a + C::one())..(b + C::one()))
								.collect()
						} else {
							root.dom()
						}
					}
					_ => panic!(),
				};
				(children, doms)
			})
			.collect::<Vec<_>>();

		let next_layer = next_layer
			.into_iter()
			.map(|(children, dom)| match children {
				[x] => x.clone(),
				[left, right] => {
					let parent = next_int_var(
						db,
						dom.clone(),
						cutoff,
						add_consistency,
						format!("gt_{level}"),
					);

					TernLeEncoder::default()
						.encode(
							db,
							&TernLeConstraint::new(&left, &right, cmp.clone(), &parent),
						)
						.unwrap();
					parent
				}
				_ => unreachable!(),
			})
			.collect::<Vec<_>>();

		build_totalizer(
			next_layer,
			db,
			cmp,
			l,
			level + 1,
			add_consistency,
			cutoff,
			root,
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
		helpers::tests::{assert_sol, TestDB},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Comparator,
		Encoder,
		LinExp,
		LinearAggregator,
		LinearConstraint,
		SortedEncoder,
	};

	#[test]
	fn test_sort_same_coefficients_2() {
		use crate::linear::{LinearEncoder, StaticLinEncoder};
		use crate::{Checker, Encoder};
		let mut db = TestDB::new(5);
		let mut agg = LinearAggregator::default();
		agg.sort_same_coefficients(SortedEncoder::default(), 3);
		let mut encoder = LinearEncoder::<StaticLinEncoder<TotalizerEncoder<i32>>>::default();
		encoder.add_linear_aggregater(agg);
		let con = LinearConstraint::new(
			LinExp::new() + (1, 3) + (2, 3) + (3, 1) + (4, 1) + (5, 3),
			Comparator::GreaterEq,
			2,
		);
		assert!(encoder.encode(&mut db, &con).is_ok());
		db.with_check(|sol| {
			{
				let con = LinearConstraint::new(
					LinExp::new() + (1, 3) + (2, 3) + (3, 1) + (4, 1) + (5, 3),
					Comparator::GreaterEq,
					2,
				);
				con.check(sol)
			}
			.is_ok()
		})
		.check_complete()
	}

	linear_test_suite!(TotalizerEncoder::default());
	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
}
