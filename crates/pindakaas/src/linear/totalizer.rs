pub(crate) use crate::int::IntVar;
use crate::int::Lin;
use crate::int::Model;
use crate::Literal;
use std::cell::RefCell;
use std::rc::Rc;

use itertools::Itertools;

use crate::{
	int::{IntVarEnc, IntVarOrd},
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
			.collect::<Vec<IntVarEnc<DB::Lit, C>>>();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		let mut model = build_totalizer(xs, &lin.cmp, *lin.k);
		model.propagate(false);
		model.encode(db)
	}
}

fn build_totalizer<Lit: Literal, C: Coefficient>(
	xs: Vec<IntVarEnc<Lit, C>>,
	cmp: &LimitComp,
	k: C,
) -> Model<Lit, C> {
	let mut model = Model::new();
	let mut layer = xs
		.into_iter()
		.map(|x| Rc::new(RefCell::new(model.add_int_var_enc(x))))
		.collect::<Vec<_>>();

	while layer.len() > 1 {
		let mut next_layer = Vec::<Rc<RefCell<IntVar<C>>>>::new();
		for children in layer.chunks(2) {
			match children {
				[x] => {
					next_layer.push(x.clone());
				}
				[left, right] => {
					let dom = if layer.len() == 2 {
						vec![k]
					} else {
						left.borrow()
							.dom
							.iter()
							.cartesian_product(right.borrow().dom.iter())
							.map(|(&a, &b)| a + b)
							.sorted()
							.dedup()
							.collect()
					};
					let parent = Rc::new(RefCell::new(model.new_var(dom)));

					model.cons.push(Lin::tern(
						left.clone(),
						right.clone(),
						cmp.clone(),
						parent.clone(),
					));
					next_layer.push(parent);
				}
				_ => panic!(),
			}
		}
		layer = next_layer;
	}

	model
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
