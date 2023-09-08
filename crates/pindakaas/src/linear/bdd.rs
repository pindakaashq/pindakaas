use std::{cell::RefCell, collections::HashMap, rc::Rc};

use iset::IntervalMap;
use itertools::Itertools;

use crate::Literal;
#[allow(unused_imports)]
use crate::{
	int::{IntVarEnc, IntVarOrd, Lin, Model},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, PosCoeff, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
#[derive(Default, Clone)]
pub struct BddEncoder<C: Coefficient> {
	add_consistency: bool,
	cutoff: Option<C>,
}

impl<C: Coefficient> BddEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<C>) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl<DB, C> Encoder<DB, Linear<DB::Lit, C>> for BddEncoder<C>
where
	DB: ClauseDatabase,
	C: Coefficient,
{
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "bdd_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.flat_map(|(i, part)| IntVarEnc::from_part(db, part, lin.k.clone(), format!("x_{i}")))
			.sorted_by(|a: &IntVarEnc<_, C>, b: &IntVarEnc<_, C>| b.ub().cmp(&a.ub())) // sort by *decreasing* ub
			.collect::<Vec<_>>();

		let mut model = Model::new();

		let ys = construct_bdd(&xs, &lin.cmp, lin.k.clone());
		let xs = xs
			.into_iter()
			.map(|x| Rc::new(RefCell::new(model.add_int_var_enc(x))))
			.collect::<Vec<_>>();

		// TODO cannot avoid?
		#[allow(clippy::needless_collect)]
		let ys = ys.into_iter()
			.map(|nodes| {
				let mut views = HashMap::new();
				Rc::new(RefCell::new({
					let mut y = model.new_var(
						nodes
							.into_iter(..)
							.filter_map(|(iv, node)| match node {
								BddNode::Gap => None,
								BddNode::Val => Some(iv.end - C::one()),
								BddNode::View(view) => {
									let val = iv.end - C::one();
									views.insert(val, view);
									Some(val)
								}
							})
							.collect(),
						self.add_consistency,
					);
					y.views = views
						.into_iter()
						.map(|(val, view)| (val, (y.id + 1, view)))
						.collect();
					y
				}))
			})
			.collect::<Vec<_>>();

		let mut ys = ys.into_iter();
		let first = ys.next().unwrap();
		assert!(first.as_ref().borrow().size() == 1);
		xs.iter().zip(ys).try_fold(first, |curr, (x_i, next)| {
			model
				.add_constraint(Lin::tern(curr, x_i.clone(), lin.cmp.clone(), next.clone()))
				.map(|_| next)
		})?;

		model.encode(db, self.cutoff)?;
		Ok(())
	}
}

fn construct_bdd<Lit: Literal, C: Coefficient>(
	xs: &Vec<IntVarEnc<Lit, C>>,
	cmp: &LimitComp,
	k: PosCoeff<C>,
) -> Vec<IntervalMap<C, BddNode<C>>> {
	let k = *k;

	let bounds = xs
		.iter()
		.scan((C::zero(), C::zero()), |state, x| {
			*state = (state.0 + x.lb(), state.1 + x.ub());
			Some(*state)
		})
		.chain(std::iter::once((C::zero(), k)))
		.collect::<Vec<_>>();

	// TODO ? also hard to avoid?
	#[allow(clippy::needless_collect)]
	let margins = xs
		.iter()
		.rev()
		.scan((k, k), |state, x| {
			*state = (state.0 - x.ub(), state.1 - x.lb());
			Some(*state)
		})
		.collect::<Vec<_>>();

	let inf = xs.iter().fold(C::zero(), |a, x| a + x.ub()) + C::one();

	let mut ws = margins
		.into_iter()
		.rev()
		.chain(std::iter::once((k, k)))
		.zip(bounds)
		.map(|((lb_margin, ub_margin), (lb, ub))| {
			match cmp {
				LimitComp::LessEq => vec![
					(lb_margin > lb).then_some((C::zero()..(lb_margin + C::one()), BddNode::Val)),
					(ub_margin <= ub).then_some(((ub_margin + C::one())..inf, BddNode::Gap)),
				],
				LimitComp::Equal => vec![
					(lb_margin > lb).then_some((C::zero()..lb_margin, BddNode::Gap)),
					(lb_margin == ub_margin).then_some((k..(k + C::one()), BddNode::Val)),
					(ub_margin <= ub).then_some(((ub_margin + C::one())..inf, BddNode::Gap)),
				],
			}
			.into_iter()
			.flatten()
			.collect()
		})
		.collect();

	bdd(0, xs, C::zero(), &mut ws);
	ws
}

#[derive(Debug, Clone, PartialEq)]
enum BddNode<C: Coefficient> {
	Val,
	Gap,
	View(C),
}

fn bdd<Lit: Literal, C: Coefficient>(
	i: usize,
	xs: &Vec<IntVarEnc<Lit, C>>,
	sum: C,
	ws: &mut Vec<IntervalMap<C, BddNode<C>>>,
) -> (std::ops::Range<C>, BddNode<C>) {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let views = xs[i]
				.dom()
				.iter(..)
				.map(|v| v.end - C::one())
				.map(|v| (v, bdd(i + 1, xs, sum + v, ws)))
				.collect::<Vec<_>>();

			// TODO could we check whether a domain value of x always leads to gaps?
			let is_gap = views.iter().all(|(_, (_, v))| v == &BddNode::Gap);
			// TODO without checking actual Val identity, could we miss when the next layer has two
			// adjacent nodes that are both views on the same node at the layer below?
			let view = (views.iter().map(|(_, (iv, _))| iv).all_equal())
				.then(|| views.first().unwrap().1 .0.end - C::one());

			let interval = views
				.into_iter()
				.map(|(v, (interval, _))| (interval.start - v)..(interval.end - v))
				.reduce(|a, b| std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end))
				.unwrap();

			let node = if is_gap {
				BddNode::Gap
			} else if let Some(view) = view {
				BddNode::View(view)
			} else {
				BddNode::Val
			};

			let new_interval_inserted = ws[i].insert(interval.clone(), node.clone()).is_none();
			debug_assert!(
				new_interval_inserted,
				"Duplicate interval {interval:?} inserted into {ws:?} layer {i}"
			);
			(interval, node)
		}
		[(a, node)] => (a.clone(), (*node).clone()),
		_ => panic!("ROBDD intervals should be disjoint, but were {:?}", ws[i]),
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
		Encoder,
	};
	linear_test_suite!(BddEncoder::default());
	// FIXME: BDD does not support LimitComp::Equal
	// card1_test_suite!(BddEncoder::default());
}
