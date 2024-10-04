use std::{cell::RefCell, collections::HashMap, ops::Range, rc::Rc};

use iset::IntervalMap;
use itertools::Itertools;

use super::PosCoeff;
use crate::{
	int::{IntVarEnc, Lin, Model},
	linear::LimitComp,
	ClauseDatabase, Coeff, Encoder, Linear, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct BddEncoder {
	add_consistency: bool,
	cutoff: Option<Coeff>,
}

impl BddEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<Coeff>) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl<DB: ClauseDatabase> Encoder<DB, Linear> for BddEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "bdd_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut DB, lin: &Linear) -> Result {
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.flat_map(|(i, part)| IntVarEnc::from_part(db, part, lin.k, format!("x_{i}")))
			.sorted_by(|a: &IntVarEnc, b: &IntVarEnc| b.ub().cmp(&a.ub())) // sort by *decreasing* ub
			.collect_vec();

		let mut model = Model::default();

		let ys = construct_bdd(&xs, &lin.cmp, lin.k);
		let xs = xs
			.into_iter()
			.map(|x| Rc::new(RefCell::new(model.add_int_var_enc(x))))
			.collect_vec();

		let ys = ys
			.into_iter()
			.map(|nodes| {
				let mut views = HashMap::new();
				Rc::new(RefCell::new({
					let mut y = model.new_var(
						nodes
							.into_iter(..)
							.filter_map(|(iv, node)| match node {
								BddNode::Gap => None,
								BddNode::Val => Some(iv.end - 1),
								BddNode::View(view) => {
									let val = iv.end - 1;
									let _ = views.insert(val, view);
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
			.collect_vec();

		let mut ys = ys.into_iter();
		let first = ys.next().unwrap();
		assert!(first.as_ref().borrow().size() == 1);
		let _ = xs.iter().zip(ys).fold(first, |curr, (x_i, next)| {
			model.cons.push(Lin::tern(
				curr,
				Rc::clone(x_i),
				lin.cmp.clone(),
				Rc::clone(&next),
			));
			next
		});

		model.encode(db, self.cutoff)?;
		Ok(())
	}
}

fn construct_bdd(
	xs: &Vec<IntVarEnc>,
	cmp: &LimitComp,
	k: PosCoeff,
) -> Vec<IntervalMap<Coeff, BddNode>> {
	let k = *k;

	let bounds = xs
		.iter()
		.scan((0, 0), |state, x| {
			*state = (state.0 + x.lb(), state.1 + x.ub());
			Some(*state)
		})
		.chain(std::iter::once((0, k)))
		.collect_vec();

	let margins = xs
		.iter()
		.rev()
		.scan((k, k), |state, x| {
			*state = (state.0 - x.ub(), state.1 - x.lb());
			Some(*state)
		})
		.collect_vec();

	let inf = xs.iter().fold(0, |a, x| a + x.ub()) + 1;

	let mut ws = margins
		.into_iter()
		.rev()
		.chain(std::iter::once((k, k)))
		.zip(bounds)
		.map(|((lb_margin, ub_margin), (lb, ub))| {
			match cmp {
				LimitComp::LessEq => vec![
					(lb_margin > lb).then_some((0..(lb_margin + 1), BddNode::Val)),
					(ub_margin <= ub).then_some(((ub_margin + 1)..inf, BddNode::Gap)),
				],
				LimitComp::Equal => vec![
					(lb_margin > lb).then_some((0..lb_margin, BddNode::Gap)),
					(lb_margin == ub_margin).then_some((k..(k + 1), BddNode::Val)),
					(ub_margin <= ub).then_some(((ub_margin + 1)..inf, BddNode::Gap)),
				],
			}
			.into_iter()
			.flatten()
			.collect()
		})
		.collect();

	let _ = bdd(0, xs, 0, &mut ws);
	ws
}

#[derive(Debug, Clone, PartialEq)]
enum BddNode {
	Val,
	Gap,
	View(Coeff),
}

fn bdd(
	i: usize,
	xs: &Vec<IntVarEnc>,
	sum: Coeff,
	ws: &mut Vec<IntervalMap<Coeff, BddNode>>,
) -> (Range<Coeff>, BddNode) {
	match &ws[i].overlap(sum).collect_vec()[..] {
		[] => {
			let views = xs[i]
				.dom()
				.iter(..)
				.map(|v| v.end - 1)
				.map(|v| (v, bdd(i + 1, xs, sum + v, ws)))
				.collect_vec();

			// TODO could we check whether a domain value of x always leads to gaps?
			let is_gap = views.iter().all(|(_, (_, v))| v == &BddNode::Gap);
			// TODO without checking actual Val identity, could we miss when the next layer has two
			// adjacent nodes that are both views on the same node at the layer below?
			let view = (views.iter().map(|(_, (iv, _))| iv).all_equal())
				.then(|| views.first().unwrap().1 .0.end - 1);

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

	use traced_test::test;

	use super::*;
	use crate::helpers::tests::expect_file;
	use crate::{
		helpers::tests::assert_solutions,
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Cnf,
		Encoder,
	};

	linear_test_suite!(BddEncoder::default());
	// FIXME: BDD does not support LimitComp::Equal
	// card1_test_suite!(BddEncoder::default());
}
