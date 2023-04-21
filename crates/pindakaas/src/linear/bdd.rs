use std::{cell::RefCell, rc::Rc};

use iset::{interval_map, IntervalMap};
use itertools::Itertools;

#[allow(unused_imports)]
use crate::{
	int::{IntVarEnc, IntVarOrd, Lin, Model},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Consistency, Encoder, Linear, PosCoeff, Result,
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
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "bdd_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone(), format!("x_{i}")).into()
			})
			.sorted_by(|a: &IntVarEnc<_, C>, b: &IntVarEnc<_, C>| b.ub().cmp(&a.ub())) // sort by *decreasing* ub
			.collect::<Vec<_>>();

		let ws = construct_bdd(db, &xs, &lin.cmp, lin.k.clone(), self.add_consistency);

		let mut model = Model::new();

		let xs = xs
			.into_iter()
			.map(|x| Rc::new(RefCell::new(model.add_int_var_enc(x))))
			.collect::<Vec<_>>();

		let ws = ws
			.into_iter()
			.map(|w| Rc::new(RefCell::new(model.add_int_var_enc(w))))
			.collect::<Vec<_>>();

		// TODO add consistency
		let mut ws = ws.into_iter();
		let first = ws.next().unwrap();
		xs.iter().zip(ws).fold(first, |curr, (x_i, next)| {
			model.cons.push(Lin::tern(
				curr.clone(),
				x_i.clone(),
				lin.cmp.clone(),
				next.clone(),
			));
			next
		});

		//let add_propagation = Consistency::Bounds;
		//let size = model.size();
		//model.propagate(&add_propagation, vec![model.cons.len() - 1]);
		//assert!(size - model.size() == 0);
		//println!("{} - {} = {}", size, model.size(), size - model.size());
		model.encode(db)?;
		Ok(())
	}
}

fn construct_bdd<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	xs: &Vec<IntVarEnc<DB::Lit, C>>,
	cmp: &LimitComp,
	k: PosCoeff<C>,
	add_consistency: bool,
) -> Vec<IntVarEnc<DB::Lit, C>> {
	let k = *k;

	let bounds = xs
		.iter()
		.scan((C::zero(), C::zero()), |state, x| {
			*state = (state.0 + x.lb(), state.1 + x.ub());
			Some(*state)
		})
		.chain(std::iter::once((
			match cmp {
				LimitComp::LessEq => C::zero(),
				LimitComp::Equal => C::zero(),
			},
			k,
		)))
		.collect::<Vec<_>>();

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
		.chain(std::iter::once((
			match cmp {
				LimitComp::LessEq => k,
				LimitComp::Equal => k,
			},
			k,
		)))
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

	bdd(db, 0, xs, C::zero(), &mut ws);

	ws.into_iter()
		.enumerate()
		.map(|(i, nodes)| {


			let mut last_false_iv_start = None;
			let nodes = nodes
				.into_iter(..)
				.filter(|(iv, _)| iv.end - C::one() >= C::zero())
				.filter_map(|(iv, node)| match node {
					BddNode::View(_) | BddNode::Val => {
						if let Some(last_false_iv_start_) = last_false_iv_start {
							last_false_iv_start = None;
							Some((last_false_iv_start_..iv.end, Some(node)))
						} else {
							Some((iv, Some(node)))
						}
					}
					BddNode::Gap => {
						if last_false_iv_start.is_none() {
							last_false_iv_start = Some(iv.start);
						}
						None
					}
				})
				.collect::<IntervalMap<_, _>>();

			dbg!(&nodes);
			let y = if nodes.len() == 1 {
				IntVarEnc::Const(nodes.into_iter(..).next().unwrap().0.end - C::one())
			} else {
				let y = IntVarOrd::from_dom(
					db,
					&nodes
						.intervals(..)
						.map(|c| c.end - C::one())
						.collect::<Vec<_>>()[..],
					None,
					format!("bdd_{i}"),
				);
				let y = IntVarEnc::Ord(y);

				if add_consistency {
					y.consistent(db).unwrap();
				}
				y
			};
			y
		})
		.collect()
}

#[derive(Debug, Clone, PartialEq)]
enum BddNode<C: Coefficient> {
	Val,
	Gap,
	View(C),
}

fn bdd<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	i: usize,
	xs: &Vec<IntVarEnc<DB::Lit, C>>,
	sum: C,
	ws: &mut Vec<IntervalMap<C, BddNode<C>>>,
) -> (std::ops::Range<C>, BddNode<C>) {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let dom = xs[i].dom();
			let views = dom
				.iter(..)
				.map(|v| v.end - C::one())
				.map(|v| (v, bdd(db, i + 1, xs, sum + v, ws)))
				.collect::<Vec<_>>();

			let view = (views.iter().map(|(_, (iv, _))| iv).all_equal())
				.then(|| views.first().unwrap().1 .0.end - C::one());

			let interval = views
				.into_iter()
				.map(|(v, (interval, _))| (interval.start - v)..(interval.end - v))
				.reduce(|a, b| std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end))
				.unwrap();

			let node = if let Some(view) = view {
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
		[(a, node)] => (a.clone(), node.clone().clone()),
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
