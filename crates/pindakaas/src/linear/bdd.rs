use std::collections::HashMap;

use iset::IntervalMap;
use itertools::Itertools;

#[allow(unused_imports)]
use crate::{
	int::{IntVarEnc, IntVarOrd, Lin, LinExp, Model, Term},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, PosCoeff, Result,
};
use crate::{Comparator, Literal, Unsatisfiable};

const SORT_TERMS: bool = true;

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

	pub(crate) fn decompose<Lit: Literal>(
		&mut self,
		lin: Lin<C>,
		num_var: usize,
	) -> crate::Result<Model<Lit, C>, Unsatisfiable> {
		let mut model = Model::<Lit, C>::new(num_var);

		// sort by *decreasing* ub

		let lin = if SORT_TERMS {
			Lin {
				exp: LinExp {
					terms: lin
						.exp
						.terms
						.iter()
						.cloned()
						.sorted_by(|a: &Term<C>, b: &Term<C>| b.ub().cmp(&a.ub()))
						.collect(),
				},
				..lin
			}
		} else {
			lin
		};

		let ys = construct_bdd(&lin);

		// TODO cannot avoid?
		#[allow(clippy::needless_collect)]
		let ys = ys.into_iter()
			.enumerate()
			.flat_map(|(i, nodes)| {
				let mut views = HashMap::new();
				let dom = nodes
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
					.collect::<Vec<_>>();
				model
					.new_var(&dom, self.add_consistency, Some(format!("bdd_{}", i)))
					.map(|y| {
						y.borrow_mut().views = views
							.into_iter()
							.map(|(val, view)| (val, (y.borrow().id + 1, view)))
							.collect();
						y
					})
			})
			.map(Term::from)
			.collect::<Vec<_>>();

		let mut ys = ys.into_iter();
		let first = ys.next().unwrap();
		assert!(first.size() == 1);
		lin.exp
			.terms
			.iter()
			.zip(ys)
			.try_fold(first, |curr, (term, next)| {
				model
					.add_constraint(Lin::tern(curr, term.clone(), lin.cmp, next.clone(), None))
					.map(|_| next)
			})?;

		Ok(model)
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
		let mut model = Model::default();
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.flat_map(|(i, part)| IntVarEnc::from_part(db, part, lin.k.clone(), format!("x_{i}")))
			.flat_map(|x| model.add_int_var_enc(x))
			.map(Term::from)
			.collect::<Vec<_>>();

		model.extend(self.decompose::<DB::Lit>(
			Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None),
			model.num_var,
		)?);

		model.encode(db, self.cutoff)?;
		Ok(())
	}
}

fn construct_bdd<C: Coefficient>(lin: &Lin<C>) -> Vec<IntervalMap<C, BddNode<C>>> {
	// Ex. 2 x1 {0,2} + 3 x2 {0,3} + 5 x3 {0,5} <= 6
	// Calculate the lower and upper bounds of the first i terms ++ (0,k)
	// Ex. [(0,2), (0,5), (0,10), (0,6)]
	let bounds = lin
		.exp
		.terms
		.iter()
		.scan((C::zero(), C::zero()), |state, term| {
			*state = (state.0 + term.lb(), state.1 + term.ub());
			Some(*state)
		})
		.chain(std::iter::once((C::zero(), lin.k)))
		.collect::<Vec<_>>();

	// TODO ? also hard to avoid?
	// Calculate the margin for the partial sum up to term i before we get UNSAT/SAT
	// Ex. [(1,6), (-2,6), (-4,6) ]
	//  (-2,6) means at the 2nd term, the sum cannot exceed 6 (otherwise, it's UNSAT), and cannot be less than 2 (otherwise it's SAT; if the partial sum is 1, we cannot violate the constraint with only have 5 left in the last term)
	#[allow(clippy::needless_collect)]
	let margins = lin
		.exp
		.terms
		.iter()
		.rev()
		.scan((lin.k, lin.k), |state, term| {
			*state = (state.0 - term.ub(), state.1 - term.lb());
			Some(*state)
		})
		.collect::<Vec<_>>();

	let (neg_inf, pos_inf) = (lin.lb() - C::one(), lin.ub() + C::one());

	let mut ws = margins
		.into_iter()
		.rev()
		.chain(std::iter::once((lin.k, lin.k)))
		.zip(bounds)
		.map(|((lb_margin, ub_margin), (lb, ub))| {
			match lin.cmp {
				Comparator::LessEq => vec![
					(lb_margin > lb).then_some((neg_inf..(lb_margin + C::one()), BddNode::Val)),
					(ub_margin <= ub).then_some(((ub_margin + C::one())..pos_inf, BddNode::Gap)),
				],
				Comparator::Equal => vec![
					(lb_margin > lb).then_some((neg_inf..lb_margin, BddNode::Gap)),
					(lb_margin == ub_margin).then_some((lin.k..(lin.k + C::one()), BddNode::Val)),
					(ub_margin <= ub).then_some(((ub_margin + C::one())..pos_inf, BddNode::Gap)),
				],
				Comparator::GreaterEq => vec![
					(ub_margin < ub).then_some(((lb_margin + C::one())..pos_inf, BddNode::Gap)),
					(lb_margin >= lb).then_some((neg_inf..(lb_margin + C::one()), BddNode::Val)),
				],
			}
			.into_iter()
			.flatten()
			.collect()
		})
		.collect();

	bdd(0, &lin.exp.terms, C::zero(), &mut ws);
	ws
}

#[derive(Debug, Clone, PartialEq)]
enum BddNode<C: Coefficient> {
	Val,
	Gap,
	View(C),
}

fn bdd<C: Coefficient>(
	i: usize,
	xs: &Vec<Term<C>>,
	sum: C,
	ws: &mut Vec<IntervalMap<C, BddNode<C>>>,
) -> (std::ops::Range<C>, BddNode<C>) {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let dom = xs[i].dom();
			let views = dom
				.iter()
				.map(|v| (v, bdd(i + 1, xs, sum + *v, ws)))
				.collect::<Vec<_>>();

			// TODO could we check whether a domain value of x always leads to gaps?
			let is_gap = views.iter().all(|(_, (_, v))| v == &BddNode::Gap);
			// TODO without checking actual Val identity, could we miss when the next layer has two
			// adjacent nodes that are both views on the same node at the layer below?
			let view = (views.iter().map(|(_, (iv, _))| iv).all_equal())
				.then(|| views.first().unwrap().1 .0.end - C::one());

			let interval = views
				.into_iter()
				.map(|(v, (interval, _))| (interval.start - *v)..(interval.end - *v))
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
