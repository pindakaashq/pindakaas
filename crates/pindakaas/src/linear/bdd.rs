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

		let mut ys = (0..lin.exp.terms.len())
			.map(|i| rest(&lin, i))
			.chain(std::iter::once((C::zero(), C::zero())))
			.map(|(inner_lb, inner_ub)| (lin.k - inner_ub, lin.k - inner_lb)) // find inner bounds
			.into_iter()
			.zip(
				lin.exp
					.terms
					.iter()
					.map(|term| (term.lb(), term.ub()))
					.chain(std::iter::once((C::zero(), lin.k)))
					.scan((C::zero(), C::zero()), |state, (lb, ub)| {
						*state = (state.0 + lb, state.1 + ub);
						Some(*state)
					}),
			)
			.map(|((inner_lb, inner_ub), (outer_lb, outer_ub))| {
				match lin.cmp {
					Comparator::LessEq => vec![
						(outer_lb..=inner_lb, BddNode::Val),
						(inner_ub + C::one()..=outer_ub, BddNode::Gap),
					],
					Comparator::Equal => {
						vec![
							(outer_lb..=(inner_lb - C::one()), BddNode::Gap),
							(inner_ub..=inner_lb, BddNode::Val),
							((inner_ub + C::one())..=outer_ub, BddNode::Gap),
						]
					}
					Comparator::GreaterEq => {
						vec![
							(outer_lb..=(inner_lb - C::one()), BddNode::Gap),
							(inner_ub..=outer_ub, BddNode::Val),
						]
					}
				}
				.into_iter()
				.filter(|(iv, _)| !iv.is_empty())
				.map(|(iv, node)| {
					let (lb, ub) = iv.into_inner();
					(lb..(ub + C::one()), node)
				})
				.collect::<IntervalMap<_, _>>()
			})
			.collect::<Vec<_>>();

		bdd(0, &lin.exp.terms, C::zero(), &mut ys);

		// TODO cannot avoid?
		#[allow(clippy::needless_collect)]
		let ys = ys.into_iter()
			.enumerate()
			.flat_map(|(i, nodes)| {
				let mut views = HashMap::new();
				let dom = nodes
					.into_iter(..)
					.filter_map(|(iv, node)| match node {
						BddNode::Val => Some(iv.end - C::one()),
						BddNode::Gap => None,
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
					.add_constraint(Lin::tern(term.clone(), curr, lin.cmp, next.clone(), None))
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

		let decomposition = self.decompose::<DB::Lit>(
			Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None),
			model.num_var,
		)?;


		model.extend(decomposition);

		model.encode(db, self.cutoff)?;
		Ok(())
	}
}


/// m(i) = ∑_i^n ( ub(x_i), lb(x_i) )
fn rest<C: Coefficient>(lin: &Lin<C>, i: usize) -> (C, C) {
	(
		lin.exp.terms[i..]
			.iter()
			.map(|term| term.lb())
			.fold(C::zero(), C::add),
		lin.exp.terms[i..]
			.iter()
			.map(|term| term.ub())
			.fold(C::zero(), C::add),
	)
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
			let children = dom
				.iter()
				.map(|v| (v, bdd(i + 1, xs, sum + *v, ws)))
				.collect::<Vec<_>>();

			let is_gap = children.iter().all(|(_, (_, v))| v == &BddNode::Gap);

			let view = (children.iter().map(|(_, (iv, _))| iv).all_equal())
				.then(|| children.first().unwrap().1 .0.end - C::one());

			let iv = children
				.into_iter()
				.map(|(v, (iv, _))| (iv.start - *v)..(iv.end - *v))
				.reduce(|a, b| std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end))
				.unwrap();

			let node = if is_gap {
				BddNode::Gap
			} else if let Some(view) = view {
				BddNode::View(view)
			} else {
				BddNode::Val
			};

			assert!(
				ws[i].insert(iv.clone(), BddNode::Val).is_none(),
				"Duplicate interval {iv:?} inserted into {ws:?} layer {i}"
			);
			(iv, node)
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
