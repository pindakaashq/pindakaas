use std::{collections::HashMap, ops::Range};

use iset::IntervalMap;
use itertools::Itertools;

use crate::{
	int::{Decompose, IntVar},
	Comparator, Decomposer, Literal, ModelConfig, Unsatisfiable,
};
#[allow(unused_imports)]
use crate::{
	int::{IntVarEnc, IntVarOrd, Lin, LinExp, Model, Term},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, PosCoeff, Result,
};

#[allow(dead_code)]
enum BddSort {
	Asc,
	Dsc,
	None,
}

const SORT_TERMS: BddSort = BddSort::Dsc;

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

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for BddEncoder<C> {
	fn decompose(&self, mut model: Model<Lit, C>) -> Result<Model<Lit, C>, Unsatisfiable> {
		assert!(model.cons.len() == 1);
		let lin = model.cons.pop().unwrap();

		// traditionally, sort by *decreasing* ub
		let lin = Lin {
			exp: LinExp {
				terms: lin
					.exp
					.terms
					.iter()
					.cloned()
					.sorted_by_key(|term| match SORT_TERMS {
						BddSort::Dsc => -term.ub(),
						BddSort::Asc => term.ub(),
						BddSort::None => C::zero(),
					})
					.collect(),
			},
			..lin
		};

		// Ex. 2 x1 {0,2} + 3 x2 {0,3} + 5 x3 {0,5} <= 6
		// NOTE: Example assumes `SORT_TERMS = false`

		// We calculate the bounds of the partial sum
		// Ex. [(0,0), (0,2), (0,5), (0,10)]
		let mut ys = std::iter::once((C::zero(), C::zero()))
			.chain(
				lin.exp
					.terms
					.iter()
					.map(|term| (term.lb(), term.ub()))
					.scan((C::zero(), C::zero()), |state, (lb, ub)| {
						*state = (state.0 + lb, state.1 + ub);
						Some(*state)
					}),
			)
			.map(|(outer_lb, outer_ub)| {
				// From each outer bound, we can calculate the distance to k as k - (UB - ub)
				// Ex. [ k - (10,0), k - (8,0), k - (5,0), k - (0,0) ] // remaining weight for each term
				//       = [ (-4,6), (-2, 6), (1, 6), (0,6) ] // distance to k
				let (inner_lb, inner_ub) = (
					(lin.k - (lin.ub() - outer_ub)),
					(lin.k - (lin.lb() - outer_lb)),
				);

				// The distance to k determines sat/unsat (1/0 terminal)
				// And the outer bounds are used as plus/minus-infinity
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
					// Turn inclusive ranges into regular ranges for IntervalMap
					let (lb, ub) = iv.into_inner();
					(lb..(ub + C::one()), node)
				})
				.collect::<IntervalMap<_, _>>()
			})
			.collect::<Vec<_>>();
		// Ex. base case:
		// []
		// []
		// [0..1 => Val]
		// [0..6 => Val, 7..10 => Gap]

		// Construct BDD
		// Ex.
		// [0..0 => Val]
		// [0..1 => Val, 2..2 => Val]
		// [0..1 => Val, 2..5 => Val]
		// [0..6 => Val, 7..10 => Gap]
		bdd(0, &lin.exp.terms, &lin.cmp, C::zero(), &mut ys);

		// Turn BDD into integer variables and constraints
		// Ex.
		// x1 ∈ {0,2} + y_0 ∈ {0} ≤ y_1 ∈ {1,2}
		// x2 ∈ {0,3} + y_1 ∈ {1,2} ≤ y_2 ∈ {1,5}
		// x3 ∈ {0,5} + y_2 ∈ {1,5} ≤ y_3 ∈ {6}
		// TODO since both borrow model, I don't know how to avoid needless_collect
		#[allow(clippy::needless_collect)]
		let ys = ys.into_iter()
			.enumerate()
			.flat_map(|(i, nodes)| {
				let mut views = HashMap::new();

				let dom = nodes
					.into_iter(..)
					.filter_map(|(iv, node)| match node {
						BddNode::Val => Some(process_val(iv, &lin.cmp)),
						BddNode::Gap => None,
						BddNode::View(view) => {
							let val = process_val(iv, &lin.cmp);
							views.insert(val, view);
							Some(val)
						}
					})
					.collect::<Vec<_>>();
				model
					.new_var(
						&dom,
						model.config.add_consistency,
						None,
						Some(format!("bdd_{}", i + 1)),
					)
					.map(|var| (var, views))
			})
			.collect::<Vec<_>>()
			.into_iter()
			.chain([(model.new_constant(C::zero()), HashMap::default())]) // Ensure final element is not cut off by tuple_windows
			.tuple_windows()
			.map(|((y, views), (y_next, _))| {
				// Views are always from one y to the next
				y.borrow_mut().views = views
					.into_iter()
					.map(|(val, view)| (val, (y_next.borrow().id, view)))
					.collect();
				y
			})
			.map(Term::from)
			.collect::<Vec<_>>();

		let mut ys = ys.into_iter();
		if let Some(first) = ys.next() {
			assert!(first.size() == C::one());

			lin.exp.terms.iter().zip(ys).enumerate().try_fold(
				first,
				|curr, (i, (term, next))| {
					model
						.add_constraint(
							Lin::tern(
								term.clone(),
								curr,
								lin.cmp,
								next.clone(),
								lin.lbl.as_ref().map(|lbl| format!("bdd_{}_{}", i + 1, lbl)),
							), // TODO .simplified()?,
						)
						.map(|_| next)
				},
			)?;
		}

		Ok(model)
	}
}

fn process_val<C: Coefficient>(iv: Range<C>, cmp: &Comparator) -> C {
	match cmp {
		Comparator::LessEq | Comparator::Equal => iv.end - C::one(),
		Comparator::GreaterEq => iv.start,
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
		let mut model = Model {
			config: ModelConfig {
				cutoff: self.cutoff,
				add_consistency: self.add_consistency,
				decomposer: Decomposer::Bdd,
				..ModelConfig::default()
			},
			..Model::default()
		};

		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVar::from_part(db, &mut model, part, lin.k.clone(), format!("x_{i}"))
					.map(Term::from)
			})
			.collect::<Result<Vec<_>, _>>()?;

		// TODO pass BDD::decompose to Model::encode instead, since otherwise we risk decomposing twice
		let mut model = self.decompose(Model {
			cons: vec![Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None)],
			..model
		})?;

		// model.extend(decomposition);

		model.encode(db, false)?;
		Ok(())
	}
}

#[derive(Debug, Clone, PartialEq)]
enum BddNode<C: Coefficient> {
	Val,
	Gap,
	View(C),
}

fn bdd<Lit: Literal, C: Coefficient>(
	i: usize,
	xs: &Vec<Term<Lit, C>>,
	_cmp: &Comparator,
	sum: C,
	ws: &mut Vec<IntervalMap<C, BddNode<C>>>,
) -> (std::ops::Range<C>, BddNode<C>) {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let dom = xs[i].dom();
			let children = dom
				.iter()
				.map(|v| (v, bdd(i + 1, xs, _cmp, sum + *v, ws)))
				.collect::<Vec<_>>();

			let is_gap = children.iter().all(|(_, (_, v))| v == &BddNode::Gap);

			let view = None;
			// (children
			// .iter()
			// .flat_map(|(_, (iv, v))| (v == &BddNode::Val).then_some(iv))
			// .all_equal() && false)
			// .then(|| process_val(children.first().unwrap().1 .0.clone(), cmp));

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
				ws[i].insert(iv.clone(), node.clone()).is_none(),
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
