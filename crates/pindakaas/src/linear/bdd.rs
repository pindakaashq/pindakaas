use std::{collections::HashMap, ops::Range};

use iset::IntervalMap;
use itertools::Itertools;

use crate::{
	int::{Dom, Lin, LinExp, Model},
	ClauseDatabase, Coeff, Comparator, Decompose, Decomposer, Encoder, IntVar, Linear, ModelConfig,
	Result, Term, Unsatisfiable,
};

#[allow(dead_code)]
enum BddSort {
	Asc,  // Bad
	Dsc,  // Good
	None, // useful for debugging
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq)]
enum BddNode {
	Val,
	Gap,
	View(Coeff),
}

/// Determine sorting order of terms (useful for debugging)
const SORT_TERMS: BddSort = BddSort::Dsc;

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

impl Decompose for BddEncoder {
	fn decompose(&self, mut model: Model) -> Result<Model, Unsatisfiable> {
		assert!(model.cons.len() == 1);
		let lin = model.cons.pop().unwrap();

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
						BddSort::None => 0,
					})
					.collect(),
			},
			..lin
		};

		// Ex. 2 x1 {0,2} + 3 x2 {0,3} + 5 x3 {0,5} <= 6
		// NOTE: Example assumes `SORT_TERMS = BddSort::None`

		// We calculate the bounds of the partial sum
		// Ex. [(0,0), (0,2), (0,5), (0,10)]
		let mut ys = std::iter::once((0, 0))
			.chain(
				lin.exp
					.terms
					.iter()
					.map(|term| (term.lb(), term.ub()))
					.scan((0, 0), |state, (lb, ub)| {
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
						((inner_ub + 1)..=outer_ub, BddNode::Gap),
					],
					Comparator::Equal => {
						vec![
							(outer_lb..=(inner_lb - 1), BddNode::Gap),
							(inner_ub..=inner_lb, BddNode::Val),
							((inner_ub + 1)..=outer_ub, BddNode::Gap),
						]
					}
					Comparator::GreaterEq => {
						vec![
							(outer_lb..=(inner_lb - 1), BddNode::Gap),
							(inner_ub..=outer_ub, BddNode::Val),
						]
					}
				}
				.into_iter()
				.filter(|(iv, _)| !iv.is_empty())
				.map(|(iv, node)| {
					// Turn inclusive ranges into regular ranges for IntervalMap
					let (lb, ub) = iv.into_inner();
					(lb..(ub + 1), node)
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
		bdd(0, &lin.exp.terms, &lin.cmp, 0, &mut ys);

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
					.new_aux_var(
						Dom::from_slice(&dom),
						model.config.add_consistency,
						None,
						Some(format!("bdd_{}", i + 1)),
					)
					.map(|var| (var, views))
			})
			.collect::<Vec<_>>()
			.into_iter()
			.chain([(model.new_constant(0), HashMap::default())]) // Ensure final element is not cut off by tuple_windows
			.tuple_windows()
			.map(|((y, _views), (_y_next, _))| {
				// Views are always from one y to the next
				// TODO reimplement partial views
				// y.borrow_mut().views = views
				// 	.into_iter()
				// 	.map(|(val, view)| (val, (y_next.borrow().id, view)))
				// 	.collect();
				y
			})
			.map(Term::from)
			.collect::<Vec<_>>();

		let mut ys = ys.into_iter();
		if let Some(first) = ys.next() {
			assert!(first.size() == 1);

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

fn process_val(iv: Range<Coeff>, cmp: &Comparator) -> Coeff {
	match cmp {
		Comparator::LessEq | Comparator::Equal => iv.end - 1,
		Comparator::GreaterEq => iv.start,
	}
}

impl<DB: ClauseDatabase> Encoder<DB, Linear> for BddEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "bdd_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]

	fn encode(&self, db: &mut DB, lin: &Linear) -> Result {
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
				IntVar::from_part(db, &mut model, part, lin.k, format!("x_{i}")).map(Term::from)
			})
			.collect::<Result<Vec<_>, _>>()?;

		// TODO pass BDD::decompose to Model::encode instead, since otherwise we risk decomposing twice
		let mut model = self.decompose(Model {
			cons: vec![Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None)],
			..model
		})?;

		model.encode_internal(db, false)?;
		Ok(())
	}
}

fn bdd(
	i: usize,
	xs: &Vec<Term>,
	_cmp: &Comparator,
	sum: Coeff,
	ws: &mut Vec<IntervalMap<Coeff, BddNode>>,
) -> (std::ops::Range<Coeff>, BddNode) {
	// TODO assert at most one (this was the last case, but seemed to impact performance in profiling!)
	match &ws[i].overlap(sum).next() {
		None => {
			let (iv, node) = xs[i]
				.dom()
				.iter()
				.map(|v| (v, bdd(i + 1, xs, _cmp, sum + *v, ws)))
				.map(|(v, (iv, n))| ((iv.start - *v)..(iv.end - *v), n))
				.reduce(|(iv_a, n_a), (iv_b, n_b)| {
					(
						std::cmp::max(iv_a.start, iv_b.start)..std::cmp::min(iv_a.end, iv_b.end),
						if n_a == BddNode::Val { n_a } else { n_b },
					)
				})
				.unwrap();
			let duplicate = ws[i].insert(iv.clone(), node.clone());
			debug_assert!(
				duplicate.is_none(),
				"Duplicate interval {iv:?} inserted into {ws:?} layer {i}"
			);
			(iv, node)
		}
		Some((a, node)) => (a.clone(), (*node).clone()),
		// _ => panic!("ROBDD intervals should be disjoint, but were {:?}", ws[i]),
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		helpers::tests::{assert_sol, lits},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, PosCoeff,
		},
		Encoder, Lit,
	};
	linear_test_suite!(BddEncoder::default());
}
