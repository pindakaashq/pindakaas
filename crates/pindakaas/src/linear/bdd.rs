use iset::{interval_set, IntervalSet};
use itertools::Itertools;

use crate::{
	int::{IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	ClauseDatabase, Coefficient, Encoder, Linear, Literal, PosCoeff, Result,
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

		// TODO add consistency
		let mut ws = ws.into_iter();
		let first = ws.next().unwrap();
		xs.iter().zip(ws).fold(first, |curr, (x_i, next)| {
			let c = TernLeConstraint::new(&curr, x_i, lin.cmp.clone(), &next);
			TernLeEncoder::default().encode(db, &c).unwrap();
			next
		});

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
	let ubs = xs.iter().map(|x| x.ub()).collect::<Vec<_>>();
	let k = *k;
	let inf = ubs.iter().fold(C::one() + C::one(), |a, &b| (a + b));
	let neg_inf = k - inf;

	let mut ws = ubs
		.iter()
		.enumerate()
		.map(|(i, _)| {
			// TODO optimize
			let lb = neg_inf..ubs[i..].iter().fold(k + C::one(), |acc, ub| acc - *ub);
			let ub = (k + C::one())..inf;
			match cmp {
				LimitComp::LessEq => {
					interval_set! { lb, ub }
				}
				LimitComp::Equal => interval_set! { lb.start..(lb.end - C::one()), ub },
			}
		})
		.chain(std::iter::once(match cmp {
			LimitComp::LessEq => {
				interval_set! { neg_inf..C::zero(), C::zero()..k+C::one(), k+C::one()..inf }
			}
			LimitComp::Equal => interval_set! { neg_inf..k, k..k+C::one(), k+C::one()..inf },
		}))
		.collect();
	bdd(0, xs, C::zero(), &mut ws);
	ws.into_iter()
		.enumerate()
		.map(|(i, w)| {
			let mut dom = w.into_iter(..);
			if cmp == &LimitComp::Equal {
				dom.next();
			}

			let dom = dom
				.map(|iv| iv.end - C::one())
				.filter(|c| c >= &C::zero())
				.collect::<Vec<_>>();
			let dom = &dom[..(dom.len() - 1)];
			let y = IntVarEnc::from_dom(db, dom, format!("bdd_{i}")).unwrap();
			if add_consistency {
				y.consistent(db).unwrap();
			}
			y
		})
		.collect()
}

fn bdd<Lit: Literal, C: Coefficient>(
	i: usize,
	xs: &Vec<IntVarEnc<Lit, C>>,
	sum: C,
	ws: &mut Vec<IntervalSet<C>>,
) -> std::ops::Range<C> {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let interval = xs[i]
				.dom()
				.iter(..)
				.map(|v| {
					let v = v.end - C::one();
					let interval = bdd(i + 1, xs, sum + v, ws);
					(interval.start - v)..(interval.end - v)
				})
				.reduce(|a, b| std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end))
				.unwrap();
			let new_interval_inserted = ws[i].insert(interval.clone());
			debug_assert!(
				new_interval_inserted,
				"Duplicate interval {interval:?} inserted into {ws:?} layer {i}"
			);
			interval
		}
		[a] => a.clone(),
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
