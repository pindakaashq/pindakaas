use iset::{interval_set, IntervalMap, IntervalSet};
use itertools::{Itertools, Position};

use crate::{
	int::{ord_plus_ord_le_ord, IntVar},
	linear::LimitComp,
	new_var, ClauseDatabase, Coefficient, Encoder, Linear, PosCoeff, Result,
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
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		assert!(lin.cmp == LimitComp::LessEq);
		let xs = lin
			.terms
			.iter()
			.map(|part| IntVar::from_part_using_le_ord(db, part, lin.k.clone()))
			.collect::<Vec<_>>();
		let mut ws =
			construct_bdd(db, xs.iter().map(IntVar::ub).collect(), lin.k.clone()).into_iter();
		let first = ws.next().unwrap();
		xs.into_iter().zip(ws).fold(first, |curr, (x_i, next)| {
			if self.add_consistency {
				next.encode_consistency(db);
			}

			ord_plus_ord_le_ord(db, &curr, &x_i, &next);
			next
		});

		Ok(())
	}
}

fn construct_bdd<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	ubs: Vec<PosCoeff<C>>,
	k: PosCoeff<C>,
) -> Vec<IntVar<DB::Lit, C>> {
	let ubs = ubs.into_iter().map(|ub| *ub).collect::<Vec<_>>();
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
			interval_set! { lb, ub }
		})
		.chain(std::iter::once(
			interval_set! { neg_inf..k+C::one(), k+C::one()..inf },
		))
		.collect();
	bdd(0, &ubs, C::zero(), &mut ws);
	ws.into_iter()
		.map(|w| {
			let (mut lb, mut ub) = (-C::one(), -C::one());
			IntVar::new(
				IntervalMap::from_iter(w.into_iter(..).with_position().filter_map(|position| {
					match position {
						Position::First(interval) => {
							lb = std::cmp::max(C::zero(), interval.end - C::one());
							None
						}
						Position::Middle(interval) => Some((interval, new_var!(db))),
						Position::Last(interval) => {
							ub = interval.start - C::one();
							None
						}
						_ => None,
					}
				})),
				lb.into(),
				ub.into(),
			)
		})
		.collect()
}

fn bdd<C: Coefficient>(
	i: usize,
	ubs: &Vec<C>,
	sum: C,
	ws: &mut Vec<IntervalSet<C>>,
) -> std::ops::Range<C> {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let ub = ubs[i];
			let a = bdd(i + 1, ubs, sum, ws);
			let b = bdd(i + 1, ubs, sum + ub, ws);
			let ab = if a == b {
				a.start..(a.end - ub)
			} else {
				let b = (b.start - ub)..(b.end - ub);
				std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end)
			};
			debug_assert!(ws[i].insert(ab.clone()), "Duplicate interval inserted");
			ab
		}
		[interval] => interval.clone(),
		_ => panic!("ROBDD intervals should be disjoint, but were {:?}", ws[i]),
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Checker,
		Encoder,
	};
	linear_test_suite!(BddEncoder::default());
	// FIXME: BDD does not support LimitComp::Equal
	// card1_test_suite!(BddEncoder::default());
}
