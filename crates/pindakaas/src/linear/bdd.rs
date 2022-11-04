use iset::{interval_map, IntervalMap};
use itertools::{Itertools, Position};

use crate::{
	int::{IntVarEnc, IntVarOrd, LitOrConst, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	trace::new_var,
	ClauseDatabase, Coefficient, Encoder, Linear, PosCoeff, Result,
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
		assert!(lin.cmp == LimitComp::LessEq);
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone(), format!("x_{i}")).into()
			})
			.sorted_by(|a: &IntVarEnc<_, C>, b: &IntVarEnc<_, C>| b.ub().cmp(&a.ub())) // sort by *decreasing* ub
			.collect::<Vec<_>>();
		let mut ws = construct_bdd(db, &xs, lin.k.clone(), self.add_consistency).into_iter();
		let first = ws.next().unwrap();
		xs.iter().zip(ws).fold(first, |curr, (x_i, next)| {
			TernLeEncoder::default()
				.encode(
					db,
					&TernLeConstraint::new(&curr, x_i, LimitComp::LessEq, &next),
				)
				.unwrap();
			next
		});

		Ok(())
	}
}

fn construct_bdd<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	xs: &Vec<IntVarEnc<DB::Lit, C>>,
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
			interval_map! { lb => LitOrConst::Const(true), ub => LitOrConst::Const(false) }
		})
		.chain(std::iter::once(
			interval_map! { neg_inf..k+C::one() => LitOrConst::Const(true) , k+C::one()..inf => LitOrConst::Const(false) },
		))
		.collect();
	bdd(db, 0, xs, C::zero(), &mut ws, true);
	ws.into_iter()
		.enumerate()
		.with_position()
		.filter_map(|w| {
			// TODO refactor by directly converting Const layers into Constants (regardless of position)
			match w {
				Position::First(_) => Some(IntVarEnc::Const(C::zero())),
				Position::Middle((i, w)) => {
					let dom: IntervalMap<_, _> = w
						.into_iter(..)
						.tuple_windows()
						.filter_map(|((prev, _), (iv, lit))| {
							let interval = prev.end..iv.end;
							match lit {
								LitOrConst::Lit(lit) => Some((interval, Some(lit))),
								LitOrConst::Const(false) => None,
								_ => unreachable!(),
							}
						})
						.collect();
					if dom.is_empty() {
						None
					} else {
						let x = IntVarOrd::new(db, dom, format!("bdd_{i}"));
						if add_consistency {
							x.consistent(db).unwrap();
						}
						Some(IntVarEnc::Ord(x))
					}
				}
				Position::Last(_) => Some(IntVarEnc::Const(k)),
				Position::Only(_) => unreachable!(),
			}
		})
		.collect()
}

fn bdd<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	i: usize,
	xs: &Vec<IntVarEnc<DB::Lit, C>>,
	sum: C,
	ws: &mut Vec<IntervalMap<C, LitOrConst<DB::Lit>>>,
	first: bool,
) -> (std::ops::Range<C>, LitOrConst<DB::Lit>) {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let interval = xs[i]
				.dom()
				.iter(..)
				.map(|v| {
					let v = v.end - C::one();
					let (interval, lit) = bdd(db, i + 1, xs, sum + v, ws, false);
					((interval.start - v)..(interval.end - v), lit)
				})
				.reduce(|(a, _), (b, lit_b)| {
					(
						std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end),
						lit_b,
					)
				})
				.unwrap()
				.0;
			let lit = if first {
				LitOrConst::Const(true)
			} else {
				LitOrConst::Lit(new_var!(db, format!("bdd_{i}>={interval:?}")))
			};

			let interval_already_exists = ws[i].insert(interval.clone(), lit.clone()).is_some();
			debug_assert!(!interval_already_exists, "Duplicate interval inserted");
			(interval, lit)
		}
		[(a, lit)] => (a.clone(), (*lit).clone()),
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
		Checker,
		Encoder,
	};
	linear_test_suite!(BddEncoder::default());
	// FIXME: BDD does not support LimitComp::Equal
	// card1_test_suite!(BddEncoder::default());
}
