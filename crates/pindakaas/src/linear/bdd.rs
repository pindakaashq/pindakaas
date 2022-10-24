use iset::{interval_map, IntervalMap};
use itertools::{Itertools, Position};

use crate::{
	int::{encode_consistency, ord_plus_ord_le_x, Constant, IntVarEnc, IntVarOrd, LitOrConst},
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

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> Encoder<DB, Linear<DB::Lit, C>>
	for BddEncoder
{
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		assert!(lin.cmp == LimitComp::LessEq);
		let xs = lin
			.terms
			.iter()
			.map(|part| -> Box<dyn IntVarEnc<DB, C>> {
				Box::new(IntVarOrd::from_part_using_le_ord(db, part, lin.k.clone()))
			})
			.sorted_by(|a, b| b.ub().cmp(&a.ub())) // sort by *decreasing* ub
			.collect::<Vec<_>>();
		let mut ws = construct_bdd(db, &xs, lin.k.clone()).into_iter();
		let first = ws.next().unwrap();
		xs.into_iter().zip(ws).fold(first, |curr, (x_i, next)| {
			if self.add_consistency {
				encode_consistency(db, &next);
			}

			ord_plus_ord_le_x(db, &curr, &x_i, &next);
			next
		});

		Ok(())
	}
}

fn construct_bdd<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
	db: &mut DB,
	xs: &Vec<Box<dyn IntVarEnc<DB, C>>>,
	k: PosCoeff<C>,
) -> Vec<Box<dyn IntVarEnc<DB, C>>> {
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
		.with_position()
		.filter_map(|w| -> Option<Box<dyn IntVarEnc<DB, C>>> {
			// TODO refactor by directly converting Const layers into Constants (regardless of position)
			match w {
				Position::First(_) => Some(Box::new(Constant::new(C::zero()))),
				Position::Middle(w) => {
					let dom: IntervalMap<_, _> = w
						.into_iter(..)
						.tuple_windows()
						.filter_map(|((prev, _), (iv, lit))| {
							let interval = (prev.end - C::one())..iv.end;
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
						Some(Box::new(IntVarOrd::new(db, dom)))
					}
				}
				Position::Last(_) => Some(Box::new(Constant::new(k))),
				Position::Only(_) => unreachable!(),
			}
		})
		.collect()
}

fn bdd<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
	db: &mut DB,
	i: usize,
	xs: &Vec<Box<dyn IntVarEnc<DB, C>>>,
	sum: C,
	ws: &mut Vec<IntervalMap<C, LitOrConst<DB::Lit>>>,
	first: bool,
) -> (std::ops::Range<C>, LitOrConst<DB::Lit>) {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let (interval, lit) = (
				xs[i]
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
					.0,
				if first {
					LitOrConst::Const(true)
				} else {
					LitOrConst::Lit(new_var!(db))
				},
			);

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
