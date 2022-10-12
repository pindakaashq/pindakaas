use iset::{interval_set, IntervalMap, IntervalSet};

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
		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)]
		let xs = lin.terms
			.iter()
			.map(|part| IntVar::from_part_using_le_ord(db, part, lin.k.clone()))
			.collect::<Vec<_>>();
		let ws = construct_bdd(db, xs.iter().map(IntVar::ub).collect(), lin.k.clone());
		xs.into_iter().zip(ws.into_iter()).fold(
			IntVar::constant(C::zero().into()),
			|curr, (x_i, next)| {
				if self.add_consistency {
					next.encode_consistency(db);
				}

				ord_plus_ord_le_ord(db, &curr, &x_i, &next);
				next
			},
		);

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
	let inf = ubs.iter().fold(C::one(), |a, &b| (a + b));
	let neg_inf = k - inf;

	let mut ws = ubs
		.iter()
		.enumerate()
		.map(|(i, _)| {
			let lb = neg_inf..(ubs[i..].iter().fold(k + C::one(), |acc, ub| acc - *ub));
			let ub = (k + C::one())..inf;
			interval_set! { lb, ub }
		})
		.chain(std::iter::once(
			interval_set! { neg_inf..k+C::one(), k+C::one()..inf },
		))
		.collect();
	bdd(0, &ubs, C::zero(), &mut ws);
	ws.pop();
	for w in &mut ws {
		w.remove((k + C::one())..(k + C::one() + C::one()));
	}

	ws.into_iter()
		.zip(ubs.into_iter())
		.map(|(w, ub)| {
			let mut it = w.into_iter(..);
			let lb = std::cmp::max(C::zero(), it.next().unwrap().end);
			let xs = IntervalMap::from_sorted(it.map(|interval| (interval, new_var!(db))));
			IntVar::new(xs, lb.into(), ub.into())
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
				a.start..a.end.checked_sub(&ub).unwrap_or_else(C::zero)
			} else {
				let b = b.start.checked_sub(&ub).unwrap_or_else(C::zero)
					..b.end.checked_sub(&ub).unwrap_or_else(C::zero);
				std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end)
			};
			debug_assert!(ws[i].insert(ab.clone()), "Duplicate interval inserted");
			ab
		}
		[interval] => interval.clone(),
		_ => panic!(),
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
