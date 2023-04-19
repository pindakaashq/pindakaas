use iset::{interval_map, IntervalMap};
use itertools::Itertools;

use crate::{
	int::{IntVarEnc, IntVarOrd, LitOrConst, TernLeConstraint, TernLeEncoder},
	linear::LimitComp,
	trace::new_var,
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

		println!(
			"{} {} {}",
			xs.iter().map(|x| format!("{x}")).join(" + "),
			lin.cmp,
			*lin.k
		);

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
                    if lb.end - C::one() >= C::zero() {
                        interval_map! { lb => LitOrConst::Const(true), ub => LitOrConst::Const(false) }
                    } else {
                        interval_map! { ub => LitOrConst::Const(false) }
                    }
				}
				LimitComp::Equal => interval_map! { lb.start..(lb.end - C::one()) => LitOrConst::Const(false), ub => LitOrConst::Const(false) },
			}
		})
		.chain(std::iter::once(match cmp {
			LimitComp::LessEq => {
				interval_map! { neg_inf..C::zero() => LitOrConst::Const(false), C::zero()..k+C::one() => LitOrConst::Const(true), k+C::one()..inf => LitOrConst::Const(false)}
			}
			LimitComp::Equal => interval_map! { neg_inf..k => LitOrConst::Const(false), k..k+C::one() => LitOrConst::Const(true), k+C::one()..inf => LitOrConst::Const(false) },
		}))
		.collect();

	//struct TDB<Lit: Literal> {
	//	nlit: usize,
	//}

	//impl<Lit: Literal + AddAssign + One> ClauseDatabase for TDB<Lit> {
	//	type Lit = Lit;

	//	fn new_var(&mut self) -> Self::Lit {
	//		self.nlit += 1;
	//		self.nlit
	//	}

	//	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
	//		unreachable!()
	//	}
	//}

	bdd(db, 0, xs, C::zero(), &mut ws);
	ws.into_iter()
		.enumerate()
		.map(|(i, w)| {
			let mut views = w.into_iter(..);
			if cmp == &LimitComp::Equal {
				views.next();
			}

			let lb = views
				.find_map(|(iv, lit)| {
					(matches!(lit, LitOrConst::Lit(_) | LitOrConst::Const(true)))
						.then_some(iv.end - C::one())
				})
				.unwrap();

			let mut last_false_iv_start = None;
			let views = views
				.filter(|(iv, _)| iv.end - C::one() >= C::zero())
				.filter_map(|(iv, lit)| match lit {
					LitOrConst::Lit(lit) => {
						if let Some(last_false_iv_start_) = last_false_iv_start {
							last_false_iv_start = None;
							Some((last_false_iv_start_..iv.end, Some(lit)))
						} else {
							Some((iv, Some(lit)))
						}
					}
					LitOrConst::Const(true) => None,
					LitOrConst::Const(false) => {
						if last_false_iv_start.is_none() {
							last_false_iv_start = Some(iv.start);
						}
						None
					}
				})
				.collect::<IntervalMap<_, _>>();

			let y = if views.is_empty() {
				IntVarEnc::Const(lb)
			} else {
				let mut y = IntVarOrd::from_views(db, views, Some(lb), format!("bdd_{i}"));
				y.gapless(); // TODO this indicates we can remove `syms`
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

fn bdd<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	i: usize,
	xs: &Vec<IntVarEnc<DB::Lit, C>>,
	sum: C,
	ws: &mut Vec<IntervalMap<C, LitOrConst<DB::Lit>>>,
) -> (std::ops::Range<C>, LitOrConst<DB::Lit>) {
	match &ws[i].overlap(sum).collect::<Vec<_>>()[..] {
		[] => {
			let dom = xs[i].dom();
			let views = dom
				.iter(..)
				.map(|v| v.end - C::one())
				.map(|v| (v, bdd(db, i + 1, xs, sum + v, ws)))
				.collect::<Vec<_>>();

			let view = (views.iter().map(|(_, (_, lit))| lit).all_equal())
				.then(|| views.first().unwrap().1 .1.clone());

			let interval = views
				.into_iter()
				.map(|(v, (interval, _))| (interval.start - v)..(interval.end - v))
				.reduce(|a, b| std::cmp::max(a.start, b.start)..std::cmp::min(a.end, b.end))
				.unwrap();

			let lit = if let Some(view) = view {
				view
			} else {
				LitOrConst::Lit(new_var!(
					db,
					format!("bdd_{i}>={}..{}", interval.start, interval.end - C::one())
				))
			};

			let new_interval_inserted = ws[i].insert(interval.clone(), lit.clone()).is_none();
			debug_assert!(
				new_interval_inserted,
				"Duplicate interval {interval:?} inserted into {ws:?} layer {i}"
			);
			(interval, lit)
		}
		[(a, lit)] => (a.clone(), lit.clone().clone()),
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
