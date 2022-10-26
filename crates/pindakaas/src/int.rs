use iset::IntervalMap;
use itertools::Itertools;

use crate::{linear::Part, new_var, ClauseDatabase, Coefficient, Literal, PosCoeff};
use std::{
	collections::{HashMap, HashSet},
	ops::Neg,
};

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LitOrConst<Lit: Literal> {
	Lit(Lit),
	Const(bool),
}

impl<Lit: Literal> Neg for LitOrConst<Lit> {
	type Output = Self;

	fn neg(self) -> Self {
		match self {
			Self::Lit(lit) => Self::Lit(lit.negate()),
			Self::Const(b) => Self::Const(!b),
		}
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Debug, Clone)]
pub(crate) struct IntVar<Lit: Literal, C: Coefficient> {
	xs: IntervalMap<C, Lit>,
	lb: PosCoeff<C>,
	ub: PosCoeff<C>,
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> for IntVar<Lit, C> {
	fn lb(&self) -> &C {
		&self.lb
	}

	fn ub(&self) -> &C {
		&self.ub
	}

	// TODO return ref
	// TODO impl Index
	fn eq(&self, _: &C) -> Vec<LitOrConst<Lit>> {
		todo!();
	}

	fn geq(&self, v: &C) -> Option<Vec<Lit>> {
		if v <= self.lb() {
			None
		} else if v > self.ub() {
			Some(vec![])
		} else {
			match self.xs.overlap(*v).collect::<Vec<_>>()[..] {
				[(_, x)] => Some(vec![x.clone()]),
				_ => panic!("No or multiples variables at {v:?} in {self:?}"),
			}
		}
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Clone, Debug)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	xs: Vec<Lit>,
	lb: C,
	ub: C,
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> for IntVarBin<Lit, C> {
	fn lb(&self) -> &C {
		&self.lb
	}

	fn ub(&self) -> &C {
		&self.ub
	}

	// TODO return ref
	// TODO impl Index
	fn geq(&self, v: &C) -> Option<Vec<Lit>> {
		let mut v = *v;
		v.unsigned_shl(v.trailing_zeros());
		let mut vs: Vec<Lit> = vec![];
		let mut i = 0;
		loop {
			vs.push(self.xs[i].clone());
			v = v.signed_shl(v.signed_shl(1).trailing_zeros() + 1); // TODO not sure if better than just shifting one at a time
			i += v.trailing_zeros() as usize;
			if i >= self.xs.len() {
				return Some(vs);
			}
		}
	}

	fn eq(&self, _: &C) -> Vec<LitOrConst<Lit>> {
		todo!();
	}
}
impl<Lit: Literal, C: Coefficient> IntVar<Lit, C> {
	pub fn new(xs: IntervalMap<C, Lit>, lb: PosCoeff<C>, ub: PosCoeff<C>) -> Self {
		debug_assert!(*lb <= *ub);
		Self { xs, lb, ub }
	}

	pub fn from_terms(terms: Vec<(PosCoeff<C>, Lit)>, lb: PosCoeff<C>, ub: PosCoeff<C>) -> Self {
		// TODO perhaps lb/ub should always be equal to min/max of terms
		debug_assert!(*lb <= *ub);
		Self {
			xs: IntervalMap::from_sorted(
				terms
					.into_iter()
					.map(|(coef, lit)| (*coef..(*coef + C::one()), lit)),
			),
			lb,
			ub,
		}
	}

	pub fn constant(c: PosCoeff<C>) -> Self {
		Self {
			xs: IntervalMap::new(),
			lb: c.clone(),
			ub: c,
		}
	}

	pub fn iter(&self) -> impl Iterator<Item = (LitOrConst<Lit>, PosCoeff<C>)> + '_ {
		std::iter::once((LitOrConst::Const(true), self.lb.clone())).chain(
			self.xs
				.iter(..)
				.map(|(c, l)| (LitOrConst::Lit(l.clone()), (c.end - C::one()).into())),
		)
	}

	pub fn encode_consistency<DB: ClauseDatabase<Lit = Lit> + ?Sized>(&self, db: &mut DB) {
		self.iter()
			.tuple_windows()
			.skip(1)
			.for_each(|((lit_a, _), (lit_b, _))| {
				// TODO clean up
				if let LitOrConst::Lit(a) = lit_a {
					if let LitOrConst::Lit(b) = lit_b {
						db.add_clause(&[b.negate(), a]).unwrap();
					} else {
						panic!();
					}
				} else {
					panic!();
				}
			});
	}

	/// Constructs IntVar `y` for linear expression `xs` so that ∑ xs ≦ y, using order encoding
	pub fn from_part_using_le_ord<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		xs: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
	) -> Self {
		// TODO add_consistency on coupled leaves (wherever not equal to principal vars)
		// if add_consistency {
		// 	for leaf in &leaves {
		// 		leaf.encode_consistency(db);
		// 	}
		// }

		// couple given encodings to the order encoding
		// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

		match xs {
			Part::Amo(terms) => {
				let terms: Vec<(PosCoeff<C>, DB::Lit)> = terms
					.iter()
					.map(|(lit, coef)| (coef.clone(), lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: HashMap<C, Vec<DB::Lit>> = HashMap::with_capacity(terms.len());
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(*coef).or_insert_with(Vec::new).push(lit);
				}

				let xs = h
					.into_iter()
					.map(|(coef, lits)| -> (PosCoeff<C>, _) {
						if lits.len() == 1 {
							(coef.into(), lits[0].clone())
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								db.add_clause(&[lit.negate(), o.clone()]).unwrap();
							}
							(coef.into(), o)
						}
					})
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					.collect::<Vec<(_, _)>>();

				let ub = xs
					.iter()
					.map(|(c, _)| (*c.clone()))
					.max()
					.unwrap_or(*ub)
					.into();
				IntVar::from_terms(xs, C::zero().into(), ub)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				IntVar::from_terms(
					terms
						.iter()
						.map(|(lit, coef)| {
							acc += **coef;
							debug_assert!(acc <= *ub);
							(acc.into(), lit.clone())
						})
						.collect(),
					C::zero().into(),
					ub,
				)
			}
			Part::Dom(_terms, _l, _u) => todo!(),
			// Part::Dom(terms, l, u) => build_totalizer(
			// 	terms
			// 		.iter()
			// 		// .chain(std::iter::once(IntVar::new(vec![], -l, -l); % TODO need neg. coefficients and int addition!
			// 		.map(|(lit, coef)| IntVar::new(vec![(*coef, lit.clone())], C::zero(), *coef))
			// 		.collect(),
			// 	db,
			// 	*l,
			// 	std::cmp::min(*u, ub),
			// 	false,
			// 	add_consistency,
			// 	0,
			// ),
		}
	}
}

pub(crate) trait IntVarEnc<Lit: Literal, C: Coefficient> {
	// fn index(&self, v: &C) -> &Self::Output;
	fn geq(&self, v: &C) -> Option<Vec<Lit>>;

	fn eq(&self, v: &C) -> Vec<LitOrConst<Lit>>;
	fn lb(&self) -> &C;
	fn ub(&self) -> &C;
}

pub(crate) fn ord_plus_ord_le_x<
	DB: ClauseDatabase + ?Sized,
	C: Coefficient,
	IV: IntVarEnc<DB::Lit, C>,
>(
	db: &mut DB,
	a: &IntVar<DB::Lit, C>,
	b: &IntVar<DB::Lit, C>,
	c: &IV,
) {
	for (l_a, c_a) in a.iter() {
		for (l_b, c_b) in b.iter() {
			let create_clause =
				|lits: Vec<LitOrConst<DB::Lit>>| -> std::result::Result<Vec<DB::Lit>, ()> {
					lits.into_iter()
						.filter_map(|lit| match lit {
							LitOrConst::Lit(lit) => Some(Ok(lit)),
							LitOrConst::Const(true) => Some(Err(())), // clause satisfied
							LitOrConst::Const(false) => None,         // literal falsified
						})
						.collect()
				};

			let v = *c_a + *c_b;
			if let Some(c_geq_v) = c.geq(&v) {
				// TODO convert lits to LitOrConst, since we still need to adapt iter before we can handle this properly
				let c_geq_v = c_geq_v.into_iter().map(LitOrConst::Lit).collect::<Vec<_>>();
				if !(c_geq_v.contains(&l_a) || c_geq_v.contains(&l_b)) {
					let clause = vec![vec![-l_a.clone(), -l_b], c_geq_v].concat();
					if let Ok(cls) = &create_clause(clause) {
						db.add_clause(cls).unwrap();
					}
				}
			}
		}
	}
}

pub(crate) fn ord_plus_ord_le_ord_sparse_dom<C: Coefficient>(
	a: Vec<C>,
	b: Vec<C>,
	l: C,
	u: C,
) -> Vec<C> {
	HashSet::<C>::from_iter(a.iter().flat_map(|a| {
		b.iter().filter_map(move |b| {
			// TODO refactor: use then_some when stabilized
			if *a + *b > l && *a + *b <= u {
				Some(*a + *b)
			} else {
				None
			}
		})
	}))
	.into_iter()
	.sorted()
	.collect::<Vec<_>>()
}

#[cfg(test)]
pub mod tests {
	use super::*;
	use crate::helpers::tests::TestDB;
	use iset::interval_map;

	#[test]
	fn bin_geq_test() {
		let x = IntVarBin {
			xs: vec![1, 2, 3, 4],
			lb: 0,
			ub: 12,
		};
		assert_eq!(x.geq(&3), Some(vec![1, 3]));
	}

	fn get_xy() -> (IntVar<i32, i32>, IntVar<i32, i32>) {
		(
			IntVar {
				xs: interval_map!( 1..2 => 1, 5..7 => 2 ), // 0, 1, 6
				lb: 0.into(),
				ub: 8.into(),
			},
			IntVar {
				xs: interval_map!( 2..3 => 3, 4..5 => 5 ), // 1, 2, 4
				lb: 1.into(),
				ub: 8.into(),
			},
		)
	}

	#[test]
	fn ord_plus_ord_leq_ord_test() {
		let mut db = TestDB::new(7);
		let (x, y) = get_xy();
		let z = IntVar {
			xs: interval_map!( 0..4 => 6, 4..11 => 7 ), // 0, 1, 2, 4, 6,
			lb: 0.into(),
			ub: 10.into(),
		};
		ord_plus_ord_le_x(&mut db, &x, &y, &z);
		db.expect_clauses(vec![]).check_complete();
	}

	#[test]
	fn ord_plus_ord_leq_bin_test() {
		let mut db = TestDB::new(7);
		let (x, y) = get_xy();
		let z = IntVarBin {
			xs: vec![1, 2, 3, 4],
			lb: 0.into(),
			ub: 12.into(),
		};
		ord_plus_ord_le_x(&mut db, &x, &y, &z);
		db.expect_clauses(vec![]).check_complete();
	}
}
