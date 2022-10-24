use iset::{interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	linear::Part,
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Literal, PosCoeff,
};
use std::{collections::HashSet, hash::BuildHasherDefault, ops::Neg};

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
#[derive(Clone, Debug)]
pub(crate) struct Constant<C: Coefficient> {
	c: C,
}

impl<C: Coefficient> Constant<C> {
	pub fn new(c: C) -> Self {
		Self { c }
	}
}

impl<C: Coefficient> Constant<C> {
	fn dom(&self) -> IntervalSet<C> {
		interval_set!(self.c..(self.c + C::one()))
	}

	fn eq(&self, v: &C) -> bool {
		self.c == *v
	}

	fn geq(&self, v: &C) -> bool {
		self.c >= *v
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Debug, Clone)]
pub(crate) struct IntVarOrd<Lit: Literal, C: Coefficient> {
	xs: IntervalMap<C, Lit>,
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		dom: IntervalMap<C, Option<Lit>>,
	) -> Self {
		let xs = dom
			.into_iter(..)
			.map(|(v, lit)| (v, lit.unwrap_or_else(|| new_var!(db))))
			.collect::<IntervalMap<_, _>>();
		debug_assert!(!xs.is_empty());
		Self { xs }
	}
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	fn dom(&self) -> IntervalSet<C> {
		std::iter::once(self.lb()..self.lb() + C::one())
			.chain(self.xs.intervals(..))
			.collect()
	}

	fn lb(&self) -> C {
		self.xs.range().unwrap().start - C::one()
	}

	fn ub(&self) -> C {
		self.xs.range().unwrap().end - C::one()
	}

	fn eq(&self, _: &C) -> Option<Vec<Lit>> {
		todo!();
	}

	fn geq(&self, v: &C) -> Option<Vec<Lit>> {
		if v <= &self.lb() {
			None
		} else if v > &self.ub() {
			Some(vec![])
		} else {
			match self.xs.overlap(*v).collect::<Vec<_>>()[..] {
				[(_, x)] => Some(vec![x.clone()]),
				_ => panic!("No or multiples variables at {v:?}"),
			}
		}
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Debug, Clone)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	xs: Vec<Lit>,
	lb: C,
	ub: C,
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	pub fn _new<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, ub: C) -> Self {
		let bits = C::zero().leading_zeros() - ub.leading_zeros();
		Self {
			xs: (0..bits).map(|_| db.new_var()).collect(),
			lb: C::zero(), // TODO support non-zero
			ub,
		}
	}
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	fn dom(&self) -> IntervalSet<C> {
		num::iter::range_inclusive(self.lb, self.ub)
			.map(|i| i..(i + C::one()))
			.collect()
	}

	fn lb(&self) -> C {
		self.lb
	}

	fn ub(&self) -> C {
		self.ub
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

	fn eq(&self, _: &C) -> Option<Vec<Lit>> {
		todo!();
	}
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	// TODO can be removed using new
	pub fn from_terms(terms: IntervalMap<C, Lit>) -> Self {
		debug_assert!(!terms.is_empty());
		Self {
			xs: IntervalMap::from_sorted(
				terms.into_iter(..).map(|(interval, lit)| (interval, lit)),
			),
		}
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
				let terms: Vec<(PosCoeff<C>, Lit)> = terms
					.iter()
					.map(|(lit, coef)| (coef.clone(), lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: FxHashMap<C, Vec<Lit>> =
					FxHashMap::with_capacity_and_hasher(terms.len(), BuildHasherDefault::default());
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(*coef).or_insert_with(Vec::new).push(lit);
				}

				IntVarOrd::from_terms(
					std::iter::once((C::zero(), vec![]))
						.chain(h.into_iter())
						.sorted_by(|(a, _), (b, _)| a.cmp(b))
						.tuple_windows()
						.map(|((prev, _), (coef, lits))| {
							let interval = (prev + C::one())..(coef + C::one());
							if lits.len() == 1 {
								(interval, lits[0].clone())
							} else {
								let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
								for lit in lits {
									emit_clause!(db, &[lit.negate(), o.clone()]).unwrap();
								}
								(interval, o)
							}
						})
						.collect(),
				)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				IntVarOrd::from_terms(
					std::iter::once(&(terms[0].0.clone(), C::zero().into()))
						.chain(terms.iter())
						.map(|(lit, coef)| {
							acc += **coef;
							debug_assert!(acc <= *ub);
							(acc, lit.clone())
						})
						.tuple_windows()
						.map(|((prev, _), (coef, lit))| ((prev + C::one())..(coef + C::one()), lit))
						.collect(),
				)
			}
			Part::Dom(_terms, _l, _u) => todo!(),
		}
	}
}

#[derive(Debug, Clone)]
pub(crate) enum IntVarEnc<Lit: Literal, C: Coefficient> {
	Ord(IntVarOrd<Lit, C>),
	#[allow(dead_code)]
	Bin(IntVarBin<Lit, C>),
	Const(Constant<C>),
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> {
	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	pub(crate) fn geq(&self, v: &C) -> Option<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.geq(v),
			IntVarEnc::Bin(b) => b.geq(v),
			IntVarEnc::Const(c) => {
				if c.geq(v) {
					None
				} else {
					Some(Vec::new())
				}
			}
		}
	}

	/// Returns a clause constraining `x==v`, which is None if true and empty if false
	#[allow(dead_code)]
	pub(crate) fn eq(&self, v: &C) -> Option<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.eq(v),
			IntVarEnc::Bin(b) => b.eq(v),
			IntVarEnc::Const(c) => {
				if c.eq(v) {
					None
				} else {
					Some(Vec::new())
				}
			}
		}
	}

	/// Returns a partitioned domain
	pub(crate) fn dom(&self) -> IntervalSet<C> {
		match self {
			IntVarEnc::Ord(o) => o.dom(),
			IntVarEnc::Bin(b) => b.dom(),
			IntVarEnc::Const(c) => c.dom(),
		}
	}

	#[allow(dead_code)]
	pub(crate) fn lb(&self) -> C {
		match self {
			IntVarEnc::Ord(o) => o.lb(),
			IntVarEnc::Bin(b) => b.lb(),
			IntVarEnc::Const(c) => c.c,
			// _ => self.dom().range().unwrap().start - C::one(),
		}
	}

	pub(crate) fn ub(&self) -> C {
		match self {
			IntVarEnc::Ord(o) => o.ub(),
			IntVarEnc::Bin(b) => b.ub(),
			IntVarEnc::Const(c) => c.c,
			// _ => self.dom().range().unwrap().end - C::one(),
		}
	}
}

pub(crate) fn encode_consistency<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	x: &IntVarEnc<DB::Lit, C>,
) {
	let b = IntVarEnc::Const(Constant::new(-C::one()));
	ord_plus_ord_le_x(db, x, &b, x);
}

pub(crate) fn ord_plus_ord_le_x<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	a: &IntVarEnc<DB::Lit, C>,
	b: &IntVarEnc<DB::Lit, C>,
	c: &IntVarEnc<DB::Lit, C>,
) {
	for c_a in a.dom() {
		for c_b in b.dom() {
			let neg = |disjunction: Option<Vec<DB::Lit>>| -> Option<Vec<DB::Lit>> {
				match disjunction {
					None => Some(vec![]),
					Some(lits) if lits.is_empty() => None,
					Some(lits) => Some(lits.into_iter().map(|l| l.negate()).collect()),
				}
			};

			let (c_a, c_b) = ((c_a.end - C::one()), (c_b.end - C::one()));
			let c_c = c_a + c_b;
			let (l_a, l_b, l_c) = (neg(a.geq(&c_a)), neg(b.geq(&c_b)), c.geq(&c_c));

			if let Some(l_a) = l_a {
				if let Some(l_b) = l_b {
					if let Some(l_c) = l_c {
						emit_clause!(db, &[l_a, l_b, l_c].concat()).unwrap();
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
) -> IntervalSet<C> {
	// TODO optimize by dedup (if already sorted?)
	HashSet::<C>::from_iter(a.iter().flat_map(|a| {
		b.iter().filter_map(move |b| {
			// TODO refactor: use then_some when stabilized
			if *a + *b >= l && *a + *b <= u {
				Some(*a + *b)
			} else {
				None
			}
		})
	}))
	.into_iter()
	.sorted()
	.tuple_windows()
	.map(|(a, b)| (a + C::one())..(b + C::one()))
	.collect::<IntervalSet<_>>()
}

#[cfg(test)]
pub mod tests {
	#![allow(dead_code)]

	use super::*;
	use crate::helpers::tests::TestDB;
	use iset::interval_set;

	fn get_ord_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: IntervalSet<C>,
	) -> IntVarEnc<DB::Lit, C> {
		IntVarEnc::Ord(IntVarOrd::new(
			db,
			dom.into_iter(..).map(|iv| (iv, None)).collect(),
		))
	}

	#[test]
	fn bin_geq_test() {
		let mut db = TestDB::new(0);
		let x = IntVarBin::_new(&mut db, 12);
		assert_eq!(x.geq(&3), Some(vec![1, 3]));
	}

	#[test]
	fn ord_plus_ord_leq_ord_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7)),
			get_ord_x(&mut db, interval_set!(2..3, 4..5)),
			get_ord_x(&mut db, interval_set!(0..4, 4..11)),
		);
		ord_plus_ord_le_x(&mut db, &x, &y, &z);
		db.expect_clauses(vec![]).check_complete();
	}

	// #[test]
	fn ord_plus_ord_leq_bin_test() {
		let mut db = TestDB::new(0);

		let x = get_ord_x(&mut db, interval_set!(1..2, 5..7));
		let y = get_ord_x(&mut db, interval_set!(2..3, 4..5));
		let z = IntVarEnc::Bin(IntVarBin::_new(&mut db, 12));

		ord_plus_ord_le_x(&mut db, &x, &y, &z);
		db.expect_clauses(vec![vec![]]).check_complete();
	}

	// #[test]
	fn bin_plus_bin_le_bin_test() {
		let mut db = TestDB::new(0);
		let mut bin_12 = || IntVarEnc::Bin(IntVarBin::_new(&mut db, 12));

		let x = bin_12();
		let y = bin_12();
		let z = bin_12();

		ord_plus_ord_le_x(&mut db, &x, &y, &z);
		db.expect_clauses(vec![]).check_complete();
	}
}
