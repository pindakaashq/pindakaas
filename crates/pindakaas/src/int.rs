use iset::{interval_set, IntervalMap, IntervalSet};
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
#[derive(Clone, Debug)]
pub(crate) struct Constant<C: Coefficient> {
	c: C,
}

impl<C: Coefficient> Constant<C> {
	pub fn new(c: C) -> Self {
		Self { c }
	}
}

impl<DB: ClauseDatabase, C: Coefficient + 'static> IntVarEnc<DB, C> for Constant<C> {
	fn dom(&self) -> IntervalSet<C> {
		interval_set!(self.c..(self.c + C::one()))
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<DB, C>> {
		Box::new(self.clone()) // Forward to the derive(Clone) impl
	}

	fn eq(&self, v: &C) -> Option<Vec<DB::Lit>> {
		if &self.c == v {
			None
		} else {
			Some(vec![])
		}
	}

	fn geq(&self, v: &C) -> Option<Vec<DB::Lit>> {
		if &self.c >= v {
			None
		} else {
			Some(vec![])
		}
	}
}

// TODO maybe C -> PosCoeff<C>
// #[derive(Debug)]
pub(crate) struct IntVarOrd<DB: ClauseDatabase, C: Coefficient> {
	xs: IntervalMap<C, DB::Lit>,
}

impl<DB: ClauseDatabase, C: Coefficient> Clone for Box<dyn IntVarEnc<DB, C>> {
	fn clone(&self) -> Self {
		self.clone_dyn()
	}
}

impl<DB: ClauseDatabase, C: Coefficient> IntVarOrd<DB, C> {
	pub fn new(db: &mut DB, dom: IntervalMap<C, Option<DB::Lit>>) -> Self {
		let xs = dom
			.into_iter(..)
			.map(|(v, lit)| (v, lit.unwrap_or_else(|| new_var!(db))))
			.collect::<IntervalMap<_, _>>();
		debug_assert!(!xs.is_empty());
		Self { xs }
	}
}

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> IntVarEnc<DB, C> for IntVarOrd<DB, C> {
	fn dom(&self) -> IntervalSet<C> {
		std::iter::once(self.lb()..self.lb() + C::one())
			.chain(self.xs.intervals(..))
			.collect()
	}

	fn lb(&self) -> C {
		self.xs.range().unwrap().start - C::one()
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<DB, C>> {
		Box::new(IntVarOrd {
			xs: self.xs.clone(),
		})
	}

	fn ub(&self) -> C {
		self.xs.range().unwrap().end - C::one()
	}

	fn eq(&self, _: &C) -> Option<Vec<DB::Lit>> {
		todo!();
	}

	fn geq(&self, v: &C) -> Option<Vec<DB::Lit>> {
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
#[derive(Clone)]
pub(crate) struct IntVarBin<DB: ClauseDatabase, C: Coefficient> {
	xs: Vec<DB::Lit>,
	lb: C,
	ub: C,
}

impl<DB: ClauseDatabase, C: Coefficient> IntVarBin<DB, C> {
	pub fn _new(db: &mut DB, ub: C) -> Self {
		let bits = C::zero().leading_zeros() - ub.leading_zeros();
		Self {
			xs: (0..bits).map(|_| db.new_var()).collect(),
			lb: C::zero(), // TODO support non-zero
			ub,
		}
	}
}

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> IntVarEnc<DB, C> for IntVarBin<DB, C> {
	fn dom(&self) -> IntervalSet<C> {
		num::iter::range_inclusive(self.lb, self.ub)
			.map(|i| i..(i + C::one()))
			.collect()
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<DB, C>> {
		Box::new(IntVarBin {
			xs: self.xs.clone(),
			lb: self.lb,
			ub: self.ub,
		})
	}

	fn lb(&self) -> C {
		self.lb
	}

	fn ub(&self) -> C {
		self.ub
	}

	// TODO return ref
	// TODO impl Index
	fn geq(&self, v: &C) -> Option<Vec<DB::Lit>> {
		let mut v = *v;
		v.unsigned_shl(v.trailing_zeros());
		let mut vs: Vec<DB::Lit> = vec![];
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

	fn eq(&self, _: &C) -> Option<Vec<DB::Lit>> {
		todo!();
	}
}

impl<DB: ClauseDatabase + 'static, C: Coefficient + 'static> IntVarOrd<DB, C> {
	/// Constructs IntVar `y` for linear expression `xs` so that ∑ xs ≦ y, using order encoding
	pub fn from_part_using_le_ord(
		db: &mut DB,
		xs: &Part<DB::Lit, PosCoeff<C>>,
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

				let dom = std::iter::once((C::zero(), vec![]))
					.chain(h.into_iter())
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					.tuple_windows()
					.map(|((prev, _), (coef, lits))| {
						let interval = (prev + C::one())..(coef + C::one());
						if lits.len() == 1 {
							(interval, Some(lits[0].clone()))
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								db.add_clause(&[lit.negate(), o.clone()]).unwrap();
							}
							(interval, Some(o))
						}
					})
					.collect();
				IntVarOrd::new(db, dom)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				IntVarOrd::new(
					db,
					std::iter::once(&(terms[0].0.clone(), C::zero().into()))
						.chain(terms.iter())
						.map(|(lit, coef)| {
							acc += **coef;
							debug_assert!(acc <= *ub);
							(acc, lit.clone())
						})
						.tuple_windows()
						.map(|((prev, _), (coef, lit))| {
							((prev + C::one())..(coef + C::one()), Some(lit))
						})
						.collect(),
				)
			}
			Part::Dom(_terms, _l, _u) => todo!(),
		}
	}
}

pub(crate) trait IntVarEnc<DB: ClauseDatabase, C: Coefficient> {
	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	fn geq(&self, v: &C) -> Option<Vec<DB::Lit>>;

	/// Returns a clause constraining `x==v`, which is None if true and empty if false
	fn eq(&self, v: &C) -> Option<Vec<DB::Lit>>;

	/// Returns a partitioned domain
	fn dom(&self) -> IntervalSet<C>;

	fn lb(&self) -> C {
		self.dom().range().unwrap().start - C::one()
	}

	fn ub(&self) -> C {
		self.dom().range().unwrap().end - C::one()
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<DB, C>>;
}

pub(crate) fn encode_consistency<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
	db: &mut DB,
	x: &Box<dyn IntVarEnc<DB, C>>,
) {
	let b: Box<dyn IntVarEnc<DB, C>> = Box::new(Constant::new(-C::one()));
	ord_plus_ord_le_x(db, x, &b, x);
}

pub(crate) fn ord_plus_ord_le_x<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	a: &Box<dyn IntVarEnc<DB, C>>,
	b: &Box<dyn IntVarEnc<DB, C>>,
	c: &Box<dyn IntVarEnc<DB, C>>,
) {
	for c_a in a.dom() {
		for c_b in b.dom() {
			let neg = |disjunction: Option<Vec<DB::Lit>>| -> Option<Vec<DB::Lit>> {
				match disjunction {
					None => Some(vec![]),
					Some(lits) if lits.is_empty() => None,
					Some(lits) => Some(lits.into_iter().map(|l| -l).collect()),
				}
			};

			let (c_a, c_b) = ((c_a.end - C::one()), (c_b.end - C::one()));
			let c_c = c_a + c_b;
			let (l_a, l_b, l_c) = (neg(a.geq(&c_a)), neg(b.geq(&c_b)), c.geq(&c_c));

			if let Some(l_a) = l_a {
				if let Some(l_b) = l_b {
					if let Some(l_c) = l_c {
						db.add_clause(&[l_a, l_b, l_c].concat()).unwrap();
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

	fn get_ord_x<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
		db: &mut DB,
		dom: IntervalSet<C>,
	) -> Box<dyn IntVarEnc<DB, C>> {
		Box::new(IntVarOrd::new(
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
		let (x, y, z): (_, _, Box<dyn IntVarEnc<TestDB, i32>>) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7)),
			get_ord_x(&mut db, interval_set!(2..3, 4..5)),
			Box::new(IntVarBin::_new(&mut db, 12)),
		);
		ord_plus_ord_le_x(&mut db, &x, &y, &z);
		db.expect_clauses(vec![vec![]]).check_complete();
	}

	// #[test]
	fn bin_plus_bin_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z): (
			Box<dyn IntVarEnc<TestDB, i32>>,
			Box<dyn IntVarEnc<TestDB, i32>>,
			Box<dyn IntVarEnc<TestDB, i32>>,
		) = (
			Box::new(IntVarBin::_new(&mut db, 12)),
			Box::new(IntVarBin::_new(&mut db, 12)),
			Box::new(IntVarBin::_new(&mut db, 12)),
		);
		ord_plus_ord_le_x(&mut db, &x, &y, &z);
		db.expect_clauses(vec![]).check_complete();
	}
}
