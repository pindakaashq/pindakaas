use iset::{interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	linear::{lex_lesseq_const, LinExp, Part},
	trace::{emit_clause, new_var},
	CheckError, Checker, ClauseDatabase, Coefficient, Encoder, Literal, PosCoeff, Result,
	Unsatisfiable,
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
			.map(|(v, lit)| {
				let lit = lit.unwrap_or_else(|| new_var!(db, format!("x>={v:?}")));
				(v, lit)
			})
			.collect::<IntervalMap<_, _>>();
		debug_assert!(!xs.is_empty());
		Self { xs }
	}

	pub fn _consistency(&self) -> ImplicationChainConstraint<Lit> {
		ImplicationChainConstraint {
			lits: self.xs.values(..).cloned().collect::<Vec<_>>(),
		}
	}
}

pub(crate) struct ImplicationChainConstraint<Lit: Literal> {
	lits: Vec<Lit>, // TODO slice?
}

#[derive(Default)]
pub(crate) struct ImplicationChainEncoder {}

impl ImplicationChainEncoder {
	pub fn _encode<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
		ic: &ImplicationChainConstraint<DB::Lit>,
	) -> Result {
		for (a, b) in ic.lits.iter().tuple_windows() {
			emit_clause!(db, &[b.negate(), a.clone()])?
		}
		Ok(())
	}
}

impl<Lit: Literal> Checker for ImplicationChainConstraint<Lit> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		self.lits.iter().tuple_windows().try_for_each(|(a, b)| {
			let a = Self::assign(a, solution);
			let b = Self::assign(b, solution);
			if b.is_negated() || !a.is_negated() {
				Ok(())
			} else {
				Err(CheckError::Unsatisfiable(Unsatisfiable))
			}
		})
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

	fn as_lin_exp(&self) -> LinExp<Lit, C> {
		let mut acc = self.lb();
		LinExp::new()
			.add_chain(
				&self
					.xs
					.iter(..)
					.map(|(iv, lit)| {
						let v = iv.end - C::one() - acc;
						acc += v;
						(lit.clone(), v)
					})
					.collect::<Vec<_>>(),
			)
			.add_constant(self.lb())
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Debug, Clone)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	pub(crate) xs: Vec<Lit>,
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

	pub fn _consistency(&self) -> TernLeConstraintContainer<Lit, C> {
		TernLeConstraintContainer {
			x: IntVarEnc::Bin(self.clone()),
			y: IntVarEnc::Const(self.lb),
			z: IntVarEnc::Const(self.ub),
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
		let v = *v - C::one(); // x >= 7 == x > 6
		Some(
			self.xs
				.iter()
				.enumerate()
				.filter_map(|(i, lit)| {
					if ((v >> i) & C::one()) != C::one() {
						Some(lit.clone())
					} else {
						None
					}
				})
				.collect::<Vec<_>>(),
		)
	}

	fn eq(&self, _: &C) -> Option<Vec<Lit>> {
		todo!();
	}

	fn as_lin_exp(&self) -> LinExp<Lit, C> {
		let mut exp = LinExp::new();
		let mut k = C::one();
		let two = C::one() + C::one();
		for lit in &self.xs {
			exp += (lit.clone(), k);
			k *= two;
		}
		exp
	}
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
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
								emit_clause!(db, &[lit.negate(), o.clone()]).unwrap();
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

#[derive(Debug, Clone)]
pub(crate) enum IntVarEnc<Lit: Literal, C: Coefficient> {
	Ord(IntVarOrd<Lit, C>),
	#[allow(dead_code)]
	Bin(IntVarBin<Lit, C>),
	Const(C),
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> {
	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	pub(crate) fn geq(&self, v: &C) -> Option<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.geq(v),
			IntVarEnc::Bin(b) => b.geq(v),
			IntVarEnc::Const(c) => {
				if c >= v {
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
				if c == v {
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
			IntVarEnc::Const(c) => interval_set!(*c..(*c + C::one())),
		}
	}

	#[allow(dead_code)]
	pub(crate) fn lb(&self) -> C {
		match self {
			IntVarEnc::Ord(o) => o.lb(),
			IntVarEnc::Bin(b) => b.lb(),
			IntVarEnc::Const(c) => *c,
			// _ => self.dom().range().unwrap().start - C::one(),
		}
	}

	pub(crate) fn ub(&self) -> C {
		match self {
			IntVarEnc::Ord(o) => o.ub(),
			IntVarEnc::Bin(b) => b.ub(),
			IntVarEnc::Const(c) => *c,
			// _ => self.dom().range().unwrap().end - C::one(),
		}
	}

	pub(crate) fn as_lin_exp(&self) -> LinExp<Lit, C> {
		match self {
			IntVarEnc::Ord(o) => o.as_lin_exp(),
			IntVarEnc::Bin(b) => b.as_lin_exp(),
			IntVarEnc::Const(c) => LinExp::new().add_constant(*c),
		}
	}
}

pub(crate) fn encode_consistency<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	x: &IntVarEnc<DB::Lit, C>,
) -> Result {
	let b = IntVarEnc::Const(-C::one());
	TernLeEncoder::default().encode(db, &TernLeConstraint::new(x, &b, x))
}

pub(crate) struct TernLeConstraint<'a, Lit: Literal, C: Coefficient> {
	pub(crate) x: &'a IntVarEnc<Lit, C>,
	pub(crate) y: &'a IntVarEnc<Lit, C>,
	pub(crate) z: &'a IntVarEnc<Lit, C>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraint<'a, Lit, C> {
	pub fn new(
		x: &'a IntVarEnc<Lit, C>,
		y: &'a IntVarEnc<Lit, C>,
		z: &'a IntVarEnc<Lit, C>,
	) -> Self {
		Self { x, y, z }
	}
}

impl<'a, Lit: Literal, C: Coefficient> Checker for TernLeConstraint<'a, Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let x = LinExp::from(self.x).assign(solution);
		let y = LinExp::from(self.y).assign(solution);
		let z = LinExp::from(self.z).assign(solution);
		if x + y <= z {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

#[allow(dead_code)] // TODO
pub(crate) struct TernLeConstraintContainer<Lit: Literal, C: Coefficient> {
	pub(crate) x: IntVarEnc<Lit, C>,
	pub(crate) y: IntVarEnc<Lit, C>,
	pub(crate) z: IntVarEnc<Lit, C>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraintContainer<Lit, C> {
	#[allow(dead_code)]
	pub(crate) fn get(&'a self) -> TernLeConstraint<'a, Lit, C> {
		TernLeConstraint {
			x: &self.x,
			y: &self.y,
			z: &self.z,
		}
	}
}

#[derive(Default)]
pub(crate) struct TernLeEncoder {}

impl<'a, DB: ClauseDatabase, C: Coefficient> Encoder<DB, TernLeConstraint<'a, DB::Lit, C>>
	for TernLeEncoder
{
	fn encode(&mut self, db: &mut DB, tern: &TernLeConstraint<DB::Lit, C>) -> Result {
		let TernLeConstraint { x, y, z } = tern;
		if let IntVarEnc::Bin(x_bin) = x {
			if let IntVarEnc::Const(z_con) = z {
				return lex_lesseq_const(
					db,
					x_bin
						.xs
						.iter()
						.map(|x| Some(x.clone()))
						.collect::<Vec<_>>()
						.as_slice(),
					(*z_con).into(),
					x_bin.xs.len(),
				);
			} else if let IntVarEnc::Bin(_z_bin) = z {
				todo!()
			} else {
				unimplemented!("LHS binary variables only implemented for some cases (and not tested in general method")
			}
		} else {
			for c_a in x.dom() {
				for c_b in y.dom() {
					let neg = |disjunction: Option<Vec<DB::Lit>>| -> Option<Vec<DB::Lit>> {
						match disjunction {
							None => Some(vec![]),
							Some(lits) if lits.is_empty() => None,
							Some(lits) => Some(lits.into_iter().map(|l| l.negate()).collect()),
						}
					};

					let (c_a, c_b) = ((c_a.end - C::one()), (c_b.end - C::one()));
					let c_c = c_a + c_b;
					let (l_a, l_b, l_c) = (neg(x.geq(&c_a)), neg(y.geq(&c_b)), z.geq(&c_c));

					if let Some(l_a) = l_a {
						if let Some(l_b) = l_b {
							if let Some(l_c) = l_c {
								emit_clause!(db, &[l_a, l_b, l_c].concat())?
							}
						}
					}
				}
			}
			Ok(())
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
	use crate::helpers::tests::{assert_sol, TestDB};
	use iset::interval_set;

	fn get_ord_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: IntervalSet<C>,
		consistent: bool,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarOrd::new(db, dom.into_iter(..).map(|iv| (iv, None)).collect());
		if consistent {
			ImplicationChainEncoder::default()
				._encode(db, &x._consistency())
				.unwrap();
		}
		IntVarEnc::Ord(x)
	}

	fn get_bin_x<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
		db: &mut DB,
		ub: C,
		consistent: bool,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarBin::_new(db, ub);
		if consistent {
			TernLeEncoder::default()
				.encode(db, &x._consistency().get())
				.unwrap();
		}
		IntVarEnc::Bin(x)
	}

	#[test]
	fn constant_test() {
		let c: IntVarEnc<i32, _> = IntVarEnc::Const(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(&6), None);
		assert_eq!(c.geq(&45), Some(vec![]));
	}

	#[test]
	fn bin_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_bin_x::<_, i32>(&mut db, 12, true);
		let x_lin: LinExp<i32, i32> = LinExp::from(&x);

		assert_eq!(x.lb(), 0);
		assert_eq!(x.ub(), 12);
		assert_eq!(x.geq(&7), Some(vec![1, 4])); // 7-1=6 = 0110

		assert_eq!(x_lin.assign(&[-1, -2, -3, -4]), 0);
		assert_eq!(x_lin.assign(&[1, -2, -3, -4]), 1);
		assert_eq!(x_lin.assign(&[1, 2, -3, -4]), 3);
		assert_eq!(x_lin.assign(&[1, 2, -3, 4]), 11);
		assert_eq!(x_lin.assign(&[1, 2, 3, 4]), 15);

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			z: &IntVarEnc::Const(10), // TODO no consistency implemented for this bound yet
		};

		db.num_var = 4;

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4],
		  vec![1, -2, -3, -4],
		  vec![-1, 2, -3, -4],
		  vec![1, 2, -3, -4],
		  vec![-1, -2, 3, -4],
		  vec![1, -2, 3, -4],
		  vec![-1, 2, 3, -4],
		  vec![1, 2, 3, -4],
		  vec![-1, -2, -3, 4],
		  vec![1, -2, -3, 4],
		  vec![-1, 2, -3, 4],
		]);
	}

	#[test]
	fn bin_geq_2_test() {
		let mut db = TestDB::new(0);
		let tern = TernLeConstraint {
			x: &IntVarEnc::Bin(IntVarBin::_new(&mut db, 12)),
			y: &IntVarEnc::Const(0),
			z: &IntVarEnc::Const(6),
		};
		db.num_var = 4;
		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		vec![-1, -2, -3, -4], // 0
		vec![1, -2, -3, -4], // 1
		vec![-1, 2, -3, -4], // 2
		vec![1, 2, -3, -4], // 3
		vec![-1, -2, 3, -4], // 4
		vec![1, -2, 3, -4], // 5
		vec![-1, 2, 3, -4],// 6
		]);
	}

	#[test]
	fn ord_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_ord_x::<_, i32>(&mut db, interval_set!(3..5, 5..7, 7..11), true);

		let x_lin: LinExp<i32, i32> = LinExp::from(&x);

		assert_eq!(x.lb(), 2);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(&6), Some(vec![2]));

		assert_eq!(x_lin.assign(&[-1, -2, -3]), 2);
		assert_eq!(x_lin.assign(&[1, -2, -3]), 4);
		assert_eq!(x_lin.assign(&[1, 2, -3]), 6);
		assert_eq!(x_lin.assign(&[1, 2, 3]), 10);

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			z: &IntVarEnc::Const(6),
		};

		// TernLeEncoder::default().encode(&mut db, &tern).unwrap();
		// db.generate_solutions(
		// 	move |sol| tern.check(sol).is_ok() && consistency.check(sol).is_ok(),
		// 	3,
		// );

		db.num_var = 3;

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3],
		  vec![1, -2, -3],
		  vec![1, 2, -3],
		]);
	}

	#[test]
	fn ord_plus_ord_leq_ord_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true),
			get_ord_x(&mut db, interval_set!(2..3, 4..5), true),
			get_ord_x(&mut db, interval_set!(0..4, 4..11), true),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			z: &z,
		};
		db.num_var = 6;

		// TernLeEncoder::default().encode(&mut db, &tern).unwrap();
		// let x_con = x
		// 	.as_any()
		// 	.downcast_ref::<IntVarOrd<i32, i32>>()
		// 	.unwrap()
		// 	._consistency();
		// let y_con = y
		// 	.as_any()
		// 	.downcast_ref::<IntVarOrd<i32, i32>>()
		// 	.unwrap()
		// 	._consistency();
		// let z_con = z
		// 	.as_any()
		// 	.downcast_ref::<IntVarOrd<i32, i32>>()
		// 	.unwrap()
		// 	._consistency();
		// db.generate_solutions(
		// 	move |sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x_con.check(sol).is_ok()
		// 			&& y_con.check(sol).is_ok()
		// 			&& z_con.check(sol).is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, 5, -6],
		  vec![-1, -2, -3, -4, 5, 6],
		  vec![-1, -2, 3, -4, 5, -6],
		  vec![-1, -2, 3, -4, 5, 6],
		  vec![-1, -2, 3, 4, 5, 6],
		  vec![1, -2, -3, -4, 5, -6],
		  vec![1, -2, -3, -4, 5, 6],
		  vec![1, -2, 3, -4, 5, -6],
		  vec![1, -2, 3, -4, 5, 6],
		  vec![1, -2, 3, 4, 5, 6],
		  vec![1, 2, -3, -4, 5, 6],
		  vec![1, 2, 3, -4, 5, 6],
		  vec![1, 2, 3, 4, 5, 6],
				]);
	}

	// 	// #[test]
	// 	fn ord_plus_ord_leq_bin_test() {
	// 		let mut db = TestDB::new(0);
	// 		assert_sol!(
	// 			TernLeEncoder::default(),
	// 			0,
	// 			&TernLeConstraint {
	// 				x: &get_ord_x(&mut db, interval_set!(1..2, 5..7), true),
	// 				y: &get_ord_x(&mut db, interval_set!(2..3, 4..5), true),
	// 				z: &get_bin_x(&mut db, 12, true),
	// 			}
	// 		);
	// 	}

	// 	// #[test]
	// 	fn bin_plus_bin_le_bin_test() {
	// 		let mut db = TestDB::new(0);
	// 		let (x, y, z): (
	// 			Box<dyn IntVarEnc<i32, i32>>,
	// 			Box<dyn IntVarEnc<i32, i32>>,
	// 			Box<dyn IntVarEnc<i32, i32>>,
	// 		) = (
	// 			Box::new(IntVarBin::_new(&mut db, 12)),
	// 			Box::new(IntVarBin::_new(&mut db, 12)),
	// 			Box::new(IntVarBin::_new(&mut db, 12)),
	// 		);

	// 		let con = TernLeConstraint {
	// 			x: &x,
	// 			y: &y,
	// 			z: &z,
	// 		};
	// 		assert_sol!(db, TernLeEncoder::default(), 0, con);
	// 	}

	// #[test]
	// fn bin_plus_bin_le_bin_test() {
	// 	let mut db = TestDB::new(0);
	// 	assert_sol!(
	// 		TernLeEncoder::default(),
	// 		0,
	// 		&TernLeConstraint {
	// 			x: &get_bin_x(&mut db, 12, true),
	// 			y: &get_bin_x(&mut db, 12, true),
	// 			z: &get_bin_x(&mut db, 12, true),
	// 		}
	// 	);
	// }
}
