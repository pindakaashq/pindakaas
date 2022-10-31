use iset::{interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use std::any::Any;

use crate::{
	linear::{LinExp, Part},
	new_var, CheckError, Checker, ClauseDatabase, Coefficient, Encoder, Literal, PosCoeff, Result,
	Unsatisfiable,
};
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

impl<Lit: Literal, C: Coefficient + 'static> IntVarEnc<Lit, C> for Constant<C> {
	fn dom(&self) -> IntervalSet<C> {
		interval_set!(self.c..(self.c + C::one()))
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<Lit, C>> {
		Box::new(self.clone())
	}

	fn eq(&self, v: &C) -> Option<Vec<Lit>> {
		if &self.c == v {
			None
		} else {
			Some(vec![])
		}
	}

	fn geq(&self, v: &C) -> Option<Vec<Lit>> {
		if &self.c >= v {
			None
		} else {
			Some(vec![])
		}
	}

	fn into_lin_exp(&self) -> LinExp<Lit, C> {
		LinExp::new().add_constant(self.c)
	}

	fn as_any(&self) -> &dyn Any {
		self
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Debug)]
pub(crate) struct IntVarOrd<Lit: Literal, C: Coefficient> {
	xs: IntervalMap<C, Lit>,
}

impl<Lit: Literal, C: Coefficient> Clone for Box<dyn IntVarEnc<Lit, C>> {
	fn clone(&self) -> Self {
		self.clone_dyn()
	}
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		dom: IntervalMap<C, Option<Lit>>,
	) -> Self {
		let xs = dom
			.into_iter(..)
			.map(|(v, lit)| {
				#[cfg(debug_assertions)]
				let lbl = format!("x>={v:?}");
				(v, lit.unwrap_or_else(|| new_var!(db, lbl)))
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
			db.add_clause(&[b.negate(), a.clone()])?
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

impl<Lit: Literal + 'static, C: Coefficient + 'static> IntVarEnc<Lit, C> for IntVarOrd<Lit, C> {
	fn dom(&self) -> IntervalSet<C> {
		std::iter::once(self.lb()..self.lb() + C::one())
			.chain(self.xs.intervals(..))
			.collect()
	}

	fn lb(&self) -> C {
		self.xs.range().unwrap().start - C::one()
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<Lit, C>> {
		Box::new(IntVarOrd {
			xs: self.xs.clone(),
		})
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

	fn into_lin_exp(&self) -> LinExp<Lit, C> {
		let mut acc = self.lb();
		LinExp::new().add_chain(
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
	}

	fn as_any(&self) -> &dyn Any {
		self
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Clone, Debug)]
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

impl<Lit: Literal + 'static, C: Coefficient + 'static> IntVarEnc<Lit, C> for IntVarBin<Lit, C> {
	fn dom(&self) -> IntervalSet<C> {
		num::iter::range_inclusive(self.lb, self.ub)
			.map(|i| i..(i + C::one()))
			.collect()
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<Lit, C>> {
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

	fn into_lin_exp(&self) -> LinExp<Lit, C> {
		let mut exp = LinExp::new();
		let mut k = C::one();
		let two = C::one() + C::one();
		for lit in &self.xs {
			exp += (lit.clone(), k);
			k *= two;
		}
		exp
	}

	fn as_any(&self) -> &dyn Any {
		self
	}
}

impl<Lit: Literal + 'static, C: Coefficient + 'static> IntVarOrd<Lit, C> {
	/// Constructs IntVar `y` for linear expression `xs` so that ∑ xs ≦ y, using order encoding
	pub fn from_part_using_le_ord<DB: ClauseDatabase<Lit = Lit>>(
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

pub(crate) trait IntVarEnc<Lit: Literal, C: Coefficient>: std::fmt::Debug {
	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	fn geq(&self, v: &C) -> Option<Vec<Lit>>;

	/// Returns a clause constraining `x==v`, which is None if true and empty if false
	fn eq(&self, v: &C) -> Option<Vec<Lit>>;

	/// Returns a partitioned domain
	fn dom(&self) -> IntervalSet<C>;

	fn lb(&self) -> C {
		self.dom().range().unwrap().start
	}

	fn ub(&self) -> C {
		self.dom().range().unwrap().end - C::one()
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<Lit, C>>;

	// TODO consume self?
	fn into_lin_exp(&self) -> LinExp<Lit, C>;

	fn debug(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "x in {:?}", self.dom())
	}

	fn as_any(&self) -> &dyn Any;
}

pub(crate) fn encode_consistency<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
	db: &mut DB,
	x: &Box<dyn IntVarEnc<DB::Lit, C>>,
) -> Result {
	let b: Box<dyn IntVarEnc<DB::Lit, C>> = Box::new(Constant::new(-C::one()));
	TernLeEncoder::default().encode(db, &TernLeConstraint::new(x, &b, x))
}

pub(crate) struct TernLeConstraint<'a, Lit: Literal, C: Coefficient> {
	pub(crate) x: &'a Box<dyn IntVarEnc<Lit, C>>,
	pub(crate) y: &'a Box<dyn IntVarEnc<Lit, C>>,
	pub(crate) z: &'a Box<dyn IntVarEnc<Lit, C>>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraint<'a, Lit, C> {
	pub fn new(
		x: &'a Box<dyn IntVarEnc<Lit, C>>,
		y: &'a Box<dyn IntVarEnc<Lit, C>>,
		z: &'a Box<dyn IntVarEnc<Lit, C>>,
	) -> Self {
		Self { x, y, z }
	}
}

impl<'a, Lit: Literal, C: Coefficient> Checker for TernLeConstraint<'a, Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let x = LinExp::<_, _>::from(self.x).assign(solution);
		let y = LinExp::<_, _>::from(self.y).assign(solution);
		let z = LinExp::<_, _>::from(self.z).assign(solution);
		if x + y <= z {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
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
							db.add_clause(&[l_a, l_b, l_c].concat())?
						}
					}
				}
			}
		}
		Ok(())
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

	fn get_constant<Lit: Literal, C: Coefficient + 'static>(c: C) -> Box<dyn IntVarEnc<Lit, C>> {
		Box::new(Constant::new(c))
	}

	fn get_ord_x<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
		db: &mut DB,
		dom: IntervalSet<C>,
	) -> Box<dyn IntVarEnc<DB::Lit, C>> {
		let x = IntVarOrd::new(db, dom.into_iter(..).map(|iv| (iv, None)).collect());
		Box::new(x)
	}

	fn get_bin_x<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
		db: &mut DB,
		ub: C,
	) -> Box<dyn IntVarEnc<DB::Lit, C>> {
		let x = IntVarBin::_new(db, ub);
		Box::new(x)
	}

	#[test]
	fn constant_test() {
		let c = get_constant::<i32, i32>(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(&6), None);
		assert_eq!(c.geq(&45), Some(vec![]));
	}

	#[test]
	fn ord_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_ord_x::<_, i32>(&mut db, interval_set!(1..5, 5..7, 7..11));
		let consistency = x
			.as_any()
			.downcast_ref::<IntVarOrd<_, i32>>()
			.unwrap()
			._consistency();

		ImplicationChainEncoder::default()
			._encode(&mut db, &consistency)
			.unwrap();
		let x_lin: LinExp<i32, i32> = LinExp::from(&x);

		assert_eq!(x.lb(), 0);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(&6), Some(vec![2]));

		assert_eq!(x_lin.assign(&[-1, -2, -3]), 0);
		assert_eq!(x_lin.assign(&[1, -2, -3]), 4);
		assert_eq!(x_lin.assign(&[1, 2, -3]), 6);
		assert_eq!(x_lin.assign(&[1, 2, 3]), 10);

		let tern = TernLeConstraint {
			x: &x,
			y: &get_constant(0),
			z: &get_constant(6),
		};

		// TernLeEncoder::default().encode(&mut db, &tern).unwrap();
		// db.generate_solutions(
		// 	move |sol| tern.check(sol).is_ok() && consistency.check(sol).is_ok(),
		// 	3,
		// );

		db.num_var = 3;

		assert_sol!(db, TernLeEncoder::default(), 3, &tern =>
		vec![
		  vec![-1, -2, -3],
		  vec![1, -2, -3],
		  vec![1, 2, -3],
		]);
	}

	#[test]
	fn bin_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_bin_x(&mut db, 12);
		assert_eq!(x.geq(&3), Some(vec![1, 3]));
	}

	// 	#[test]
	// 	fn ord_plus_ord_leq_ord_test() {
	// 		let mut db = TestDB::new(0);
	// 		assert_sol!(
	// 			TernLeEncoder::default(),
	// 			0,
	// 			&TernLeConstraint {
	// 				x: &get_ord_x(&mut db, interval_set!(1..2, 5..7)),
	// 				y: &get_ord_x(&mut db, interval_set!(2..3, 4..5)),
	// 				z: &get_ord_x(&mut db, interval_set!(0..4, 4..11)),
	// 			}
	// 		);
	// 	}

	// 	// #[test]
	// 	fn ord_plus_ord_leq_bin_test() {
	// 		let mut db = TestDB::new(0);
	// 		assert_sol!(
	// 			TernLeEncoder::default(),
	// 			0,
	// 			&TernLeConstraint {
	// 				x: &get_ord_x(&mut db, interval_set!(1..2, 5..7)),
	// 				y: &get_ord_x(&mut db, interval_set!(2..3, 4..5)),
	// 				z: &get_bin_x(&mut db, 12),
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
	// 			x: &get_bin_x(&mut db, 12),
	// 			y: &get_bin_x(&mut db, 12),
	// 			z: &get_bin_x(&mut db, 12),
	// 		}
	// 	);
	// }
}
