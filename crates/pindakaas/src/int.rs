use iset::{interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use std::any::Any;
use std::ops::Range;

use crate::{
	linear::{log_enc_add, x_bin_le, LimitComp, LinExp, Part},
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
	pub(crate) c: C,
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

	fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		if self.c >= v.end - C::one() {
			vec![]
		} else {
			vec![vec![]]
		}
	}

	fn into_lin_exp(&self) -> LinExp<Lit, C> {
		LinExp::new().add_constant(self.c)
	}

	fn as_any(&self) -> &dyn Any {
		self
	}

	fn lits(&self) -> usize {
		0
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
		lbl: String,
	) -> Self {
		let xs = dom
			.into_iter(..)
			.map(|(v, lit)| {
				#[cfg(debug_assertions)]
				let lbl = format!("{lbl}>={v:?}");
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

	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		ImplicationChainEncoder::default()._encode(db, &self._consistency())
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

	fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		let v = v.end - C::one();
		if v <= self.lb() {
			vec![]
		} else if v > self.ub() {
			vec![vec![]]
		} else {
			match self.xs.overlap(v).collect::<Vec<_>>()[..] {
				[(_, x)] => vec![vec![x.clone()]],
				_ => panic!("No or multiples variables at {v:?}"),
			}
		}
	}

	fn into_lin_exp(&self) -> LinExp<Lit, C> {
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

	fn as_any(&self) -> &dyn Any {
		self
	}

	fn lits(&self) -> usize {
		self.xs.len()
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Clone, Debug)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	pub(crate) xs: Vec<Lit>,
	lb: Constant<C>,
	ub: Constant<C>,
}

impl<Lit: Literal + 'static, C: Coefficient + 'static> IntVarBin<Lit, C> {
	// TODO change to with_label or something
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, ub: C, lbl: String) -> Self {
		let bits = C::zero().leading_zeros() - ub.leading_zeros();
		Self {
			xs: (0..bits)
				.map(|i| {
					#[cfg(debug_assertions)]
					let lbl = format!("{}^{}", lbl, i);
					new_var!(db, lbl)
				})
				.collect(),
			lb: Constant::new(C::zero()), // TODO support non-zero
			ub: Constant::new(ub),
		}
	}

	pub fn _consistency(&self) -> TernLeConstraint<Lit, C> {
		TernLeConstraint {
			x: self,
			y: &self.lb,
			cmp: LimitComp::LessEq,
			z: &self.ub,
		}
	}

	pub fn consistent<DB: ClauseDatabase<Lit = Lit> + 'static>(&self, db: &mut DB) -> Result {
		TernLeEncoder::default().encode(db, &self._consistency())
	}
}

impl<Lit: Literal + 'static, C: Coefficient + 'static> IntVarEnc<Lit, C> for IntVarBin<Lit, C> {
	fn dom(&self) -> IntervalSet<C> {
		num::iter::range_inclusive(self.lb.c, self.ub.c)
			.map(|i| i..(i + C::one()))
			.collect()
	}

	fn clone_dyn(&self) -> Box<dyn IntVarEnc<Lit, C>> {
		Box::new(IntVarBin {
			xs: self.xs.clone(),
			lb: self.lb.clone(),
			ub: self.ub.clone(),
		})
	}

	fn lb(&self) -> C {
		self.lb.c
	}

	fn ub(&self) -> C {
		self.ub.c
	}

	// TODO return ref
	// TODO impl Index
	fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		num::iter::range_inclusive(
			std::cmp::max(self.lb(), v.start - C::one()),
			std::cmp::min(self.ub(), v.end - C::one() - C::one()),
		)
		.map(|v| {
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
				.collect::<Vec<_>>()
		})
		.collect()
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

	fn lits(&self) -> usize {
		self.xs.len()
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
				IntVarOrd::new(db, dom, String::from("x"))
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
					String::from("x"),
				)
			}
			Part::Dom(_terms, _l, _u) => todo!(),
		}
	}
}

pub(crate) trait IntVarEnc<Lit: Literal, C: Coefficient>: std::fmt::Debug {
	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>>;

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

	/// Return number of lits in encoding
	fn lits(&self) -> usize;
}

#[derive(Debug)]
pub(crate) struct TernLeConstraint<'a, Lit: Literal, C: Coefficient> {
	pub(crate) x: &'a dyn IntVarEnc<Lit, C>,
	pub(crate) y: &'a dyn IntVarEnc<Lit, C>,
	pub(crate) cmp: LimitComp,
	pub(crate) z: &'a dyn IntVarEnc<Lit, C>,
}

// TODO rename TernLeConstraint => TernLinConstraint/Encoder
impl<'a, Lit: Literal, C: Coefficient> TernLeConstraint<'a, Lit, C> {
	pub fn new(
		x: &'a dyn IntVarEnc<Lit, C>,
		y: &'a dyn IntVarEnc<Lit, C>,
		cmp: LimitComp,
		z: &'a dyn IntVarEnc<Lit, C>,
	) -> Self {
		Self { x, y, cmp, z }
	}
}

impl<'a, Lit: Literal, C: Coefficient> Checker for TernLeConstraint<'a, Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let x = LinExp::<_, _>::from(self.x).assign(solution);
		let y = LinExp::<_, _>::from(self.y).assign(solution);
		let z = LinExp::<_, _>::from(self.z).assign(solution);
		// TODO into LinearConstraint => Check?
		if match self.cmp {
			LimitComp::LessEq => x + y <= z,
			LimitComp::Equal => x + y == z,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

#[derive(Default)]
pub(crate) struct TernLeEncoder {}

impl<'a, DB: ClauseDatabase + 'static, C: Coefficient + 'static>
	Encoder<DB, TernLeConstraint<'a, DB::Lit, C>> for TernLeEncoder
{
	fn encode(&mut self, db: &mut DB, tern: &TernLeConstraint<DB::Lit, C>) -> Result {
		let TernLeConstraint { x, y, cmp, z } = tern;
		if let Some(x_bin) = x.as_any().downcast_ref::<IntVarBin<DB::Lit, C>>() {
			if let (Some(y_con), Some(z_con)) = (
				y.as_any().downcast_ref::<Constant<C>>(),
				z.as_any().downcast_ref::<Constant<C>>(),
			) {
				assert!(
					cmp == &LimitComp::LessEq,
					"Only support <= for x:B+y:Constant ? z:Constant"
				);
				return x_bin_le(
					db,
					x_bin
						.xs
						.iter()
						.map(|x| Some(x.clone()))
						.collect::<Vec<_>>()
						.as_slice(),
					(z_con.c - y_con.c).into(),
					x_bin.xs.len(),
				);
			} else if let (Some(y_bin), Some(z_bin)) = (
				y.as_any().downcast_ref::<IntVarBin<DB::Lit, C>>(),
				z.as_any().downcast_ref::<IntVarBin<DB::Lit, C>>(),
			) {
				assert!(
					cmp == &LimitComp::Equal,
					"Only support == for x:B+y:B ? z:B"
				);
				log_enc_add(db, &x_bin.xs, &y_bin.xs, &z_bin.xs, z_bin.lits())
			} else {
				unimplemented!("LHS binary variables only implemented for some cases (and not tested in general method) for {x:?}, {y:?}, {z:?}")
			}
		} else {
			assert!(cmp == &LimitComp::LessEq, "Only support <= for x+y ? z");
			for c_a in x.dom() {
				for c_b in y.dom() {
					let neg = |clauses: Vec<Vec<DB::Lit>>| -> Vec<Vec<DB::Lit>> {
						if clauses.is_empty() {
							vec![vec![]]
						} else if clauses.contains(&vec![]) {
							vec![]
						} else {
							clauses
								.into_iter()
								.map(|clause| clause.into_iter().map(|lit| lit.negate()).collect())
								.collect()
						}
					};

					// TODO tighten c_c.start
					let c_c = (std::cmp::min(c_a.start, c_b.start))
						..(((c_a.end - C::one()) + (c_b.end - C::one())) + C::one());
					let (a, b, c) = (
						neg(x.geq(c_a.clone())),
						neg(y.geq(c_b.clone())),
						z.geq(c_c.clone()),
					);

					for cls_a in &a {
						for cls_b in &b {
							for cls_c in &c {
								db.add_clause(
									&[cls_a.clone(), cls_b.clone(), cls_c.clone()].concat(),
								)?;
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

	fn get_constant<Lit: Literal, C: Coefficient + 'static>(c: C) -> Box<dyn IntVarEnc<Lit, C>> {
		Box::new(Constant::new(c))
	}

	fn get_ord_x<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
		db: &mut DB,
		dom: IntervalSet<C>,
		consistent: bool,
		lbl: String,
	) -> Box<dyn IntVarEnc<DB::Lit, C>> {
		let x = IntVarOrd::new(db, dom.into_iter(..).map(|iv| (iv, None)).collect(), lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		Box::new(x)
	}

	fn get_bin_x<DB: ClauseDatabase + 'static, C: Coefficient + 'static>(
		db: &mut DB,
		ub: C,
		consistent: bool,
		lbl: String,
	) -> Box<dyn IntVarEnc<DB::Lit, C>> {
		let x = IntVarBin::new(db, ub, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		Box::new(x)
	}

	#[test]
	fn constant_test() {
		let c = get_constant::<i32, i32>(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(6..7), Vec::<Vec<i32>>::new());
		assert_eq!(c.geq(45..46), vec![vec![]]);
	}

	#[test]
	fn bin_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_bin_x::<_, i32>(&mut db, 12, true, String::from("x"));
		let x_con = x
			.as_any()
			.downcast_ref::<IntVarBin<i32, i32>>()
			.unwrap()
			._consistency();
		let x_lin: LinExp<i32, i32> = LinExp::from(x.as_ref());

		assert_eq!(x.lits(), 4);
		assert_eq!(x.lb(), 0);
		assert_eq!(x.ub(), 12);
		assert_eq!(x.geq(7..8), vec![vec![1, 4]]); // 7-1=6 == 0110 (right-to-left!)
		assert_eq!(x.geq(5..8), vec![vec![1, 2, 4], vec![2, 4], vec![1, 4]]); // 4=0100,5=0101,6=0110

		assert_eq!(x_lin.assign(&[-1, -2, -3, -4]), 0);
		assert_eq!(x_lin.assign(&[1, -2, -3, -4]), 1);
		assert_eq!(x_lin.assign(&[1, 2, -3, -4]), 3);
		assert_eq!(x_lin.assign(&[1, 2, -3, 4]), 11);
		assert_eq!(x_lin.assign(&[1, 2, 3, 4]), 15);

		let tern = TernLeConstraint {
			x: x.as_ref(),
			y: &Constant::new(0),
			cmp: LimitComp::LessEq,
			z: &Constant::new(10), // TODO no consistency implemented for this bound yet
		};

		db.num_var = x.lits() as i32;

		db.generate_solutions(
			|sol| tern.check(sol).is_ok() && x_con.check(sol).is_ok(),
			db.num_var,
		);

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
		let x = IntVarBin::new(&mut db, 12, String::from("x"));
		let tern = TernLeConstraint {
			x: &x,
			y: &Constant::new(0),
			cmp: LimitComp::LessEq,
			z: &Constant::new(6),
		};
		db.num_var = x.lits() as i32;
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
		let x = get_ord_x::<_, i32>(
			&mut db,
			interval_set!(3..5, 5..7, 7..11),
			true,
			String::from("x"),
		);

		let x_lin: LinExp<i32, i32> = LinExp::from(x.as_ref());

		assert_eq!(x.lits(), 3);
		assert_eq!(x.lb(), 2);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(6..7), vec![vec![2]]);
		assert_eq!(x.geq(4..7), vec![vec![2]]);

		assert_eq!(x_lin.assign(&[-1, -2, -3]), 2);
		assert_eq!(x_lin.assign(&[1, -2, -3]), 4);
		assert_eq!(x_lin.assign(&[1, 2, -3]), 6);
		assert_eq!(x_lin.assign(&[1, 2, 3]), 10);

		let tern = TernLeConstraint {
			x: x.as_ref(),
			y: &Constant::new(0),
			cmp: LimitComp::LessEq,

			z: &Constant::new(6),
		};

		db.num_var = x.lits() as i32;

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3],
		  vec![1, -2, -3],
		  vec![1, 2, -3],
		]);
	}

	#[test]
	fn ord_plus_ord_le_ord_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true, String::from("x")),
			get_ord_x(&mut db, interval_set!(2..3, 4..5), true, String::from("y")),
			get_ord_x(&mut db, interval_set!(0..4, 4..11), true, String::from("z")),
		);
		let tern = TernLeConstraint {
			x: x.as_ref(),
			y: y.as_ref(),
			cmp: LimitComp::LessEq,
			z: z.as_ref(),
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		let x_con = x
			.as_any()
			.downcast_ref::<IntVarOrd<i32, i32>>()
			.unwrap()
			._consistency();
		let y_con = y
			.as_any()
			.downcast_ref::<IntVarOrd<i32, i32>>()
			.unwrap()
			._consistency();
		let z_con = z
			.as_any()
			.downcast_ref::<IntVarOrd<i32, i32>>()
			.unwrap()
			._consistency();
		db.generate_solutions(
			|sol| {
				tern.check(sol).is_ok()
					&& x_con.check(sol).is_ok()
					&& y_con.check(sol).is_ok()
					&& z_con.check(sol).is_ok()
			},
			db.num_var,
		);

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

	#[test]
	fn ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true, String::from("x")),
			get_constant(0),
			get_bin_x(&mut db, 7, true, String::from("z")),
		);
		let tern = TernLeConstraint {
			x: x.as_ref(),
			y: y.as_ref(),
			cmp: LimitComp::LessEq,
			z: z.as_ref(),
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		let x_con = x
			.as_any()
			.downcast_ref::<IntVarOrd<i32, i32>>()
			.unwrap()
			._consistency();
		let z_con = z
			.as_any()
			.downcast_ref::<IntVarBin<i32, i32>>()
			.unwrap()
			._consistency();
		db.generate_solutions(
			|sol| tern.check(sol).is_ok() && x_con.check(sol).is_ok() && z_con.check(sol).is_ok(),
			db.num_var,
		);

		assert_sol!(db => TernLeEncoder::default(), &tern => vec![
		vec![-1, -2, -3, -4, -5],
		vec![-1, -2, 3, -4, -5],
		vec![1, -2, 3, -4, -5],
		vec![-1, -2, -3, 4, -5],
		vec![1, -2, -3, 4, -5],
		vec![-1, -2, 3, 4, -5],
		vec![1, -2, 3, 4, -5],
		vec![-1, -2, -3, -4, 5],
		vec![1, -2, -3, -4, 5],
		vec![-1, -2, 3, -4, 5],
		vec![1, -2, 3, -4, 5],
		vec![-1, -2, -3, 4, 5],
		vec![1, -2, -3, 4, 5],
		vec![1, 2, -3, 4, 5],
		vec![-1, -2, 3, 4, 5],
		vec![1, -2, 3, 4, 5],
		vec![1, 2, 3, 4, 5],
			 ]);
	}

	#[test]
	fn ord_plus_ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true, String::from("x")),
			get_ord_x(&mut db, interval_set!(2..3, 4..5), true, String::from("y")),
			get_bin_x(&mut db, 12, true, String::from("z")),
		);
		let tern = TernLeConstraint {
			x: x.as_ref(),
			y: y.as_ref(),
			cmp: LimitComp::LessEq,
			z: z.as_ref(),
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

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
		// 	.downcast_ref::<IntVarBin<i32, i32>>()
		// 	.unwrap()
		// 	._consistency();
		// db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x_con.check(sol).is_ok()
		// 			&& y_con.check(sol).is_ok()
		// 			&& z_con.check(sol).is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5, -6, -7, 8],
		  vec![-1, -2, -3, -4, -5, -6, 7, -8],
		  vec![-1, -2, -3, -4, -5, -6, 7, 8],
		  vec![-1, -2, -3, -4, -5, 6, -7, -8],
		  vec![-1, -2, -3, -4, -5, 6, -7, 8],
		  vec![-1, -2, -3, -4, -5, 6, 7, -8],
		  vec![-1, -2, -3, -4, 5, -6, -7, -8],
		  vec![-1, -2, -3, -4, 5, -6, -7, 8],
		  vec![-1, -2, -3, -4, 5, -6, 7, -8],
		  vec![-1, -2, -3, -4, 5, 6, -7, -8],
		  vec![-1, -2, -3, -4, 5, 6, -7, 8],
		  vec![-1, -2, -3, -4, 5, 6, 7, -8],
		  vec![-1, -2, 3, -4, -5, -6, -7, 8],
		  vec![-1, -2, 3, -4, -5, -6, 7, -8],
		  vec![-1, -2, 3, -4, -5, -6, 7, 8],
		  vec![-1, -2, 3, -4, -5, 6, -7, -8],
		  vec![-1, -2, 3, -4, -5, 6, -7, 8],
		  vec![-1, -2, 3, -4, -5, 6, 7, -8],
		  vec![-1, -2, 3, -4, 5, -6, -7, 8],
		  vec![-1, -2, 3, -4, 5, -6, 7, -8],
		  vec![-1, -2, 3, -4, 5, 6, -7, -8],
		  vec![-1, -2, 3, -4, 5, 6, -7, 8],
		  vec![-1, -2, 3, -4, 5, 6, 7, -8],
		  vec![-1, -2, 3, 4, -5, -6, -7, 8],
		  vec![-1, -2, 3, 4, -5, -6, 7, -8],
		  vec![-1, -2, 3, 4, -5, -6, 7, 8],
		  vec![-1, -2, 3, 4, -5, 6, -7, 8],
		  vec![-1, -2, 3, 4, -5, 6, 7, -8],
		  vec![-1, -2, 3, 4, 5, -6, -7, 8],
		  vec![-1, -2, 3, 4, 5, -6, 7, -8],
		  vec![-1, -2, 3, 4, 5, 6, -7, 8],
		  vec![-1, -2, 3, 4, 5, 6, 7, -8],
		  vec![1, -2, -3, -4, -5, -6, -7, 8],
		  vec![1, -2, -3, -4, -5, -6, 7, -8],
		  vec![1, -2, -3, -4, -5, -6, 7, 8],
		  vec![1, -2, -3, -4, -5, 6, -7, -8],
		  vec![1, -2, -3, -4, -5, 6, -7, 8],
		  vec![1, -2, -3, -4, -5, 6, 7, -8],
		  vec![1, -2, -3, -4, 5, -6, -7, 8],
		  vec![1, -2, -3, -4, 5, -6, 7, -8],
		  vec![1, -2, -3, -4, 5, 6, -7, -8],
		  vec![1, -2, -3, -4, 5, 6, -7, 8],
		  vec![1, -2, -3, -4, 5, 6, 7, -8],
		  vec![1, -2, 3, -4, -5, -6, -7, 8],
		  vec![1, -2, 3, -4, -5, -6, 7, -8],
		  vec![1, -2, 3, -4, -5, -6, 7, 8],
		  vec![1, -2, 3, -4, -5, 6, -7, 8],
		  vec![1, -2, 3, -4, -5, 6, 7, -8],
		  vec![1, -2, 3, -4, 5, -6, -7, 8],
		  vec![1, -2, 3, -4, 5, -6, 7, -8],
		  vec![1, -2, 3, -4, 5, 6, -7, -8],
		  vec![1, -2, 3, -4, 5, 6, -7, 8],
		  vec![1, -2, 3, -4, 5, 6, 7, -8],
		  vec![1, -2, 3, 4, -5, -6, -7, 8],
		  vec![1, -2, 3, 4, -5, -6, 7, 8],
		  vec![1, -2, 3, 4, -5, 6, -7, 8],
		  vec![1, -2, 3, 4, -5, 6, 7, -8],
		  vec![1, -2, 3, 4, 5, -6, -7, 8],
		  vec![1, -2, 3, 4, 5, -6, 7, -8],
		  vec![1, -2, 3, 4, 5, 6, -7, 8],
		  vec![1, -2, 3, 4, 5, 6, 7, -8],
		  vec![1, 2, -3, -4, -5, -6, -7, 8],
		  vec![1, 2, -3, -4, -5, -6, 7, 8],
		  vec![1, 2, -3, -4, -5, 6, -7, 8],
		  vec![1, 2, -3, -4, 5, -6, -7, 8],
		  vec![1, 2, -3, -4, 5, 6, -7, 8],
		  vec![1, 2, -3, -4, 5, 6, 7, -8],
		  vec![1, 2, 3, -4, -5, -6, -7, 8],
		  vec![1, 2, 3, -4, -5, -6, 7, 8],
		  vec![1, 2, 3, -4, -5, 6, -7, 8],
		  vec![1, 2, 3, -4, 5, -6, -7, 8],
		  vec![1, 2, 3, -4, 5, 6, -7, 8],
		  vec![1, 2, 3, 4, -5, -6, 7, 8],
		  vec![1, 2, 3, 4, -5, 6, -7, 8],
		  vec![1, 2, 3, 4, 5, 6, -7, 8],
						]);
	}

	#[test]
	fn bin_plus_bin_eq_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_bin_x(&mut db, 2, true, String::from("x")),
			get_bin_x(&mut db, 3, true, String::from("y")),
			get_bin_x(&mut db, 5, true, String::from("z")),
		);

		let tern = TernLeConstraint {
			x: x.as_ref(),
			y: y.as_ref(),
			cmp: LimitComp::Equal,
			z: z.as_ref(),
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		let x_con = x
			.as_any()
			.downcast_ref::<IntVarBin<i32, i32>>()
			.unwrap()
			._consistency();
		let y_con = y
			.as_any()
			.downcast_ref::<IntVarBin<i32, i32>>()
			.unwrap()
			._consistency();
		let z_con = z
			.as_any()
			.downcast_ref::<IntVarBin<i32, i32>>()
			.unwrap()
			._consistency();
		db.generate_solutions(
			|sol| {
				tern.check(sol).is_ok()
					&& x_con.check(sol).is_ok()
					&& y_con.check(sol).is_ok()
					&& z_con.check(sol).is_ok()
			},
			db.num_var,
		);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		vec![-1, -2, -3, -4, -5, -6, -7],
		vec![-1, -2, -3, 4, -5, 6, -7],
		vec![-1, -2, 3, -4, 5, -6, -7],
		vec![-1, -2, 3, 4, 5, 6, -7],
		vec![-1, 2, -3, -4, -5, 6, -7],
		vec![-1, 2, -3, 4, -5, -6, 7],
		vec![-1, 2, 3, -4, 5, 6, -7],
		vec![-1, 2, 3, 4, 5, -6, 7],
		vec![1, -2, -3, -4, 5, -6, -7],
		vec![1, -2, -3, 4, 5, 6, -7],
		vec![1, -2, 3, -4, -5, 6, -7],
		vec![1, -2, 3, 4, -5, -6, 7],
			 ]);
	}
}
