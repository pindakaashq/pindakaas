use iset::{interval_map, interval_set, IntervalMap, IntervalSet};
use rustc_hash::FxHashMap;

use super::display_dom;
use itertools::Itertools;
use std::fmt::Display;

use crate::int::{IntVar, TernLeConstraint, TernLeEncoder};
use crate::{
	helpers::{as_binary, is_powers_of_two, unsigned_binary_range_ub},
	linear::{LimitComp, LinExp, Part},
	trace::{emit_clause, new_var},
	CheckError, Checker, ClauseDatabase, Coefficient, Encoder, Literal, PosCoeff, Result,
	Unsatisfiable,
};
use std::{
	collections::HashSet,
	fmt,
	hash::BuildHasherDefault,
	ops::{Neg, Range},
};

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LitOrConst<Lit: Literal> {
	Lit(Lit),
	Const(bool),
}

impl<Lit: Literal> From<Lit> for LitOrConst<Lit> {
	fn from(item: Lit) -> Self {
		LitOrConst::Lit(item)
	}
}

impl<Lit: Literal> From<bool> for LitOrConst<Lit> {
	fn from(item: bool) -> Self {
		LitOrConst::Const(item)
	}
}

impl<Lit: Literal> Display for LitOrConst<Lit> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LitOrConst::Const(b) => write!(f, "{}", *b as i32),
			LitOrConst::Lit(l) => write!(f, "b{l:?}"),
		}
	}
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

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarOrd<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:O ∈ {}",
			self.lbl,
			display_dom(&self.dom().iter(..).map(|d| d.end - C::one()).collect())
		)
	}
}

pub(crate) const GROUND_BINARY_AT_LB: bool = false;

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarBin<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:B ∈ {} [{}]",
			self.lbl,
			display_dom(&self.dom().iter(..).map(|d| d.end - C::one()).collect()),
			self.lits()
		)
	}
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarOrd<Lit: Literal, C: Coefficient> {
	pub(crate) xs: IntervalMap<C, Lit>,
	pub(crate) lbl: String,
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	pub fn from_bounds<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		lb: C,
		ub: C,
		lbl: String,
	) -> Self {
		Self::from_dom(
			db,
			num::iter::range_inclusive(lb, ub)
				.collect::<Vec<_>>()
				.as_slice(),
			lbl,
		)
	}

	pub fn from_dom<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, dom: &[C], lbl: String) -> Self {
		Self::from_syms(
			db,
			dom.iter()
				.tuple_windows()
				.map(|(&a, &b)| (a + C::one())..(b + C::one()))
				.collect(),
			lbl,
		)
	}

	pub fn from_syms<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		syms: IntervalSet<C>,
		lbl: String,
	) -> Self {
		Self::from_views(db, syms.into_iter(..).map(|c| (c, None)).collect(), lbl)
	}

	pub fn from_views<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		views: IntervalMap<C, Option<DB::Lit>>,
		lbl: String,
	) -> Self {
		assert!(!views.is_empty());
		assert!(
			views
				.iter(..)
				.tuple_windows()
				.all(|(a, b)| a.0.end == b.0.start),
			"Expecting contiguous domain of intervals but was {views:?}"
		);

		let xs = views
			.into_iter(..)
			.map(|(v, lit)| {
				#[cfg(feature = "trace")]
				let lbl = format!("{lbl}>={}..{}", v.start, v.end - C::one());
				(v, lit.unwrap_or_else(|| new_var!(db, lbl)))
			})
			.collect::<IntervalMap<_, _>>();
		Self { xs, lbl }
	}

	pub fn consistency(&self) -> ImplicationChainConstraint<Lit> {
		ImplicationChainConstraint {
			lits: self.xs.values(..).cloned().collect::<Vec<_>>(),
		}
	}

	#[allow(dead_code)]
	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		ImplicationChainEncoder::default()._encode(db, &self.consistency())
	}

	pub fn div(&self, c: &C) -> IntVarEnc<Lit, C> {
		assert!(*c == C::one() + C::one(), "Can only divide IntVarOrd by 2");
		let xs = self
			.xs
			.clone()
			.into_iter(..)
			.filter(|(c, _)| (c.end - C::one()).is_even())
			.map(|(c, l)| (((c.end - C::one()) / (C::one() + C::one())), l))
			.map(|(c, l)| (c..(c + C::one()), l))
			.collect::<IntervalMap<_, _>>();

		if xs.is_empty() {
			IntVarEnc::Const(self.lb() / *c)
		} else {
			IntVarOrd {
				xs,
				lbl: self.lbl.clone(),
			}
			.into()
		}
	}

	pub fn dom(&self) -> IntervalSet<C> {
		std::iter::once(self.lb()..(self.lb() + C::one()))
			.chain(self.xs.intervals(..))
			.collect()
	}

	pub fn leqs(&self) -> Vec<(Range<C>, Vec<Vec<Lit>>)> {
		self.xs
			.iter(..)
			.map(|(v, x)| {
				(
					(v.start - C::one())..(v.end - C::one()),
					vec![vec![x.negate()]],
				)
			})
			.chain(std::iter::once((self.ub()..self.ub() + C::one(), vec![])))
			.collect()
	}

	pub fn geqs(&self) -> Vec<(Range<C>, Vec<Vec<Lit>>)> {
		std::iter::once((self.lb()..(self.lb() + C::one()), vec![]))
			.chain(self.xs.iter(..).map(|(v, x)| (v, vec![vec![x.clone()]])))
			.collect()
	}

	pub fn lb(&self) -> C {
		self.xs.range().unwrap().start - C::one()
	}

	pub fn ub(&self) -> C {
		self.xs.range().unwrap().end - C::one()
	}

	pub fn leq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		let v = v.start + C::one(); // [x<=v] = [x < v+1]
		if v <= self.lb() {
			vec![vec![]]
		} else if v > self.ub() {
			vec![]
		} else {
			match self.xs.overlap(v).collect::<Vec<_>>()[..] {
				[(_, x)] => vec![vec![x.negate()]],
				_ => panic!("No or multiples literals at {v:?} for var {self:?}"),
			}
		}
	}

	pub fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		let v = v.end - C::one();
		if v <= self.lb() {
			vec![]
		} else if v > self.ub() {
			vec![vec![]]
		} else {
			match self.xs.overlap(v).collect::<Vec<_>>()[..] {
				[(_, x)] => vec![vec![x.clone()]],
				_ => panic!("No or multiples literals at {v:?} for var {self:?}"),
			}
		}
	}

	pub fn as_lin_exp(&self) -> LinExp<Lit, C> {
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

	pub fn lits(&self) -> usize {
		self.xs.len()
	}
}

pub(crate) struct ImplicationChainConstraint<Lit: Literal> {
	lits: Vec<Lit>,
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

#[derive(Debug, Clone)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	pub(crate) xs: Vec<Lit>,
	lb: C,
	ub: C,
	lbl: String,
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	// TODO change to with_label or something
	pub fn from_bounds<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		lb: C,
		ub: C,
		lbl: String,
	) -> Self {
		Self {
			xs: (0..IntVar::required_bits(lb, ub))
				.map(|_i| new_var!(db, format!("{}^{}", lbl, _i)))
				.collect(),
			lb,
			ub,
			lbl,
		}
	}

	pub fn from_terms(
		terms: Vec<(Lit, PosCoeff<C>)>,
		lb: PosCoeff<C>,
		ub: PosCoeff<C>,
		lbl: String,
	) -> Self {
		debug_assert!(is_powers_of_two(
			terms
				.iter()
				.map(|(_, c)| **c)
				.collect::<Vec<_>>()
				.as_slice()
		));
		Self {
			xs: terms.into_iter().map(|(l, _)| l).collect(),
			lb: *lb, // TODO support non-zero
			ub: *ub,
			lbl,
		}
	}

	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		let mut encoder = TernLeEncoder::default();
		if !GROUND_BINARY_AT_LB {
			encoder.encode(
				db,
				&TernLeConstraint {
					x: &IntVarEnc::Const(self.lb),
					y: &IntVarEnc::Const(C::zero()),
					cmp: LimitComp::LessEq,
					z: &IntVarEnc::Bin(self.clone()),
				},
			)?;
		}
		encoder.encode(
			db,
			&TernLeConstraint {
				x: &IntVarEnc::Bin(self.clone()),
				y: &IntVarEnc::Const(C::zero()),
				cmp: LimitComp::LessEq,
				z: &IntVarEnc::Const(self.ub),
			},
		)
	}

	fn div(&self, _: &C) -> IntVarEnc<Lit, C> {
		todo!()
	}

	fn dom(&self) -> IntervalSet<C> {
		num::iter::range_inclusive(self.lb, self.ub)
			.map(|i| i..(i + C::one()))
			.collect()
	}

	pub(crate) fn lb(&self) -> C {
		self.lb
	}

	pub(crate) fn ub(&self) -> C {
		self.ub
	}

	pub(crate) fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		self.ineq(v, true)
	}

	pub(crate) fn leq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		self.ineq(v, false)
	}

	fn ineq(&self, v: Range<C>, geq: bool) -> Vec<Vec<Lit>> {
		// TODO could *maybe* be domain lb/ub
		let v = if GROUND_BINARY_AT_LB {
			(v.start - self.lb())..(v.end - self.lb())
		} else {
			v
		};

		// The range 0..(2^n)-1 covered by the (unsigned) binary representation
		let range_lb = C::zero();
		let range_ub = unsigned_binary_range_ub::<C>(self.lits());

		num::iter::range(
			std::cmp::max(range_lb - C::one(), v.start),
			std::cmp::min(v.end, range_ub + C::one() + C::one()),
		)
		.filter_map(|v| {
			let v = if geq { v - C::one() } else { v + C::one() };
			if v < range_lb {
				(!geq).then_some(vec![])
			} else if v > range_ub {
				geq.then_some(vec![])
			} else {
				Some(
					as_binary(v.into(), Some(self.lits()))
						.into_iter()
						.zip(self.xs.iter())
						// if >=, find 0s, if <=, find 1s
						.filter_map(|(b, x)| (b != geq).then_some(x))
						.map(|x| if geq { x.clone() } else { x.negate() })
						.collect(),
				)
			}
		})
		.collect()
	}

	fn as_lin_exp(&self) -> LinExp<Lit, C> {
		let mut k = C::one();
		let two = C::one() + C::one();
		let terms = self
			.xs
			.iter()
			.map(|x| {
				let term = (x.clone(), k);
				k *= two;
				term
			})
			.collect::<Vec<_>>();
		let lin_exp = LinExp::new().add_bounded_log_encoding(terms.as_slice(), self.lb, self.ub);
		if GROUND_BINARY_AT_LB {
			lin_exp.add_constant(self.lb)
		} else {
			lin_exp
		}
	}

	pub(crate) fn lits(&self) -> usize {
		self.xs.len()
	}

	pub(crate) fn add<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		encoder: &mut TernLeEncoder,
		y: C,
	) -> Result<Self> {
		if y.is_zero() {
			Ok(self.clone())
		} else if GROUND_BINARY_AT_LB {
			Ok(IntVarBin {
				xs: self.xs.clone(),
				lb: self.lb() + y,
				ub: self.ub() + y,
				lbl: format!("{}+{}", self.lbl, y),
			})
		} else {
			let z_bin = IntVarBin::from_bounds(
				db,
				self.lb() + y,
				self.ub() + y,
				format!("{}+{}", self.lbl, y),
			);

			encoder.encode(
				db,
				&TernLeConstraint {
					x: &IntVarEnc::Bin(self.clone()),
					y: &IntVarEnc::Const(y),
					cmp: LimitComp::Equal,
					z: &IntVarEnc::Bin(z_bin.clone()),
				},
			)?;
			Ok(z_bin)
		}
	}
}

#[derive(Debug, Clone)]
pub(crate) enum IntVarEnc<Lit: Literal, C: Coefficient> {
	Ord(IntVarOrd<Lit, C>),
	Bin(IntVarBin<Lit, C>),
	Const(C),
}

const COUPLE_DOM_PART_TO_ORD: bool = false;

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> {
	/// Constructs (one or more) IntVar `ys` for linear expression `xs` so that ∑ xs ≦ ∑ ys
	pub fn from_part<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		xs: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
		lbl: String,
	) -> Vec<Self> {
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
					.collect::<IntervalMap<_, _>>();
				vec![IntVarEnc::Ord(IntVarOrd::from_views(db, dom, lbl))]
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				let dom = std::iter::once(&(terms[0].0.clone(), C::zero().into()))
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
					.collect::<IntervalMap<_, _>>();
				vec![IntVarEnc::Ord(IntVarOrd::from_views(db, dom, lbl))]
			}
			Part::Dom(terms, l, u) => {
                // TODO account for bounds (or even better, create IntVarBin)
                if COUPLE_DOM_PART_TO_ORD {
                    // TODO old method (which at least respected bounds)
				let x_bin =
					IntVarBin::from_terms(terms.to_vec(), l.clone(), u.clone(), String::from("x"));
				let x_ord = IntVarEnc::Ord(IntVarOrd::from_bounds(db, x_bin.lb(), x_bin.ub(), String::from("x")));

				TernLeEncoder::default()
					.encode(
						db,
						&TernLeConstraint::new(
                            &x_ord,
							&IntVarEnc::Const(C::zero()),
							LimitComp::LessEq,
							&x_bin.into(),
						),
					)
					.unwrap();
                vec![x_ord]
                } else {
                terms.iter().enumerate().map(|(i,(lit, coef))| {IntVarEnc::Ord(IntVarOrd::from_views(
                                db,
                                interval_map! { C::one()..(**coef+C::one()) => Some(lit.clone()) },
                                format!("{lbl}^{i}")
                                ))}).collect()
                }
			}

            // TODO Not so easy to transfer a binary encoded int var
			// Part::Dom(terms, l, u) => {
			// let coef = (terms[0].1);
			// let false_ if (coef > 1).then(|| let false_ = Some(new_var!(db)); emit_clause!(&[-false_]); false_ });
			// let terms = (1..coef).map(|_| false_.clone()).chain(terms.to_vec());

			// IntVarEnc::Bin(IntVarBin::from_terms(
			// 	terms.to_vec(),
			// 	l.clone(),
			// 	u.clone(),
			// 	String::from("x"),
			// ))},
		}
	}

	#[allow(dead_code)]
	pub(crate) fn from_dom<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		dom: &[C],
		lbl: String,
	) -> Result<IntVarEnc<DB::Lit, C>> {
		match dom {
			[] => Err(Unsatisfiable),
			[d] => Ok(IntVarEnc::Const(*d)),
			dom => Ok(IntVarOrd::from_dom(db, dom, lbl).into()),
		}
	}

	pub(crate) fn add<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		encoder: &mut TernLeEncoder,
		y: &IntVarEnc<Lit, C>,
		lb: Option<C>,
		ub: Option<C>,
		// cmp: &LimitComp,
		// enc: &'a mut dyn Encoder<DB, TernLeConstraint<'a, DB, C>>,
	) -> Result<IntVarEnc<Lit, C>> {
		let comp_lb = self.lb() + y.lb();
		let lb = std::cmp::max(lb.unwrap_or(comp_lb), comp_lb);

		let comp_ub = self.ub() + y.ub();
		let ub = std::cmp::min(ub.unwrap_or(comp_ub), comp_ub);

		match (self, y) {
			(IntVarEnc::Const(a), IntVarEnc::Const(b)) => Ok(IntVarEnc::Const(*a + *b)),
			// TODO only used in sorters which enforce the constraints later!
			(IntVarEnc::Const(c), x) | (x, IntVarEnc::Const(c)) if c.is_zero() => Ok(x.clone()),
			(IntVarEnc::Ord(x), IntVarEnc::Ord(y)) => Ok(IntVarEnc::Ord(IntVarOrd::from_syms(
				db,
				ord_plus_ord_le_ord_sparse_dom(
					x.dom().iter(..).map(|d| d.end - C::one()).collect(),
					y.dom().iter(..).map(|d| d.end - C::one()).collect(),
					lb,
					ub,
				),
				format!("{}+{}", x.lbl, y.lbl),
			))),
			(IntVarEnc::Ord(x), IntVarEnc::Const(y)) | (IntVarEnc::Const(y), IntVarEnc::Ord(x)) => {
				let xs =
					x.xs.clone()
						.into_iter(..)
						.map(|(c, l)| ((c.start + *y)..(c.end + *y), l))
						.collect();
				Ok(IntVarOrd {
					xs,
					lbl: format!("{}+{}", x.lbl, y),
				}
				.into())
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Bin(y_bin)) => {
				if GROUND_BINARY_AT_LB && comp_lb != x_bin.lb() + y_bin.lb() {
					unimplemented!(
					"Not implemented addition for unequal lbs for zero-grounded binary encodings"
				);
				}
				let z = IntVarEnc::Bin(IntVarBin::from_bounds(
					db,
					lb,
					ub,
					format!("{}+{}", x_bin.lbl, y_bin.lbl),
				));
				encoder.encode(
					db,
					&TernLeConstraint {
						x: &IntVarEnc::Bin(x_bin.clone()),
						y,
						cmp: LimitComp::Equal,
						z: &z,
					},
				)?;
				Ok(z)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y))
			| (IntVarEnc::Const(y), IntVarEnc::Bin(x_bin)) => {
				Ok(IntVarEnc::Bin(x_bin.add(db, encoder, *y)?))
			}
			_ => todo!("{self} + {y}"),
		}
	}

	pub(crate) fn leqs(&self) -> Vec<(Range<C>, Vec<Vec<Lit>>)> {
		match self {
			IntVarEnc::Ord(o) => o.leqs(),
			x => x
				.dom()
				.into_iter(..)
				.map(|c| (c.clone(), x.leq(c)))
				.collect(),
		}
	}

	pub(crate) fn geqs(&self) -> Vec<(Range<C>, Vec<Vec<Lit>>)> {
		match self {
			IntVarEnc::Ord(o) => o.geqs(),
			x => x
				.dom()
				.into_iter(..)
				.map(|c| (c.clone(), x.geq(c)))
				.collect(),
		}
	}

	/// Returns cnf constraining `x<=v`, which is empty if true and contains empty if false
	pub(crate) fn leq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.leq(v),
			IntVarEnc::Bin(b) => b.leq(v),
			IntVarEnc::Const(c) => {
				let v = v.start + C::one(); // [x<=v] = [x < v+1]
				if v <= *c {
					vec![vec![]]
				} else {
					vec![]
				}
			}
		}
	}

	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	pub(crate) fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.geq(v),
			IntVarEnc::Bin(b) => b.geq(v),
			IntVarEnc::Const(c) => {
				let v = v.end - C::one();
				if v <= *c {
					vec![]
				} else {
					vec![vec![]]
				}
			}
		}
	}

	pub(crate) fn div(&self, c: &C) -> IntVarEnc<Lit, C> {
		match self {
			IntVarEnc::Ord(o) => o.div(c),
			IntVarEnc::Bin(b) => b.div(c),
			IntVarEnc::Const(m) => IntVarEnc::Const(*m / *c),
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

	pub(crate) fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		match self {
			IntVarEnc::Ord(o) => o.consistent(db),
			IntVarEnc::Bin(b) => b.consistent(db),
			IntVarEnc::Const(_) => Ok(()),
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
	/// Return number of lits in encoding
	#[allow(dead_code)]
	pub(crate) fn lits(&self) -> usize {
		match self {
			IntVarEnc::Ord(o) => o.lits(),
			IntVarEnc::Bin(b) => b.lits(),
			IntVarEnc::Const(_) => 0,
		}
	}
}

impl<Lit: Literal, C: Coefficient> From<IntVarBin<Lit, C>> for IntVarEnc<Lit, C> {
	fn from(b: IntVarBin<Lit, C>) -> Self {
		Self::Bin(b)
	}
}

impl<Lit: Literal, C: Coefficient> From<IntVarOrd<Lit, C>> for IntVarEnc<Lit, C> {
	fn from(o: IntVarOrd<Lit, C>) -> Self {
		Self::Ord(o)
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarEnc<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			IntVarEnc::Ord(o) => o.fmt(f),
			IntVarEnc::Bin(b) => b.fmt(f),
			IntVarEnc::Const(o) => write!(f, "{o:?}"),
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
