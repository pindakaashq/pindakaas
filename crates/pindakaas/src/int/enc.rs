use iset::{interval_map, interval_set, IntervalMap, IntervalSet};
use rustc_hash::FxHashMap;

use super::display_dom;
use itertools::Itertools;
use std::collections::BTreeSet;
use std::fmt::Display;

use crate::helpers::{two_comp_bounds, unsigned_binary_range_ub};
use crate::int::{IntVar, TernLeConstraint, TernLeEncoder};
use crate::linear::{lex_geq_const, lex_leq_const, log_enc_add_fn};
use crate::Comparator;
use crate::{
	helpers::{as_binary, is_powers_of_two},
	linear::{LinExp, Part},
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

impl<Lit: Literal> From<Option<Lit>> for LitOrConst<Lit> {
	fn from(item: Option<Lit>) -> Self {
		match item {
			Some(l) => LitOrConst::Lit(l),
			None => LitOrConst::Const(false),
		}
	}
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

// TODO should be Not
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
			"({}):O ∈ {} [{}]",
			self.lbl,
			&self
				.dom()
				.iter(..)
				.map(|d| format!("{}..{}", d.start, d.end - C::one()))
				.join(","),
			self.lits()
		)
	}
}

pub(crate) const GROUND_BINARY_AT_LB: bool = false;

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarBin<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"({}):B ∈ {} [{}]",
			self.lbl,
			display_dom::<Lit, C>(&self.dom().iter(..).map(|d| d.end - C::one()).collect()),
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

		// assert!(
		// 	views
		// 		.iter(..)
		// 		.tuple_windows()
		// 		.all(|(a, b)| a.0.end == b.0.start),
		// 	"Expecting contiguous domain of intervals but was {views:?}"
		// );

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
	xs: Vec<LitOrConst<Lit>>,
	dom: BTreeSet<C>, // TODO deduplicate after IntVarEnc is part of IntVar
	lbl: String,
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	pub fn from_lits(xs: &[LitOrConst<Lit>], dom: &[C], lbl: String) -> Self {
		if GROUND_BINARY_AT_LB {
			panic!("Cannot create offset binary encoding `from_lits` without a given lower bound.")
		}

		Self {
			xs: xs.to_vec(),
			dom: dom.iter().cloned().collect(),
			lbl,
		}
	}

	pub fn from_dom<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, dom: &[C], lbl: String) -> Self {
		debug_assert!(&dom.iter().tuple_windows().all(|(a, b)| a <= b));
		let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
		Self {
			xs: Self::xs_from_bounds(db, lb, ub, &lbl),
			dom: dom.iter().cloned().collect(),
			lbl,
		}
	}

	fn xs_from_bounds<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		lb: C,
		ub: C,
		_lbl: &str,
	) -> Vec<LitOrConst<Lit>> {
		(0..IntVar::<DB::Lit, C>::required_lits(lb, ub))
			.map(|_i| (new_var!(db, format!("{}^{}", _lbl, _i))).into())
			.chain((!GROUND_BINARY_AT_LB && !lb.is_negative()).then_some(LitOrConst::Const(false)))
			.collect()
	}

	// TODO change to with_label or something
	pub fn from_bounds<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		lb: C,
		ub: C,
		lbl: String,
	) -> Self {
		Self {
			xs: Self::xs_from_bounds(db, lb, ub, &lbl),
			dom: num::range_inclusive(lb, ub).collect(),
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
			xs: terms
				.into_iter()
				.map(|(l, _)| l.into())
				.chain([LitOrConst::Const(false)])
				.collect(),
			dom: num::range_inclusive(*lb, *ub).collect(),
			lbl,
		}
	}

	/// Enforce domain on the encoding variables (bounds and gaps)
	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		self.encode_unary_constraint(db, &Comparator::GreaterEq, self.lb(), true)?;
		self.encode_unary_constraint(db, &Comparator::LessEq, self.ub(), true)?;
		for gap in self.dom.iter().tuple_windows().collect::<Vec<(&C, &C)>>() {
			for k in num::range_inclusive(*gap.0 + C::one(), *gap.1 - C::one()) {
				self.encode_neq(db, k)?;
			}
		}
		Ok(())
	}

	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn normalize(&self, k: C) -> C {
		if GROUND_BINARY_AT_LB {
			k - self.lb()
		} else {
			// encoding is grounded at the lb of the two comp representation
			k - two_comp_bounds(self.bits()).0
		}
	}

	/// Return conjunction of bits equivalent where `x=k`
	fn eq(&self, k: C) -> Result<Vec<Lit>, Unsatisfiable> {
		as_binary::<Lit, C>(self.normalize(k).into(), Some(self.bits()))
			.into_iter()
			.zip(self.xs(true).iter())
			.map(|(b, x)| if b { x.clone() } else { -x.clone() })
			.flat_map(|x| match x {
				LitOrConst::Lit(lit) => Some(Ok(lit)),
				LitOrConst::Const(true) => None,
				LitOrConst::Const(false) => Some(Err(Unsatisfiable)),
			})
			.collect()
	}

	/// Encode `x # k` where `# ∈ ≤,=,≥`
	pub(crate) fn encode_unary_constraint<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		cmp: &Comparator,
		k: C,
		force: bool,
	) -> Result {
		match cmp {
			Comparator::LessEq => {
				if k < self.lb() {
					Err(Unsatisfiable)
				} else if k >= self.ub() && !force {
					Ok(())
				} else {
					lex_leq_const(db, &self.xs(true), self.normalize(k).into(), self.bits())
				}
			}
			Comparator::Equal => self
				.eq(k)?
				.into_iter()
				.try_for_each(|cls| emit_clause!(db, &[cls])),
			Comparator::GreaterEq => {
				if k > self.ub() {
					Err(Unsatisfiable)
				} else if k <= self.lb() && !force {
					Ok(())
				} else {
					lex_geq_const(db, &self.xs(true), self.normalize(k).into(), self.bits())
				}
			}
		}
	}

	pub(crate) fn encode_neq<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB, k: C) -> Result {
		emit_clause!(db, &self.eq(k)?.iter().map(Lit::negate).collect::<Vec<_>>())
	}

	/// Get bits; option to invert the sign bit to create an unsigned binary representation offset by `-2^(k-1)`
	pub(crate) fn xs(&self, to_unsigned: bool) -> Vec<LitOrConst<Lit>> {
		if GROUND_BINARY_AT_LB {
			self.xs.clone()
		} else {
			self.xs[..self.xs.len() - 1]
				.iter()
				.cloned()
				.chain({
					let sign = self.xs.last().unwrap().clone();
					[if to_unsigned { -sign } else { sign }]
				})
				.collect()
		}
	}

	fn div(&self, _: &C) -> IntVarEnc<Lit, C> {
		todo!()
	}

	fn dom(&self) -> IntervalSet<C> {
		// TODO for now, do not add in gaps since it may interfere with coupling
		num::iter::range_inclusive(self.lb(), self.ub())
			.map(|i| i..(i + C::one()))
			.collect()
	}

	pub(crate) fn lb(&self) -> C {
		*self.dom.first().unwrap()
	}

	pub(crate) fn ub(&self) -> C {
		*self.dom.last().unwrap()
	}

	pub(crate) fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		self.ineq(v, true)
	}

	pub(crate) fn leq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		self.ineq(v, false)
	}

	fn ineq(&self, v: Range<C>, geq: bool) -> Vec<Vec<Lit>> {
		let v = self.normalize(v.start)..self.normalize(v.end);

		// The range 0..(2^n)-1 covered by the (unsigned) binary representation
		// let (range_lb, range_ub) = two_comp_bounds(self.bits());
		let range_lb = C::zero();
		let range_ub = unsigned_binary_range_ub::<C>(self.bits());

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
				as_binary::<Lit, C>(v.into(), Some(self.bits()))
					.into_iter()
					.zip(self.xs(true).into_iter())
					// if >=, find 0's, if <=, find 1's
					.filter_map(|(b, x)| (b != geq).then_some(x))
					// if <=, negate 1's to not 1's
					.map(|x| if geq { x } else { -x })
					// filter out fixed literals (possibly satisfying clause)
					.filter_map(|x| match x {
						LitOrConst::Lit(x) => Some(Ok(x)),
						LitOrConst::Const(true) => Some(Err(())), // clause satisfied
						LitOrConst::Const(false) => None,         // literal falsified
					})
					.collect::<Result<Vec<_>, _>>()
					.ok()
			}
		})
		.collect()
	}

	fn as_lin_exp(&self) -> LinExp<Lit, C> {
		let mut k = C::one();
		let mut add = C::zero(); // resulting from fixed terms
		let two = C::one() + C::one();
		let terms = self
			.xs(true)
			.into_iter()
			.filter_map(|x| {
				let term = match x {
					LitOrConst::Lit(l) => Some((l, k)),
					LitOrConst::Const(true) => {
						add += k;
						None
					}
					LitOrConst::Const(false) => None,
				};
				k *= two;
				term
			})
			.collect::<Vec<_>>();

		let offset: C = if GROUND_BINARY_AT_LB {
			self.lb()
		} else {
			two_comp_bounds(self.bits()).0
		};

		let lin_exp = LinExp::new().add_bounded_log_encoding(
			terms.as_slice(),
			// The Domain constraint bounds only account for the unfixed part of the offset binary notation
			self.lb() - offset - add,
			self.ub() - offset - add,
		);

		// The offset and the fixed value `add` are added to the constant
		lin_exp.add_constant(add + offset)
	}

	pub(crate) fn lits(&self) -> usize {
		self.xs
			.iter()
			.filter(|x| matches!(x, LitOrConst::Lit(_)))
			.count()
	}

	/// Number of bits in the encoding
	pub(crate) fn bits(&self) -> usize {
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
		} else {
			let z_bin = IntVarBin::from_dom(
				db,
				&self.dom.iter().cloned().map(|d| d + y).collect::<Vec<_>>(),
				format!("{}+{}", self.lbl, y),
			);

			encoder.encode(
				db,
				&TernLeConstraint {
					x: &IntVarEnc::Bin(self.clone()),
					y: &IntVarEnc::Const(y),
					cmp: &Comparator::Equal,
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
					.chain(h)
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
                            &Comparator::LessEq,
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

				const RETAIN_GAPS: bool = false;
				let dom = if RETAIN_GAPS {
					x_bin
						.dom
						.iter()
						.cartesian_product(y_bin.dom.iter())
						.map(|(a, b)| *a + *b)
						.collect::<Vec<_>>()
				} else {
					num::iter::range_inclusive(x_bin.lb() + y_bin.lb(), x_bin.ub() + y_bin.ub())
						.collect::<Vec<_>>()
				};

				let z = IntVarEnc::Bin(IntVarBin::from_lits(
					&log_enc_add_fn(
						db,
						&x_bin.xs(false),
						&y_bin.xs(false),
						&Comparator::Equal,
						LitOrConst::Const(false),
					)?,
					&dom,
					format!("{}+{}", x_bin.lbl, y_bin.lbl),
				));
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

	/// Returns cnf constraining `x<=v`
	pub(crate) fn leq_(&self, v: C) -> Vec<Vec<Lit>> {
		self.leq(v..(v + C::one()))
	}

	/// Returns cnf constraining `x<=a..b`
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

	/// Returns cnf constraining `x>=v`
	pub(crate) fn geq_(&self, v: C) -> Vec<Vec<Lit>> {
		self.geq(v..(v + C::one()))
	}

	/// Returns a clause constraining `x>=a..b`
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

	pub(crate) fn assign(&self, solution: &[Lit]) -> Result<C, CheckError<Lit>> {
		LinExp::from(self).assign(solution)
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
