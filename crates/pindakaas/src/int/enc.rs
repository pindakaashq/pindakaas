#![allow(unused_imports, unused_variables, dead_code)]
use super::bin::BinEnc;
use super::display_dom;
use super::helpers::to_lex_bits;
use super::ord::OrdEnc;
use crate::helpers::{is_sorted, negate_cnf};
use crate::int::helpers::filter_fixed;
use iset::{interval_map, interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::fmt::Display;

use crate::helpers::{two_comp_bounds, unsigned_binary_range_ub};
use crate::int::{helpers::required_lits, Dom, TernLeConstraint, TernLeEncoder};
use crate::linear::{lex_geq_const, lex_leq_const, log_enc_add_fn};
use crate::{
	helpers::{as_binary, is_powers_of_two},
	linear::{LinExp, Part},
	trace::{emit_clause, new_var},
	CheckError, Checker, ClauseDatabase, Coefficient, Encoder, Literal, PosCoeff, Result,
	Unsatisfiable,
};
use crate::{Cnf, Comparator};
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

const RETAIN_GAPS: bool = false;

impl<Lit: Literal> TryFrom<LitOrConst<Lit>> for bool {
	type Error = ();
	fn try_from(item: LitOrConst<Lit>) -> Result<Self, Self::Error> {
		match item {
			LitOrConst::Const(b) => Ok(b),
			_ => Err(()),
		}
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

pub(crate) const GROUND_BINARY_AT_LB: bool = true;

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarBin<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"({}):B ∈ {} [{}]",
			self.lbl,
			&display_dom(
				&self
					.dom()
					.iter(..)
					.map(|d| d.end - C::one())
					.collect::<Vec<_>>()
			),
			self.lits()
		)
	}
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarOrd<Lit: Literal, C: Coefficient> {
	pub(crate) xs: IntervalMap<C, Lit>,
	pub(crate) lbl: String,
	pub(crate) lb: C,
	pub(crate) ub_iv: Range<C>,
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	pub fn from_bounds<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		lb: C,
		ub: C,
		lbl: String,
	) -> Self {
		assert!(lb <= ub);
		Self::from_dom(
			db,
			num::iter::range_inclusive(lb, ub)
				.collect::<Vec<_>>()
				.as_slice(),
			lbl,
		)
	}

	fn interval_set_from_dom(dom: &[C]) -> IntervalSet<C> {
		assert!(is_sorted(dom));
		dom.iter()
			.tuple_windows()
			.map(|(&a, &b)| (a + C::one())..(b + C::one()))
			.collect()
	}

	pub fn from_dom<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, dom: &[C], lbl: String) -> Self {
		Self::from_syms(db, Self::interval_set_from_dom(dom), lbl)
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

		let lb = views.intervals(..).next().unwrap().start - C::one(); // lb just before the first literal
		let ub = views.intervals(..).last().unwrap().end; // but ub is the end interval of last literal!

		let ub_iv = ub..(ub + C::one()); // becomes interval of size 1

		let xs = views
			.into_iter(..)
			.map(|(v, lit)| {
				#[cfg(feature = "trace")]
				let lbl = format!("{lbl}>={}..{}", v.start, v.end - C::one());
				(v, lit.unwrap_or_else(|| new_var!(db, lbl)))
			})
			.collect::<IntervalMap<_, _>>();
		Self { xs, lb, ub_iv, lbl }
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
		todo!();
		/*
		assert!(*c == C::one() + C::one(), "Can only divide IntVarOrd by 2");
		let xs = self
			.xs
			.clone()
			.into_iter(..)
			.filter(|(c, _)| (c.end - C::one()).is_even())
			.map(|(c, l)| (((c.end - C::one()) / (C::one() + C::one())), l))
			.map(|(c, l)| (c..(c + C::one()), Some(l)))
			.collect::<IntervalMap<_, _>>();

		if xs.is_empty() {
			IntVarEnc::Const(self.lb() / *c)
		} else {
			IntVarEnc::Ord(
				IntVarOrd::from_views(
				&mut Cnf::<Lit>::default(),
				xs,
				self.lbl.clone(),
			)
				)
		}
		*/
	}

	pub fn dom(&self) -> IntervalSet<C> {
		let xs = self.xs();
		xs[..(xs.len() - 1)]
			.iter()
			.map(|(iv, _)| iv)
			.cloned()
			.collect()
	}

	pub fn xs(&self) -> Vec<(Range<C>, Vec<Vec<Lit>>)> {
		[(self.lb_iv(), vec![])]
			.into_iter()
			.chain(self.xs.iter(..).map(|(v, x)| (v, vec![vec![x.clone()]])))
			.chain([(self.ub_iv(), vec![vec![]])])
			.collect()
	}

	pub fn geqs(&self) -> Vec<(Range<C>, Vec<Vec<Lit>>)> {
		self.xs()
			.into_iter()
			// .map(|(iv, l)| (iv, l)))
			.collect()
	}

	pub fn leqs(&self) -> Vec<(Range<C>, Vec<Vec<Lit>>)> {
		self.xs()
			.into_iter()
			.map(|(iv, cnf)| {
				(
					((iv.start - C::one())..(iv.end - C::one())),
					negate_cnf(cnf),
				)
			})
			.collect()
	}

	fn lb_iv(&self) -> Range<C> {
		self.lb..self.xs.intervals(..).next().unwrap().start
	}

	fn ub_iv(&self) -> Range<C> {
		self.ub_iv.clone()
	}

	pub fn lb(&self) -> C {
		self.lb
	}

	pub fn ub(&self) -> C {
		self.ub_iv.start - C::one()
	}

	pub fn leq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		let v = v.start + C::one(); // [x<=v] = [x < v+1]
		if v <= self.lb_iv().end - C::one() {
			vec![vec![]]
		} else if v >= self.ub_iv().start {
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
		if v <= self.lb_iv().end - C::one() {
			vec![] // true
		} else if v >= self.ub_iv().start {
			vec![vec![]] // false
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

	pub fn mul<DB: ClauseDatabase<Lit = Lit>>(self, _: &mut DB, c: C) -> Self {
		assert!(!c.is_zero());
		let xs_vec = self
			.xs()
			.into_iter()
			.map(|(iv, cnf)| {
				(
					(
						(((iv.start - C::one()) * c) + C::one()),
						(((iv.end - C::one()) * c) + C::one()),
					),
					cnf,
				)
			})
			.collect_vec();

		let xs_vec = if c.is_positive() {
			xs_vec
				.into_iter()
				.map(|((l, r), lit)| (l..r, lit))
				.collect_vec()
		} else {
			xs_vec
				.into_iter()
				.map(|((l, r), lit)| (r..l, negate_cnf(lit)))
				.rev()
				.collect_vec()
		};

		let lb = xs_vec[0].0.start - C::one();
		let xs = xs_vec[1..xs_vec.len() - 1]
			.iter()
			.map(|(iv, lit)| (iv.clone(), lit[0][0].clone()))
			.collect();
		let ub_iv = xs_vec[xs_vec.len() - 1].0.clone();

		Self {
			xs,
			lb,
			ub_iv,
			lbl: format!("{}*{}", c, self.lbl.clone()),
		}
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
	pub(crate) dom: Dom<C>, // TODO deduplicate after IntVarEnc is part of IntVar
	lbl: String,
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	pub fn from_lits(xs: &[LitOrConst<Lit>], dom: Dom<C>, lbl: String) -> Self {
		if GROUND_BINARY_AT_LB {
			panic!("Cannot create offset binary encoding `from_lits` without a given lower bound.")
		}

		let lits = required_lits(dom.lb(), dom.ub());
		assert!(xs.len() >= lits);

		let xs = xs.to_vec();
		// TODO ..
		// let mut xs = xs.to_vec();
		// let (lb, ub) = (dom.lb(), dom.ub());
		// if !lb.is_negative() {
		// 	// if lb is >=0
		// 	xs.push(LitOrConst::Const(false));
		// } else if ub.is_negative() {
		// 	// if ub is < 0
		// 	xs.push(LitOrConst::Const(true));
		// }

		Self { xs, dom, lbl }
	}

	pub fn from_dom<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, dom: Dom<C>, lbl: String) -> Self {
		Self {
			xs: Self::xs_from_bounds(db, dom.lb(), dom.ub(), &lbl),
			dom,
			lbl,
		}
	}

	fn xs_from_bounds<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		lb: C,
		ub: C,
		_lbl: &str,
	) -> Vec<LitOrConst<Lit>> {
		(0..required_lits(lb, ub))
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
			dom: Dom::from_bounds(lb, ub),
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
			dom: Dom::from_bounds(*lb, *ub),
			lbl,
		}
	}

	/// Enforce domain on the encoding variables (bounds and gaps)
	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		self.encode_unary_constraint(db, &Comparator::GreaterEq, self.lb(), true)?;
		self.encode_unary_constraint(db, &Comparator::LessEq, self.ub(), true)?;
		for (a, b) in self.dom.ranges.iter().tuple_windows() {
			for k in num::range_inclusive(a.1 + C::one(), b.0 - C::one()) {
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
			k.checked_sub(&two_comp_bounds(self.bits()).0).unwrap()
		}
	}

	/// Return conjunction of bits equivalent where `x=k`
	fn eq(&self, k: C) -> Result<Vec<Lit>, Unsatisfiable> {
		as_binary(self.normalize(k).into(), Some(self.bits()))
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

	/// Encode `x # k` where `# ∈ {≤,=,≥}`
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
					lex_leq_const(db, &self.xs(true), k, self.bits())
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
					lex_geq_const(db, &self.xs(true), k, self.bits())
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
		self.dom.lb()
	}

	pub(crate) fn ub(&self) -> C {
		self.dom.ub()
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
		let range_ub = unsigned_binary_range_ub::<C>(self.bits()).unwrap();

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
				as_binary(v.into(), Some(self.bits()))
					.into_iter()
					.zip(self.xs(true))
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

	pub(crate) fn as_lin_exp(&self) -> LinExp<Lit, C> {
		let (terms, add) = filter_fixed(&self.xs(true));

		let lin_exp = LinExp::new().add_bounded_log_encoding(
			terms.as_slice(),
			// The Domain constraint bounds only account for the unfixed part of the offset binary notation
			self.lb() - add,
			self.ub() - add,
		);

		// The offset and the fixed value `add` are added to the constant
		lin_exp.add_constant(add)
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
		_: &mut TernLeEncoder,
		y: C,
	) -> Result<Self> {
		if y.is_zero() {
			Ok(self.clone())
		} else {
			let dom = self.dom.clone().add(y);
			Ok(IntVarBin::from_lits(
				&log_enc_add_fn(
					db,
					&self.clone().xs(false),
					&to_lex_bits(y, required_lits(dom.lb(), dom.ub()), true)
						.into_iter()
						.map(LitOrConst::Const)
						.collect_vec(),
					&Comparator::Equal,
					LitOrConst::Const(false),
					None,
				)?,
				dom,
				format!("{}+{}", self.lbl, y),
			))
		}
	}
}

#[derive(Debug, Clone)]
pub(crate) enum IntVarEnc<Lit: Literal, C: Coefficient> {
	Ord(OrdEnc<Lit>),
	Bin(BinEnc<Lit>),
	Const(C),
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> {
	#[allow(dead_code)]
	pub(crate) fn from_dom<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		dom: &[C],
		lbl: String,
	) -> Result<IntVarEnc<DB::Lit, C>> {
		assert!(is_sorted(dom));
		match dom {
			[] => Err(Unsatisfiable),
			[d] => Ok(IntVarEnc::Const(*d)),
			dom => Ok(OrdEnc::new(db, &Dom::from_slice(dom), Some(&lbl)).into()),
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
		todo!()
		/*
		match (self, y) {
			(IntVarEnc::Const(a), IntVarEnc::Const(b)) => Ok(IntVarEnc::Const(*a + *b)),
			// TODO only used in sorters which enforce the constraints later!
			(IntVarEnc::Const(c), x) | (x, IntVarEnc::Const(c)) if c.is_zero() => Ok(x.clone()),
			(IntVarEnc::Ord(x), IntVarEnc::Ord(y)) => {
				let comp_lb = self.lb() + y.lb();
				let lb = std::cmp::max(lb.unwrap_or(comp_lb), comp_lb);

				let comp_ub = self.ub() + y.ub();
				let ub = std::cmp::min(ub.unwrap_or(comp_ub), comp_ub);

				Ok(IntVarEnc::Ord(IntVarOrd::from_syms(
					db,
					ord_plus_ord_le_ord_sparse_dom(
						x.dom().iter(..).map(|d| d.end - C::one()).collect(),
						y.dom().iter(..).map(|d| d.end - C::one()).collect(),
						lb,
						ub,
					),
					format!("{}+{}", x.lbl, y.lbl),
				)))
			}
			(IntVarEnc::Ord(x), IntVarEnc::Const(y)) | (IntVarEnc::Const(y), IntVarEnc::Ord(x)) => {
				let xs =
					x.xs.clone()
						.into_iter(..)
						.map(|(c, l)| ((c.start + *y)..(c.end + *y), l))
						.collect();
				Ok(IntVarOrd {
					xs,
					lb: self.lb() + *y,
					ub_iv: (x.ub_iv.start + *y)..(x.ub_iv.end + *y),
					lbl: format!("{}+{}", x.lbl, y),
				}
				.into())
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Bin(y_bin)) => {
				if GROUND_BINARY_AT_LB && self.lb() + y.lb() != x_bin.lb() + y_bin.lb() {
					unimplemented!(
					"Not implemented addition for unequal lbs for zero-grounded binary encodings"
				);
				}

				let dom = if RETAIN_GAPS {
					todo!()
				// Dom::from_slice(
				// 	&self
				// 		.x
				// 		.borrow()
				// 		.dom
				// 		.iter()
				// 		.cartesian_product(y.borrow().dom.iter())
				// 		.map(|(a, b)| *a + *b)
				// 		.collect::<Vec<_>>(),
				// )
				} else {
					Dom::from_bounds(x_bin.lb() + y_bin.lb(), x_bin.ub() + y_bin.ub())
				};

				let z = IntVarEnc::Bin(IntVarBin::from_lits(
					&log_enc_add_fn(
						db,
						&x_bin.xs(false),
						&y_bin.xs(false),
						&Comparator::Equal,
						LitOrConst::Const(false),
						// Some(required_lits(dom.lb(), dom.ub())), // TODO how to calculate required bits without risking cutting of the necessary sign bit;
						None,
					)?,
					dom,
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
		*/
	}

	/*
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
	*/

	/*
	/// Returns cnf constraining `x<=v`
	pub(crate) fn leq_(&self, v: C) -> Vec<Vec<Lit>> {
		self.leq(v..(v + C::one()))
	}

	/// Returns cnf constraining `x<=a..b`
	pub(crate) fn leq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.ineq(v, &Comparator::LessEq),
			IntVarEnc::Bin(b) => b.leq(v),
			IntVarEnc::Const(c) => {
				let v = v.start + C::one(); // [x<=v] = [x < v+1]
				if v <= *c {
					vec![vec![]] // false?
				} else {
					vec![] // true?
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
	*/

	/*
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
	*/

	pub(crate) fn consistent<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		dom: &Dom<C>,
	) -> Result {
		match self {
			IntVarEnc::Ord(o) => o.consistent(db),
			IntVarEnc::Bin(b) => b.consistent(db, dom),
			IntVarEnc::Const(_) => Ok(()),
		}
	}

	/*
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
	*/

	// pub(crate) fn as_lin_exp(&self) -> LinExp<Lit, C> {
	// 	match self {
	// 		IntVarEnc::Ord(o) => o.as_lin_exp(),
	// 		IntVarEnc::Bin(b) => b.as_lin_exp(),
	// 		IntVarEnc::Const(c) => LinExp::new().add_constant(*c),
	// 	}
	// }

	// pub(crate) fn assign(&self, solution: &[Lit]) -> Result<C, CheckError<Lit>> {
	// 	LinExp::from(self).assign(solution)
	// }

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

impl<Lit: Literal, C: Coefficient> From<BinEnc<Lit>> for IntVarEnc<Lit, C> {
	fn from(b: BinEnc<Lit>) -> Self {
		Self::Bin(b)
	}
}

impl<Lit: Literal, C: Coefficient> From<OrdEnc<Lit>> for IntVarEnc<Lit, C> {
	fn from(o: OrdEnc<Lit>) -> Self {
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
