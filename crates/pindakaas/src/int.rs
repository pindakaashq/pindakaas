use iset::{interval_map, interval_set, IntervalMap, IntervalSet};
use rustc_hash::FxHashMap;

use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;
use std::{cell::RefCell, collections::BTreeSet};

use crate::{
	helpers::{as_binary, is_powers_of_two, unsigned_binary_range_ub},
	linear::{lex_geq_const, lex_leq_const, log_enc_add, log_enc_add_, LimitComp, LinExp, Part},
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

fn display_dom<C: Coefficient>(dom: &BTreeSet<C>) -> String {
	const ELIPSIZE: usize = 8;
	let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
	if dom.len() > ELIPSIZE && C::from(dom.len()).unwrap() == ub - lb + C::one() {
		format!("{}..{}", dom.first().unwrap(), dom.last().unwrap())
	} else if dom.len() > ELIPSIZE {
		format!(
			"{{{},..,{ub}}} ({}|{})",
			dom.iter().take(ELIPSIZE).join(","),
			dom.len(),
			IntVar::required_bits(lb, ub)
		)
	} else {
		format!("{{{}}}", dom.iter().join(","))
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

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarBin<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}:B ∈ {{{}..{}}}", self.lbl, self.lb(), self.ub())
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
				.into_iter()
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
		encoder.encode(
			db,
			&TernLeConstraint {
				x: &IntVarEnc::Bin(self.clone()),
				y: &IntVarEnc::Const(C::zero()),
				cmp: LimitComp::LessEq,
				z: &IntVarEnc::Const(self.ub),
			},
		)?;
		encoder.encode(
			db,
			&TernLeConstraint {
				x: &IntVarEnc::Const(C::zero()),
				y: &IntVarEnc::Const(self.lb),
				cmp: LimitComp::LessEq,
				z: &IntVarEnc::Bin(self.clone()),
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

	fn lb(&self) -> C {
		self.lb
	}

	fn ub(&self) -> C {
		self.ub
	}

	fn geq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		self.ineq(v, true)
	}

	fn leq(&self, v: Range<C>) -> Vec<Vec<Lit>> {
		self.ineq(v, false)
	}

	fn ineq(&self, v: Range<C>, geq: bool) -> Vec<Vec<Lit>> {
		// TODO could *maybe* be domain lb/ub
		let range_lb = self.range().start;
		let range_ub = self.range().end;

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
					as_binary(v.into(), self.lits())
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
		LinExp::new().add_bounded_log_encoding(terms.as_slice(), self.lb, self.ub)
	}

	fn lits(&self) -> usize {
		self.xs.len()
	}

	fn range(&self) -> Range<C> {
		C::zero()..unsigned_binary_range_ub::<C>(self.lits())
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
			(IntVarEnc::Bin(x), IntVarEnc::Bin(y)) => {
				let z_bin = IntVarBin::from_bounds(db, lb, ub, format!("{}+{}", x.lbl, y.lbl));
				log_enc_add(db, &x.xs, &y.xs, &LimitComp::Equal, &z_bin.xs)?;
				Ok(IntVarEnc::Bin(z_bin))
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y))
			| (IntVarEnc::Const(y), IntVarEnc::Bin(x_bin)) => {
				let z_bin = IntVarBin::from_bounds(db, lb, ub, format!("{}+{}", x_bin.lbl, y));
				log_enc_add_(
					db,
					&x_bin
						.xs
						.iter()
						.cloned()
						.map(LitOrConst::from)
						.collect::<Vec<_>>(),
					&as_binary((*y).into(), x_bin.lits())
						.into_iter()
						.map(LitOrConst::Const)
						.collect::<Vec<_>>(),
					&LimitComp::Equal,
					&z_bin
						.xs
						.iter()
						.cloned()
						.map(LitOrConst::from)
						.collect::<Vec<_>>(),
				)?;
				Ok(IntVarEnc::Bin(z_bin))
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
				if *c <= v.end - C::one() {
					vec![]
				} else {
					vec![vec![]]
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
				if *c >= v.end - C::one() {
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

#[derive(Debug)]
pub(crate) struct TernLeConstraint<'a, Lit: Literal, C: Coefficient> {
	pub(crate) x: &'a IntVarEnc<Lit, C>,
	pub(crate) y: &'a IntVarEnc<Lit, C>,
	pub(crate) cmp: LimitComp,
	pub(crate) z: &'a IntVarEnc<Lit, C>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraint<'a, Lit, C> {
	pub fn new(
		x: &'a IntVarEnc<Lit, C>,
		y: &'a IntVarEnc<Lit, C>,
		cmp: LimitComp,
		z: &'a IntVarEnc<Lit, C>,
	) -> Self {
		Self { x, y, cmp, z }
	}

	pub fn is_fixed(&self) -> Result<bool, Unsatisfiable> {
		let TernLeConstraint { x, y, cmp, z } = self;
		if let IntVarEnc::Const(x) = x {
			if let IntVarEnc::Const(y) = y {
				if let IntVarEnc::Const(z) = z {
					return if Self::check(*x, *y, cmp, *z) {
						Ok(true)
					} else {
						Err(Unsatisfiable)
					};
				}
			}
		}
		Ok(false)
	}

	fn check(x: C, y: C, cmp: &LimitComp, z: C) -> bool {
		match cmp {
			LimitComp::LessEq => x + y <= z,
			LimitComp::Equal => x + y == z,
		}
	}
}

impl<'a, Lit: Literal, C: Coefficient> Checker for TernLeConstraint<'a, Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let x = LinExp::from(self.x).assign(solution)?;
		let y = LinExp::from(self.y).assign(solution)?;
		let z = LinExp::from(self.z).assign(solution)?;
		if Self::check(x, y, &self.cmp, z) {
			Ok(())
		} else {
			Err(CheckError::Fail(format!(
				"Failed constraint {self} since {x}+{y} # {z}"
			)))
		}
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for TernLeConstraint<'_, Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} + {} {} {}", self.x, self.y, self.cmp, self.z)
	}
}

#[allow(dead_code)] // TODO
pub(crate) struct TernLeConstraintContainer<Lit: Literal, C: Coefficient> {
	pub(crate) x: IntVarEnc<Lit, C>,
	pub(crate) y: IntVarEnc<Lit, C>,
	pub(crate) cmp: LimitComp,
	pub(crate) z: IntVarEnc<Lit, C>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraintContainer<Lit, C> {
	#[allow(dead_code)]
	pub(crate) fn get(&'a self) -> TernLeConstraint<'a, Lit, C> {
		TernLeConstraint {
			x: &self.x,
			y: &self.y,
			cmp: self.cmp.clone(),
			z: &self.z,
		}
	}
}

#[derive(Debug, Default)]
pub(crate) struct TernLeEncoder {}

const ENCODE_REDUNDANT_X_O_Y_O_Z_B: bool = true;

impl<'a, DB: ClauseDatabase, C: Coefficient> Encoder<DB, TernLeConstraint<'a, DB::Lit, C>>
	for TernLeEncoder
{
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "tern_le_encoder", skip_all, fields(constraint = format!("{} + {} {} {}", tern.x, tern.y, tern.cmp, tern.z)))
	)]
	fn encode(&mut self, db: &mut DB, tern: &TernLeConstraint<DB::Lit, C>) -> Result {
		let TernLeConstraint { x, y, cmp, z } = tern;

		return match (x, y, z) {
			(IntVarEnc::Const(_), IntVarEnc::Const(_), IntVarEnc::Const(_)) => {
				if tern.check(&[]).is_ok() {
					Ok(())
				} else {
					Err(Unsatisfiable)
				}
			}
			(IntVarEnc::Const(x_con), IntVarEnc::Const(y_con), IntVarEnc::Bin(z_bin)) => {
				let lhs = *x_con + *y_con;
				match cmp {
					// put z_bin on the left, const on the right
					LimitComp::Equal => self.encode(
						db,
						&TernLeConstraint {
							x: z,
							y: &IntVarEnc::Const(C::zero()),
							cmp: cmp.clone(),
							z: &IntVarEnc::Const(lhs),
						},
					),
					LimitComp::LessEq => lex_geq_const(
						db,
						z_bin
							.xs
							.iter()
							.map(|x| Some(x.clone()))
							.collect::<Vec<_>>()
							.as_slice(),
						lhs.into(),
						z_bin.xs.len(),
					),
				}
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y_con), IntVarEnc::Const(z_con))
			| (IntVarEnc::Const(y_con), IntVarEnc::Bin(x_bin), IntVarEnc::Const(z_con)) => {
				// and rest is const ~ lex constraint
				// assert!(
				// 	cmp == &LimitComp::LessEq,
				// 	"Only support <= for x:B+y:Constant ? z:Constant"
				// );

				let rhs = *z_con - *y_con;
				match cmp {
					LimitComp::LessEq => lex_leq_const(
						db,
						x_bin
							.xs
							.iter()
							.map(|x| Some(x.clone()))
							.collect::<Vec<_>>()
							.as_slice(),
						rhs.into(),
						x_bin.xs.len(),
					),
					LimitComp::Equal => as_binary(rhs.into(), x_bin.xs.len())
						.into_iter()
						.zip(x_bin.xs.iter())
						.try_for_each(|(b, x)| {
							emit_clause!(db, &[if b { x.clone() } else { x.negate() }])
						}),
				}
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y_const), IntVarEnc::Bin(z_bin))
			| (IntVarEnc::Const(y_const), IntVarEnc::Bin(x_bin), IntVarEnc::Bin(z_bin)) => {
				let (x_bin, y_const) = if y_const.is_zero() || cmp == &LimitComp::Equal {
					(x_bin.clone(), *y_const)
				} else if let IntVarEnc::Bin(x_bin) = x.add(db, y, Some(z.lb()), Some(z.ub()))? {
					(x_bin, C::zero())
				} else {
					unreachable!()
				};

				log_enc_add_(
					db,
					&x_bin
						.xs
						.iter()
						.cloned()
						.map(LitOrConst::from)
						.collect::<Vec<_>>(),
					&as_binary(y_const.into(), z_bin.lits())
						.into_iter()
						.map(LitOrConst::Const)
						.collect::<Vec<_>>(),
					cmp,
					&z_bin
						.xs
						.iter()
						.cloned()
						.map(LitOrConst::from)
						.collect::<Vec<_>>(),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Bin(y_bin), IntVarEnc::Bin(z_bin)) => {
				// y and z are also bin ~ use adder
				match cmp {
					LimitComp::Equal => log_enc_add(db, &x_bin.xs, &y_bin.xs, cmp, &z_bin.xs),
					LimitComp::LessEq => {
						let xy = x.add(db, y, Some(z.lb()), Some(z.ub()))?;
						xy.consistent(db)?;
						self.encode(
							db,
							&TernLeConstraint::new(
								&xy,
								&IntVarEnc::Const(C::zero()),
								LimitComp::LessEq,
								z,
							),
						)
					}
				}
			}
			(IntVarEnc::Bin(_), IntVarEnc::Bin(_), _) => {
				// y/y is bin but z is not bin ~ redundantly encode y + z_bin in 0..z # z and z_bin <= z
				// TODO better coupling ;
				let z_bin = x.add(db, y, None, Some(z.ub()))?;
				z_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(&z_bin, &IntVarEnc::Const(C::zero()), cmp.clone(), z),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Ord(y_ord), _)
			| (IntVarEnc::Ord(y_ord), IntVarEnc::Bin(x_bin), _) => {
				// y is order and z is bin or const ~ redundant y_bin = y_ord and x_bin + y_bin # z
				let y_bin = IntVarBin::from_bounds(
					db,
					y_ord.lb(),
					y_ord.ub(),
					format!("{}{cmp}y:B", y_ord.lbl),
				);

				self.encode(
					db,
					&TernLeConstraint::new(
						&y_ord.clone().into(),
						&IntVarEnc::Const(C::zero()),
						cmp.clone(),
						&y_bin.clone().into(),
					),
				)
				.unwrap();
				y_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(&x_bin.clone().into(), &y_bin.into(), cmp.clone(), z),
				)
			}
			(IntVarEnc::Ord(_), IntVarEnc::Ord(_), IntVarEnc::Bin(_))
				if ENCODE_REDUNDANT_X_O_Y_O_Z_B =>
			{
				// Avoid too many coupling clause
				let xy_ord = x.add(db, y, None, None)?;
				// TODO why necessary?
				xy_ord.consistent(db)?;

				// TODO `x:O.add(y:O)` does not add clauses yet
				self.encode(db, &TernLeConstraint::new(x, y, cmp.clone(), &xy_ord))?;

				self.encode(
					db,
					&TernLeConstraint::new(&xy_ord, &IntVarEnc::Const(C::zero()), cmp.clone(), z),
				)
			}
			(IntVarEnc::Bin(_), IntVarEnc::Const(c), IntVarEnc::Ord(_))
			| (IntVarEnc::Const(c), IntVarEnc::Bin(_), IntVarEnc::Ord(_)) => {
				let z = z.add(db, &IntVarEnc::Const(c.neg()), Some(z.lb()), Some(z.ub()))?;

				// x + c <= z == z-c >= x == /\ (z'<=a -> x<=a)
				for (c_a, z_leq_c_a) in z.leqs() {

					let x_leq_c_a = x.leq(c_a.clone());

					add_clauses_for(db, vec![negate_cnf(z_leq_c_a.clone()), x_leq_c_a])?;
				}
				Ok(())
			}
			(x, y, z) => {
				// couple or constrain x:E + y:E <= z:E

				if cmp == &LimitComp::Equal
					&& !(matches!(
						(x, y, z),
						(
							IntVarEnc::Ord(_) | IntVarEnc::Const(_),
							IntVarEnc::Ord(_) | IntVarEnc::Const(_),
							IntVarEnc::Ord(_) | IntVarEnc::Const(_)
						)
					)) {
					unimplemented!("Not implemented equality coupling for {tern}")
				}

				for (c_a, x_geq_c_a) in x.geqs() {
					for (c_b, y_geq_c_b) in y.geqs() {
						let c_c = (std::cmp::max(c_a.start, c_b.start))
							..(((c_a.end - C::one()) + (c_b.end - C::one())) + C::one());
						let z_geq_c_c = z.geq(c_c.clone());

						add_clauses_for(
							db,
							vec![
								negate_cnf(x_geq_c_a.clone()),
								negate_cnf(y_geq_c_b),
								z_geq_c_c,
							],
						)?;
					}
				}

				// x<=a /\ y<=b -> z<=a+b
				if cmp == &LimitComp::Equal {
					for (c_a, x_leq_c_a) in x.leqs() {
						for (c_b, y_leq_c_b) in y.leqs() {
							let c_c = (c_a.start) + (c_b.start);
							let c_c = c_c..(c_c + C::one());

							let z_leq_c_c = z.leq(c_c.clone());

							add_clauses_for(
								db,
								vec![
									negate_cnf(x_leq_c_a.clone()),
									negate_cnf(y_leq_c_b),
									z_leq_c_c,
								],
							)?;
						}
					}
				}
				return Ok(());
			}
		};
	}
}

pub(crate) fn add_clauses_for<DB: ClauseDatabase>(
	db: &mut DB,
	expression: Vec<Vec<Vec<DB::Lit>>>,
) -> Result {
	// TODO doctor out type of expression (clauses containing conjunctions?)

	let filter_trivial = true;
	for cls in expression
		.into_iter()
		.map(|cls| cls.into_iter())
		.multi_cartesian_product()
	{
		let cls = cls.concat(); // filter out [] (empty conjunctions?) of the clause
		if filter_trivial {
			let mut lits = HashSet::<DB::Lit>::with_capacity(cls.len());
			if cls.iter().any(|lit| {
				if lits.contains(&lit.negate()) {
					true
				} else {
					lits.insert(lit.clone());
					false
				}
			}) {
				continue;
			}
		}
		emit_clause!(db, &cls)?
	}
	Ok(())
}

pub(crate) fn negate_cnf<Lit: Literal>(clauses: Vec<Vec<Lit>>) -> Vec<Vec<Lit>> {
	if clauses.is_empty() {
		vec![vec![]]
	} else if clauses.contains(&vec![]) {
		vec![]
	} else {
		assert!(clauses.len() == 1);
		clauses
			.into_iter()
			.map(|clause| clause.into_iter().map(|lit| lit.negate()).collect())
			.collect()
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

	use super::*;
	use crate::helpers::tests::{assert_sol, assert_unsat, TestDB};
	use iset::interval_set;

	#[cfg(feature = "trace")]
	use traced_test::test;

	macro_rules! test_int_lin {
		($encoder:expr,$x:expr,$y:expr,$cmp:expr,$z:expr) => {
			use super::*;
			#[cfg(feature = "trace")]
			use traced_test::test;

			#[test]
			fn o_o_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Ord,
						IntVarEncoding::Ord
					]
				);
			}

			#[test]
			fn o_o_b() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Ord,
						IntVarEncoding::Bin
					]
				);
			}

			#[test]
			fn o_b_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Bin,
						IntVarEncoding::Ord
					]
				);
			}

			#[test]
			fn o_b_b() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Bin,
						IntVarEncoding::Bin
					]
				);
			}

			#[test]
			fn b_o_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Bin,
						IntVarEncoding::Ord,
						IntVarEncoding::Ord
					]
				);
			}

			#[test]
			fn b_o_b() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Bin,
						IntVarEncoding::Ord,
						IntVarEncoding::Bin
					]
				);
			}

			#[test]
			fn b_b_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Bin,
						IntVarEncoding::Bin,
						IntVarEncoding::Ord
					]
				);
			}
		};
	}

	macro_rules! test_int_lin_encs {
		($encoder:expr,$x:expr,$y:expr,$cmp:expr,$z:expr,$encs:expr) => {
			let mut db = TestDB::new(0);
			let x = from_dom(&mut db, $x, &$encs[0], String::from("x"));
			let y = from_dom(&mut db, $y, &$encs[1], String::from("y"));
			let z = from_dom(&mut db, $z, &$encs[2], String::from("z"));

			db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

			let tern = TernLeConstraint {
				x: &x,
				y: &y,
				cmp: $cmp,
				z: &z,
			};

			let sols =
				db.generate_solutions(
					|sol| {
						tern.check(sol).is_ok()
					},
					db.num_var,
					);

			x.consistent(&mut db).unwrap();
			y.consistent(&mut db).unwrap();
			z.consistent(&mut db).unwrap();
			if sols.is_empty() {
				assert_unsat!(db => TernLeEncoder::default(), &tern)
			} else {
				assert_sol!(db => TernLeEncoder::default(), &tern => sols);
			}
		}
	}

	macro_rules! int_lin_test_suite {
		($encoder:expr,$cmp:expr) => {
			use super::*;

			mod _012_0_012 {
				test_int_lin!($encoder, &[0, 1, 2], &[0], $cmp, &[0, 1, 2]);
			}

			mod _01_1_2 {
				test_int_lin!($encoder, &[0, 1], &[1], $cmp, &[2]);
			}

			mod _01_1_12 {
				test_int_lin!($encoder, &[0, 1], &[1], $cmp, &[1, 2]);
			}

			mod _01_1_012 {
				test_int_lin!($encoder, &[0, 1], &[1], $cmp, &[0, 1, 2]);
			}

			mod _01_01_012 {
				test_int_lin!($encoder, &[0, 1], &[0, 1], $cmp, &[0, 1, 2]);
			}

			mod _01_012_3 {
				test_int_lin!($encoder, &[0, 1], &[0, 1, 2], $cmp, &[3]);
			}

			mod _01_01_3 {
				test_int_lin!($encoder, &[0, 1], &[0, 1], $cmp, &[3]);
			}

			mod _0123_23_2345 {
				test_int_lin!($encoder, &[0, 1, 2, 3], &[2, 3], $cmp, &[2, 3, 4, 5]);
			}

			mod _012478_0_0123456789 {
				test_int_lin!(
					$encoder,
					&[0, 1, 2, 4, 7, 8],
					&[0],
					$cmp,
					&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
				);
			}
		};
	}

	mod int_lin_le {
		int_lin_test_suite!(TernLeEncoder::default(), LimitComp::LessEq);
	}

	// mod int_lin_eq {
	// 	int_lin_test_suite!(TernLeEncoder::default(), LimitComp::Equal);
	// }

	fn get_ord_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: IntervalSet<C>,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarOrd::from_syms(db, dom, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Ord(x)
	}

	fn get_bin_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		ub: C,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarBin::from_bounds(db, C::zero(), ub, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}

	#[test]
	fn constant_test() {
		let c: IntVarEnc<i32, _> = IntVarEnc::Const(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(6..7), Vec::<Vec<i32>>::new());
		assert_eq!(c.geq(45..46), vec![vec![]]);
	}

	#[test]
	fn bin_1_test() {
		let mut db = TestDB::new(0);
		let x = get_bin_x::<_, i32>(&mut db, 12, true, "x".to_string());
		let x_lin: LinExp<i32, i32> = LinExp::from(&x);

		assert_eq!(x.lits(), 4);
		assert_eq!(x.lb(), 0);
		assert_eq!(x.ub(), 12);
		// geq looks at end - 2
		assert_eq!(x.geq(7..8), vec![vec![1, 4]]); // 7-1=6 == 0110 (right-to-left!)
		assert_eq!(x.geq(5..6), vec![vec![1, 2, 4]]); // 4=0100
		assert_eq!(x.geq(6..7), vec![vec![2, 4]]); // 5=0101
		assert_eq!(x.geq(7..8), vec![vec![1, 4]]); // 6=0110
		assert_eq!(x.geq(7..9), vec![vec![1, 4], vec![4]]); // 8=1000

		// leq looks at start .. end - 1?
		assert_eq!(x.leq(6..7), vec![vec![-1, -2, -3]]); // 7=0111
		assert_eq!(x.leq(6..8), vec![vec![-1, -2, -3], vec![-4]]); // +8=1000
		assert_eq!(x.leq(6..9), vec![vec![-1, -2, -3], vec![-4], vec![-1, -4]]); // +9=1001
		assert_eq!(x.leq(5..8), vec![vec![-2, -3], vec![-1, -2, -3], vec![-4]]); // 5+1=0110

		assert_eq!(x.geq(-2..3), vec![vec![1, 2, 3, 4], vec![2, 3, 4]]);
		assert_eq!(x.geq(13..19), vec![vec![1, 2], vec![2], vec![1], vec![]]); // 7=0111

		assert_eq!(x.leq(-2..3), vec![vec![], vec![-1], vec![-2], vec![-1, -2]]);
		assert_eq!(x.leq(13..19), vec![vec![-2, -3, -4], vec![-1, -2, -3, -4]]); // 7=0111

		assert_eq!(x_lin.assign(&[-1, -2, -3, -4]), Ok(0));
		assert_eq!(x_lin.assign(&[1, -2, -3, -4]), Ok(1));
		assert_eq!(x_lin.assign(&[1, 2, -3, -4]), Ok(3));
		assert_eq!(x_lin.assign(&[1, 2, -3, 4]), Ok(11));
		assert_eq!(
			x_lin.assign(&[1, 2, 3, 4]),
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			cmp: LimitComp::LessEq,
			z: &IntVarEnc::Const(10),
		};

		db.num_var = x.lits() as i32;

		db.generate_solutions(|sol| tern.check(sol).is_ok(), db.num_var);

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
		let x = IntVarBin::from_bounds(&mut db, 0, 12, "x".to_string());
		db.num_var = x.lits() as i32;
		let tern = TernLeConstraint {
			x: &IntVarEnc::Bin(x),
			y: &IntVarEnc::Const(0),
			cmp: LimitComp::LessEq,
			z: &IntVarEnc::Const(6),
		};
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
			"x".to_string(),
		);

		assert_eq!(x.lits(), 3);
		assert_eq!(x.lb(), 2);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(6..7), vec![vec![2]]);
		assert_eq!(x.geq(4..7), vec![vec![2]]);

		let x_lin: LinExp<i32, i32> = LinExp::from(&x);
		assert!(x_lin.assign(&[1, -2, 3]).is_err());
		assert!(x_lin.assign(&[-1, 2, -3]).is_err());
		assert_eq!(x_lin.assign(&[-1, -2, -3]), Ok(2));
		assert_eq!(x_lin.assign(&[1, -2, -3]), Ok(4));
		assert_eq!(x_lin.assign(&[1, 2, -3]), Ok(6));
		assert_eq!(x_lin.assign(&[1, 2, 3]), Ok(10));

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			cmp: LimitComp::LessEq,
			z: &IntVarEnc::Const(6),
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
			get_ord_x(&mut db, interval_set!(1..2, 2..7), true, "x".to_string()),
			get_ord_x(&mut db, interval_set!(2..3, 3..5), true, "y".to_string()),
			get_ord_x(&mut db, interval_set!(0..4, 4..11), true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
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

	#[test]
	fn ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 2..7), true, "x".to_string()),
			// TODO 'gapped' in interval_set:
			// get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
			IntVarEnc::Const(0),
			get_bin_x(&mut db, 7, true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		let sols = db.generate_solutions(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern => sols


		);
	}

	#[test]
	fn ord_plus_ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..3), true, "x".to_string()),
			get_ord_x(&mut db, interval_set!(1..4), true, "y".to_string()),
			get_bin_x(&mut db, 6, true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5],
		  vec![-1, -2, 3, -4, -5],
		  vec![-1, -2, -3, 4, -5],
		  vec![1, -2, -3, 4, -5],
		  vec![-1, -2, 3, 4, -5],
		  vec![1, -2, 3, 4, -5],
		  vec![-1, 2, 3, 4, -5],
		  vec![-1, -2, -3, -4, 5],
		  vec![1, -2, -3, -4, 5],
		  vec![-1, 2, -3, -4, 5],
		  vec![-1, -2, 3, -4, 5],
		  vec![1, -2, 3, -4, 5],
		  vec![-1, 2, 3, -4, 5],
		  vec![1, 2, 3, -4, 5],
		  vec![-1, -2, -3, 4, 5],
		  vec![1, -2, -3, 4, 5],
		  vec![-1, 2, -3, 4, 5],
		  vec![1, 2, -3, 4, 5],
		]);
	}

	#[test]
	fn bin_le_test() {
		let mut db = TestDB::new(0);
		let n = 4;
		let ub = (2i32.pow(n)) - 1;

		let (x, y, z) = (
			get_bin_x(&mut db, ub, true, "x".to_string()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			IntVarEnc::Const(14),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			// cmp: LimitComp::Equal,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		let sols = db.generate_solutions(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
					sols
		);
	}

	#[test]
	fn bin_le_bin_test() {
		let mut db = TestDB::new(0);
		let n = 5;
		let ub = (2i32.pow(n)) - 1;

		let (x, y, z) = (
			get_bin_x(&mut db, ub, true, "x".to_string()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			get_bin_x(&mut db, ub, true, "z".to_string()),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			// cmp: LimitComp::Equal,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		let sols = db.generate_solutions(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
					sols
		);
	}

	#[test]
	fn bin_plus_bin_le_bin_test() {
		let mut db = TestDB::new(0);
		let n = 2;
		let (x, y, z) = (
			get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "x".to_string()),
			get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			get_bin_x(&mut db, (2i32.pow(n + 1)) - 2, true, "z".to_string()),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		let sols = db.generate_solutions(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
					sols
		);
	}

	#[test]
	fn bin_plus_bin_eq_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_bin_x(&mut db, 2, true, "x".to_string()),
			get_bin_x(&mut db, 3, true, "y".to_string()),
			get_bin_x(&mut db, 5, true, "z".to_string()),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::Equal,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarBin<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5, -6, -7],
		  vec![1, -2, -3, -4, 5, -6, -7],
		  vec![-1, -2, 3, -4, 5, -6, -7],
		  vec![-1, 2, -3, -4, -5, 6, -7],
		  vec![1, -2, 3, -4, -5, 6, -7],
		  vec![-1, -2, -3, 4, -5, 6, -7],
		  vec![-1, 2, 3, -4, 5, 6, -7],
		  vec![1, -2, -3, 4, 5, 6, -7],
		  vec![-1, -2, 3, 4, 5, 6, -7],
		  vec![-1, 2, -3, 4, -5, -6, 7],
		  vec![1, -2, 3, 4, -5, -6, 7],
		  vec![-1, 2, 3, 4, 5, -6, 7],
		]
		);
	}

	// #[test]
	fn _bin_plus_ord_eq_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_bin_x(&mut db, 6, true, String::from("x")),
			get_ord_x(&mut db, interval_set!(1..6), true, String::from("y")),
			get_bin_x(&mut db, 6, true, String::from("z")),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: LimitComp::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarBin<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5, -6, -7],
		  vec![-1, -2, -3, -4, 5, -6, -7],
		  vec![1, -2, -3, -4, 5, -6, -7],
		  vec![-1, -2, -3, -4, -5, 6, -7],
		  vec![1, -2, -3, -4, -5, 6, -7],
		  vec![-1, 2, -3, -4, -5, 6, -7],
		  vec![-1, -2, -3, -4, 5, 6, -7],
		  vec![1, -2, -3, -4, 5, 6, -7],
		  vec![-1, 2, -3, -4, 5, 6, -7],
		  vec![1, 2, -3, -4, 5, 6, -7],
		  vec![-1, -2, -3, -4, -5, -6, 7],
		  vec![1, -2, -3, -4, -5, -6, 7],
		  vec![-1, 2, -3, -4, -5, -6, 7],
		  vec![1, 2, -3, -4, -5, -6, 7],
		  vec![-1, -2, 3, -4, -5, -6, 7],
		  vec![-1, -2, -3, -4, 5, -6, 7],
		  vec![1, -2, -3, -4, 5, -6, 7],
		  vec![-1, 2, -3, -4, 5, -6, 7],
		  vec![1, 2, -3, -4, 5, -6, 7],
		  vec![-1, -2, 3, -4, 5, -6, 7],
		  vec![1, -2, 3, -4, 5, -6, 7],
		  vec![-1, -2, -3, 4, 5, -6, 7],
		  vec![-1, -2, -3, -4, -5, 6, 7],
		  vec![1, -2, -3, -4, -5, 6, 7],
		  vec![-1, 2, -3, -4, -5, 6, 7],
		  vec![1, 2, -3, -4, -5, 6, 7],
		  vec![-1, -2, 3, -4, -5, 6, 7],
		  vec![1, -2, 3, -4, -5, 6, 7],
		  vec![-1, 2, 3, -4, -5, 6, 7],
		  vec![-1, -2, -3, 4, -5, 6, 7],
		  vec![1, -2, -3, 4, -5, 6, 7],
		]
		);
	}

	enum IntVarEncoding {
		// Dir,
		Ord,
		Bin,
	}

	fn from_dom<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: &[C],
		enc: &IntVarEncoding,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		if dom.len() == 1 {
			IntVarEnc::Const(dom[0])
		} else {
			match enc {
				IntVarEncoding::Ord => IntVarOrd::from_dom(db, dom, lbl).into(),
				IntVarEncoding::Bin => {
					IntVarBin::from_bounds(db, dom[0], dom[dom.len() - 1], lbl).into()
				}
			}
		}
	}
}

#[derive(Debug)]
pub(crate) struct Model<Lit: Literal, C: Coefficient> {
	vars: HashMap<usize, IntVarEnc<Lit, C>>,
	pub(crate) cons: Vec<Lin<C>>,
	var_ids: usize,
}

// TODO Domain will be used once (/if) this is added as encoder feature.
#[allow(dead_code)]
#[derive(Default, Clone, PartialEq)]
pub enum Consistency {
	None,
	#[default]
	Bounds,
	Domain,
}

impl<Lit: Literal, C: Coefficient> Display for Model<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for con in &self.cons {
			writeln!(f, "{}", con)?;
		}
		Ok(())
	}
}

impl<C: Coefficient> Display for Lin<C> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let disp_x = |x: &(C, Rc<RefCell<IntVar<C>>>)| -> String {
			let (coef, x) = x;
			assert!(coef.abs() == C::one());
			let x = x.borrow();

			format!("{}", x)
		};
		write!(
			f,
			"{} {} {}",
			self.xs[0..2].iter().map(disp_x).join(" + "),
			self.cmp,
			disp_x(&self.xs[2])
		)?;
		Ok(())
	}
}

impl<C: Coefficient> fmt::Display for IntVar<C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "x{} ∈ {}", self.id, display_dom(&self.dom))
	}
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	pub fn new() -> Self {
		Self {
			vars: HashMap::new(),
			cons: vec![],
			var_ids: 0,
		}
	}

	pub fn add_int_var_enc(&mut self, x: IntVarEnc<Lit, C>) -> IntVar<C> {
		let var = self.new_var(x.dom().iter(..).map(|d| d.end - C::one()).collect(), false);
		self.vars.insert(var.id, x);
		var
	}

	pub fn new_var(&mut self, dom: BTreeSet<C>, add_consistency: bool) -> IntVar<C> {
		self.var_ids += 1;
		IntVar {
			id: self.var_ids,
			dom,
			add_consistency,
			views: HashMap::default(),
		}
	}

	pub fn new_constant(&mut self, c: C) -> IntVar<C> {
		self.new_var(BTreeSet::from([c]), false)
	}

	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		cutoff: Option<C>,
	) -> Result {
		let mut all_views = HashMap::new();
		for con in &self.cons {
			let Lin { xs, cmp } = con;
			assert!(
				con.xs.len() == 3
					&& con.xs.iter().map(|(c, _)| c).collect::<Vec<_>>()
						== [&C::one(), &C::one(), &-C::one()]
			);

			for (_, x) in xs {
				let x = x.borrow();
				self.vars
					.entry(x.id)
					.or_insert_with(|| x.encode(db, &mut all_views, x.prefer_order(cutoff)));
			}

			let (x, y, z) = (
				&self.vars[&xs[0].1.borrow().id],
				&self.vars[&xs[1].1.borrow().id],
				&self.vars[&xs[2].1.borrow().id],
			);

			TernLeEncoder::default()
				.encode(db, &TernLeConstraint::new(x, y, cmp.clone(), z))
				.unwrap();
		}

		Ok(())
	}

	pub(crate) fn propagate(&mut self, consistency: &Consistency, mut queue: Vec<usize>) {
		if consistency == &Consistency::None {
			return;
		}
		while let Some(con) = queue.pop() {
			let changed = self.cons[con].propagate(consistency);
			let mut cons = self
				.cons
				.iter()
				.enumerate()
				.filter_map(|(i, con)| {
					con.xs
						.iter()
						.any(|(_, x)| changed.contains(&x.borrow().id))
						.then_some(i)
				})
				.collect::<Vec<_>>();
			queue.append(&mut cons);
		}
	}
}

#[derive(Debug)]
pub struct Lin<C: Coefficient> {
	pub(crate) xs: Vec<(C, Rc<RefCell<IntVar<C>>>)>,
	pub(crate) cmp: LimitComp,
}

impl<C: Coefficient> Lin<C> {
	pub fn tern(
		x: Rc<RefCell<IntVar<C>>>,
		y: Rc<RefCell<IntVar<C>>>,
		cmp: LimitComp,
		z: Rc<RefCell<IntVar<C>>>,
	) -> Self {
		Lin {
			xs: vec![(C::one(), x), (C::one(), y), (-C::one(), z)],
			cmp,
		}
	}

	pub fn lb(&self) -> C {
		self.xs
			.iter()
			.map(|(c, x)| x.borrow().lb(c))
			.fold(C::zero(), |a, b| a + b)
	}

	pub fn ub(&self) -> C {
		self.xs
			.iter()
			.map(|(c, x)| x.borrow().ub(c))
			.fold(C::zero(), |a, b| a + b)
	}

	pub(crate) fn propagate(&mut self, consistency: &Consistency) -> Vec<usize> {
		let mut changed = vec![];
		match consistency {
			Consistency::None => unreachable!(),
			Consistency::Bounds => loop {
				let mut fixpoint = true;
				if self.cmp == LimitComp::Equal {
					for (c, x) in &self.xs {
						let xs_ub = self.ub();
						let mut x = x.borrow_mut();
						let size = x.size();

						let id = x.id;
						let x_ub = if c.is_positive() {
							*x.dom.last().unwrap()
						} else {
							*x.dom.first().unwrap()
						};

						// c*d >= x_ub*c + xs_ub := d >= x_ub - xs_ub/c
						let b = x_ub - (xs_ub / *c);

						if !c.is_negative() {
							x.ge(&b);
						} else {
							x.le(&b);
						}

						if x.size() < size {
							changed.push(id);
							fixpoint = false;
						}
						assert!(x.size() > 0);
					}
				}

				let rs_lb = self.lb();
				for (c, x) in &self.xs {
					let mut x = x.borrow_mut();
					let size = x.size();
					let x_lb = if c.is_positive() {
						*x.dom.first().unwrap()
					} else {
						*x.dom.last().unwrap()
					};

					let id = x.id;

					// c*d <= c*x_lb - rs_lb
					// d <= x_lb - (rs_lb / c) (or d >= .. if d<0)
					let b = x_lb - (rs_lb / *c);

					if c.is_negative() {
						x.ge(&b);
					} else {
						x.le(&b);
					}

					if x.size() < size {
						//println!("Pruned {}", size - x.size());
						changed.push(id);
						fixpoint = false;
					}
					assert!(x.size() > 0);
				}

				if fixpoint {
					return changed;
				}
			},
			Consistency::Domain => {
				assert!(self.cmp == LimitComp::Equal);
				loop {
					let mut fixpoint = true;
					for (i, (c_i, x_i)) in self.xs.iter().enumerate() {
						let id = x_i.borrow().id;
						x_i.borrow_mut().dom.retain(|d_i| {
							if self
								.xs
								.iter()
								.enumerate()
								.filter_map(|(j, (c_j, x_j))| {
									(i != j).then(|| {
										x_j.borrow()
											.dom
											.iter()
											.map(|d_j_k| *c_j * *d_j_k)
											.collect::<Vec<_>>()
									})
								})
								.multi_cartesian_product()
								.any(|rs| {
									*c_i * *d_i + rs.into_iter().fold(C::zero(), |a, b| a + b)
										== C::zero()
								}) {
								true
							} else {
								fixpoint = false;
								changed.push(id);
								false
							}
						});
						assert!(x_i.borrow().size() > 0);
					}

					if fixpoint {
						return changed;
					}
				}
			}
		}
	}
}

// TODO perhaps id can be used by replacing vars HashMap to just vec
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntVar<C: Coefficient> {
	pub(crate) id: usize,
	pub(crate) dom: BTreeSet<C>,
	add_consistency: bool,
	pub(crate) views: HashMap<C, (usize, C)>,
}

impl<C: Coefficient> IntVar<C> {
	fn encode<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		views: &mut HashMap<(usize, C), DB::Lit>,
		prefer_order: bool,
	) -> IntVarEnc<DB::Lit, C> {
		if self.size() == 1 {
			IntVarEnc::Const(*self.dom.first().unwrap())
		} else {
			let x = if prefer_order {
				let dom = self
					.dom
					.iter()
					.sorted()
					.cloned()
					.tuple_windows()
					.map(|(a, b)| (a + C::one())..(b + C::one()))
					.map(|v| (v.clone(), views.get(&(self.id, v.end - C::one())).cloned()))
					.collect::<IntervalMap<_, _>>();
				IntVarEnc::Ord(IntVarOrd::from_views(db, dom, "x".to_string()))
			} else {
				let y = IntVarBin::from_bounds(
					db,
					*self.dom.first().unwrap(),
					*self.dom.last().unwrap(),
					"x".to_string(),
				);
				IntVarEnc::Bin(y)
			};

			if self.add_consistency {
				x.consistent(db).unwrap();
			}

			for view in self
				.views
				.iter()
				.map(|(c, (id, val))| ((*id, *val), x.geq(*c..(*c + C::one()))))
			{
				// TODO refactor
				if !view.1.is_empty() {
					views.insert(view.0, view.1[0][0].clone());
				}
			}
			x
		}
	}

	fn ge(&mut self, bound: &C) {
		self.dom = self.dom.split_off(bound);
	}

	fn le(&mut self, bound: &C) {
		self.dom.split_off(&(*bound + C::one()));
	}

	pub(crate) fn size(&self) -> usize {
		self.dom.len()
	}

	pub(crate) fn lb(&self, c: &C) -> C {
		*c * *(if c.is_negative() {
			self.dom.last()
		} else {
			self.dom.first()
		})
		.unwrap()
	}

	pub(crate) fn ub(&self, c: &C) -> C {
		*c * *(if c.is_negative() {
			self.dom.first()
		} else {
			self.dom.last()
		})
		.unwrap()
	}

	pub fn required_bits(_: C, ub: C) -> u32 {
		// TODO support non-zero lb's
		// lb.leading_zeros() - ub.leading_zeros()
		C::zero().leading_zeros() - ub.leading_zeros()
	}

	fn prefer_order(&self, cutoff: Option<C>) -> bool {
		match cutoff {
			None => true,
			Some(cutoff) if cutoff == C::zero() => false,
			Some(cutoff) => C::from(self.dom.len()).unwrap() < cutoff,
		}
	}
}
