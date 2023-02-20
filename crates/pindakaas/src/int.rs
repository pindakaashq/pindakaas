use iset::{interval_set, IntervalMap, IntervalSet};
use rustc_hash::FxHashMap;

use itertools::Itertools;
use std::collections::HashMap;
use std::rc::Rc;
use std::{cell::RefCell, collections::BTreeSet};

use crate::{
	helpers::is_powers_of_two,
	linear::{lex_lesseq_const, log_enc_add, LimitComp, LinExp, Part},
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

// TODO update with Model.new_var
/// Chooses next integer variable heuristically; returns Ord or Bin based on whether the number of resulting literals is under the provided cutoff
pub(crate) fn _next_int_var<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	dom: IntervalSet<C>,
	cutoff: Option<C>,
	add_consistency: bool,
	lbl: String,
) -> IntVarEnc<DB::Lit, C> {
	// TODO check for domain of 1 => Constant?
	if cutoff.is_none() || C::from(dom.len()).unwrap() <= cutoff.unwrap() {
		let x = IntVarOrd::from_syms(db, dom, lbl);
		if add_consistency {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Ord(x)
	} else {
		let x = IntVarBin::new(db, dom.range().unwrap().end - C::one(), lbl);
		if add_consistency {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}
}

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

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarOrd<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:O ∈ {{{}}} [{:?}]",
			self.lbl,
			self.dom()
				.iter(..)
				.map(|iv| iv.end - C::one())
				.sorted()
				.join(","),
			self.xs.values(..).map(|x| format!("{:?}", x)).join(","),
		)
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for IntVarBin<Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:O ∈ {{{}}}",
			self.lbl,
			self.dom()
				.iter(..)
				.map(|iv| iv.end - C::one())
				.sorted()
				.join(",")
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
		let xs = views
			.into_iter(..)
			.map(|(v, lit)| {
				#[cfg(feature = "trace")]
				let lbl = format!("{lbl}>={v:?}");
				(v, lit.unwrap_or_else(|| new_var!(db, lbl)))
			})
			.collect::<IntervalMap<_, _>>();
		Self { xs, lbl }
	}

	pub fn _consistency(&self) -> ImplicationChainConstraint<Lit> {
		ImplicationChainConstraint {
			lits: self.xs.values(..).cloned().collect::<Vec<_>>(),
		}
	}

	#[allow(dead_code)]
	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		ImplicationChainEncoder::default()._encode(db, &self._consistency())
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

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	pub fn add<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		y: &IntVarEnc<Lit, C>,
		// _: &LimitComp,
		// enc: &mut dyn Encoder<DB, TernLeConstraint<'a, DB, C>>,
	) -> Result<IntVarEnc<Lit, C>> {
		if let IntVarEnc::Const(y) = y {
			Ok(IntVarOrd {
				xs: self
					.xs
					.clone()
					.into_iter(..)
					.map(|(c, l)| ((c.start + *y)..(c.end + *y), l))
					.collect(),
				lbl: self.lbl.clone(),
			}
			.into())
		} else if let IntVarEnc::Ord(y) = y {
			let z = IntVarOrd::from_bounds(
				db,
				C::zero(),
				self.ub() + y.ub(),
				format!("{}+{}", self.lbl, y.lbl),
			)
			.into();
			// eprintln!("z: {}", z);
			// let con = TernLeConstraint::new(self, y, cmp.clone(), z.as_ref());
			// enc.encode(db, &con)?;
			Ok(z)
		} else {
			todo!()
		}
	}

	pub fn div(&self, c: &C) -> IntVarEnc<Lit, C> {
		assert!(*c == C::one() + C::one(), "Can only divide IntVarOrd by 2");
		let lb = self.lb();
		let xs = self
			.xs
			.clone()
			.into_iter(..)
			.filter(|(c, _)| (c.end - C::one()).is_even())
			.map(|(c, l)| (((c.end - C::one()) / (C::one() + C::one())), l))
			.map(|(c, l)| (c..(c + C::one()), l))
			.collect::<IntervalMap<_, _>>();

		if xs.is_empty() {
			IntVarEnc::Const(lb / *c)
		} else {
			IntVarOrd {
				xs,
				lbl: self.lbl.clone(),
			}
			.into()
		}
	}

	pub fn dom(&self) -> IntervalSet<C> {
		std::iter::once(self.lb()..self.lb() + C::one())
			.chain(self.xs.intervals(..))
			.collect()
	}

	pub fn lb(&self) -> C {
		self.xs.range().unwrap().start - C::one()
	}

	pub fn ub(&self) -> C {
		self.xs.range().unwrap().end - C::one()
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

#[derive(Debug, Clone)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	pub(crate) xs: Vec<Lit>,
	lb: C,
	ub: C,
	lbl: String,
}

impl<Lit: Literal, C: Coefficient> IntVarBin<Lit, C> {
	// TODO change to with_label or something
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, ub: C, lbl: String) -> Self {
		let bits = C::zero().leading_zeros() - ub.leading_zeros();
		Self {
			xs: (0..bits)
				.map(|_i| new_var!(db, format!("{}^{}", lbl, _i)))
				.collect(),
			lb: C::zero(), // TODO support non-zero
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

	pub fn _consistency(&self) -> TernLeConstraintContainer<Lit, C> {
		TernLeConstraintContainer {
			x: IntVarEnc::Bin(self.clone()),
			y: IntVarEnc::Const(self.lb),
			cmp: LimitComp::LessEq,
			z: IntVarEnc::Const(self.ub),
		}
	}

	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		TernLeEncoder::default().encode(db, &self._consistency().get())
	}

	fn add<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		_: &mut DB,
		_: &IntVarEnc<Lit, C>,
		// _: &LimitComp,
		// _: &mut dyn Encoder<DB, TernLeConstraint<DB, C>>,
	) -> Result<IntVarEnc<Lit, C>> {
		todo!()
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

	fn lits(&self) -> usize {
		self.xs.len()
	}
}

impl<Lit: Literal, C: Coefficient> IntVarOrd<Lit, C> {
	/// Constructs IntVar `y` for linear expression `xs` so that ∑ xs ≦ y, using order encoding
	pub fn from_part_using_le_ord<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		xs: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
		lbl: String,
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
				IntVarOrd::from_views(db, dom, lbl)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				IntVarOrd::from_views(
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
					lbl,
				)
			}
			Part::Dom(terms, l, u) => {
				let x_bin =
					IntVarBin::from_terms(terms.to_vec(), l.clone(), u.clone(), String::from("x"));
				let x_ord = IntVarOrd::from_bounds(db, x_bin.lb(), x_bin.ub(), String::from("x"));

				TernLeEncoder::default()
					.encode(
						db,
						&TernLeConstraint::new(
							&x_ord.clone().into(),
							&IntVarEnc::Const(C::zero()),
							LimitComp::LessEq,
							&x_bin.into(),
						),
					)
					.unwrap();
				x_ord
			}
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
	pub(crate) fn add<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		y: &IntVarEnc<Lit, C>,
		// cmp: &LimitComp,
		// enc: &'a mut dyn Encoder<DB, TernLeConstraint<'a, DB, C>>,
	) -> Result<IntVarEnc<Lit, C>> {
		match self {
			IntVarEnc::Ord(o) => o.add(db, y),
			IntVarEnc::Bin(b) => b.add(db, y),
			IntVarEnc::Const(c) => {
				if let IntVarEnc::Const(y) = y {
					Ok(IntVarEnc::Const(*c + *y))
				} else {
					// y.add(db, self, cmp, enc)
					y.add(db, self)
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
			Err(CheckError::Unsatisfiable(Unsatisfiable))
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

#[derive(Default)]
pub(crate) struct TernLeEncoder {}

impl<'a, DB: ClauseDatabase, C: Coefficient> Encoder<DB, TernLeConstraint<'a, DB::Lit, C>>
	for TernLeEncoder
{
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "tern_le_encoder", skip_all, fields(constraint = format!("{} + {} {} {}", tern.x, tern.y, tern.cmp, tern.z)))
	)]
	fn encode(&mut self, db: &mut DB, tern: &TernLeConstraint<DB::Lit, C>) -> Result {
		let TernLeConstraint { x, y, cmp, z } = tern;
		if matches!(
			(x, y, z),
			(
				IntVarEnc::Const(_),
				IntVarEnc::Const(_),
				IntVarEnc::Const(_)
			)
		) {
			if tern.check(&[]).is_ok() {
				Ok(())
			} else {
				Err(Unsatisfiable)
			}
		} else if matches!(x, IntVarEnc::Const(_)) {
			self.encode(
				db,
				&TernLeConstraint {
					x: *y,
					y: *x,
					cmp: cmp.clone(),
					z: *z,
				},
			)
		} else if matches!(x, IntVarEnc::Ord(_)) && matches!(y, IntVarEnc::Bin(_)) {
			self.encode(db, &TernLeConstraint::new(*y, *x, cmp.clone(), *z))
		} else if let IntVarEnc::Bin(x_bin) = x {
			if let (IntVarEnc::Const(y_con), IntVarEnc::Const(z_con)) = (y, z) {
				// assert!(
				// 	cmp == &LimitComp::LessEq,
				// 	"Only support <= for x:B+y:Constant ? z:Constant"
				// );
				return lex_lesseq_const(
					db,
					x_bin
						.xs
						.iter()
						.map(|x| Some(x.clone()))
						.collect::<Vec<_>>()
						.as_slice(),
					(*z_con - *y_con).into(),
					x_bin.xs.len(),
				);
			} else if let (IntVarEnc::Bin(y_bin), IntVarEnc::Bin(z_bin)) = (y, z) {
				// assert!(
				// 	cmp == &LimitComp::Equal,
				// 	"Only support == for x:B+y:B ? z:B"
				// );
				log_enc_add(db, &x_bin.xs, &y_bin.xs, &z_bin.xs)
			} else if let (IntVarEnc::Ord(y_ord), IntVarEnc::Bin(z_bin)) = (y, z) {
				let y_bin = IntVarBin::new(db, y_ord.ub(), "x_bin".to_string());
				TernLeEncoder::default()
					.encode(
						db,
						&TernLeConstraint::new(
							&y_ord.clone().into(),
							&IntVarEnc::Const(C::zero()),
							LimitComp::LessEq,
							&y_bin.clone().into(),
						),
					)
					.unwrap();
				self.encode(
					db,
					&TernLeConstraint::new(
						&x_bin.clone().into(),
						&y_bin.into(),
						cmp.clone(),
						&z_bin.clone().into(),
					),
				)
			} else {
				unimplemented!("LHS binary variables only implemented for some cases (and not tested in general method) for {x}, {y}, {z}")
			}
		} else if let (IntVarEnc::Ord(x_ord), IntVarEnc::Ord(y_ord), IntVarEnc::Bin(z_bin)) =
			(x, y, z)
		{
			let dom = ord_plus_ord_le_ord_sparse_dom(
				x.dom().into_iter(..).map(|c| c.end - C::one()).collect(),
				y.dom().into_iter(..).map(|c| c.end - C::one()).collect(),
				z.lb(),
				z.ub(),
			);
			let z_ord = IntVarOrd::from_syms(db, dom, String::from("z_ord"));
			self.encode(
				db,
				&TernLeConstraint::new(
					&x_ord.clone().into(),
					&y_ord.clone().into(),
					LimitComp::LessEq,
					&z_ord.clone().into(),
				),
			)?;
			self.encode(
				db,
				&TernLeConstraint::new(
					&z_ord.into(),
					&IntVarEnc::Const(C::zero()),
					LimitComp::LessEq,
					&z_bin.clone().into(),
				),
			)
		} else {
			for c_a in x.dom() {
				for c_b in y.dom() {
					// TODO tighten c_c.start
					let c_c = (std::cmp::min(c_a.start, c_b.start))
						..(((c_a.end - C::one()) + (c_b.end - C::one())) + C::one());
					let x_geq_c_a = x.geq(c_a.clone());
					let y_geq_c_b = y.geq(c_b.clone());
					let z_geq_c_c = z.geq(c_c.clone());

					add_clauses_for(db, negate_cnf(x_geq_c_a), negate_cnf(y_geq_c_b), z_geq_c_c)?;
				}
			}

			let leq = |x: &IntVarEnc<DB::Lit, C>, v: Range<C>| -> Vec<Vec<DB::Lit>> {
				negate_cnf(x.geq((v.start + C::one())..(v.end + C::one())))
			};

			// x<=a /\ y<=b -> z<=a+b
			if cmp == &LimitComp::Equal {
				for c_a in x.dom().iter(..) {
					for c_b in y.dom().iter(..) {
						let c_c = (c_a.end - C::one()) + (c_b.end - C::one());
						let c_c = c_c..(c_c + C::one());
						let x_geq_c_a = leq(x, c_a.clone());
						let y_geq_c_b = leq(y, c_b.clone());
						let z_geq_c_c = leq(z, c_c.clone());

						add_clauses_for(
							db,
							negate_cnf(x_geq_c_a),
							negate_cnf(y_geq_c_b),
							z_geq_c_c,
						)?;
					}
				}
			}
			Ok(())
		}
	}
}

pub(crate) fn add_clauses_for<DB: ClauseDatabase>(
	db: &mut DB,
	a: Vec<Vec<DB::Lit>>,
	b: Vec<Vec<DB::Lit>>,
	c: Vec<Vec<DB::Lit>>,
) -> Result {
	for cls_a in &a {
		for cls_b in &b {
			for cls_c in &c {
				emit_clause!(db, &[cls_a.clone(), cls_b.clone(), cls_c.clone()].concat())?
			}
		}
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
	#![allow(dead_code)]

	use super::*;
	use crate::helpers::tests::{assert_sol, assert_unsat, TestDB};
	use iset::interval_set;

	macro_rules! test_int_lin_ord_ord_ord {
		($encoder:expr,$x:expr,$y:expr,$cmp:expr,$z:expr) => {
			let mut db = TestDB::new(0);
			let x = from_dom(&mut db, $x, IntVarEncoding::Ord, String::from("x")).unwrap();
			let y = from_dom(&mut db, $y, IntVarEncoding::Ord, String::from("y")).unwrap();
			let z = from_dom(&mut db, $z, IntVarEncoding::Ord, String::from("z")).unwrap();

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

			#[test]
			fn test_int_lin_01_01_012() {
				test_int_lin_ord_ord_ord!($encoder, &[0, 1], &[0, 1], $cmp, &[0, 1, 2]);
			}

			#[test]
			fn test_int_lin_01_012_3() {
				test_int_lin_ord_ord_ord!($encoder, &[0, 1], &[0, 1, 2], $cmp, &[3]);
			}

			#[test]
			fn test_int_lin_01_01_3() {
				test_int_lin_ord_ord_ord!($encoder, &[0, 1], &[0, 1], $cmp, &[3]);
			}

			// #[test]
			// fn test_int_lin_01_02() {
			// test_int_lin_ord_ord_ord!(
			// $encoder,
			// &[0, 1],
			// &[0],
			// $cmp,
			// &[0, 1, 2]
			// );
			// }
		};
	}

	mod int_lin_le {
		int_lin_test_suite!(TernLeEncoder::default(), LimitComp::LessEq);
	}

	mod int_lin_eq {
		int_lin_test_suite!(TernLeEncoder::default(), LimitComp::Equal);
	}

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
		let x = IntVarBin::new(db, ub, lbl);
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
	fn bin_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_bin_x::<_, i32>(&mut db, 12, true, "x".to_string());
		let x_lin: LinExp<i32, i32> = LinExp::from(&x);

		assert_eq!(x.lits(), 4);
		assert_eq!(x.lb(), 0);
		assert_eq!(x.ub(), 12);
		assert_eq!(x.geq(7..8), vec![vec![1, 4]]); // 7-1=6 == 0110 (right-to-left!)
		assert_eq!(x.geq(5..8), vec![vec![1, 2, 4], vec![2, 4], vec![1, 4]]); // 4=0100,5=0101,6=0110

		assert_eq!(x_lin.assign(&[-1, -2, -3, -4]), Ok(0));
		assert_eq!(x_lin.assign(&[1, -2, -3, -4]), Ok(1));
		assert_eq!(x_lin.assign(&[1, 2, -3, -4]), Ok(3));
		assert_eq!(x_lin.assign(&[1, 2, -3, 4]), Ok(11));
		assert_eq!(x_lin.assign(&[1, 2, 3, 4]), Ok(15));

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			cmp: LimitComp::LessEq,
			z: &IntVarEnc::Const(10), // TODO no consistency implemented for this bound yet
		};

		db.num_var = x.lits() as i32;

		db.generate_solutions(
			|sol| {
				tern.check(sol).is_ok()
					&& match &x {
						IntVarEnc::Bin(b) => b._consistency(),
						_ => unreachable!(),
					}
					.get()
					.check(sol)
					.is_ok()
			},
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
		let x = IntVarBin::new(&mut db, 12, "x".to_string());
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
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
			get_ord_x(&mut db, interval_set!(2..3, 4..5), true, "y".to_string()),
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
			get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
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

		// let sols = db.generate_solutions(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<i32, i32>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<i32, i32>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

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

	#[test]
	fn bin_plus_ord_eq_bin_test() {
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
		Dir,
		Ord,
		Bin,
	}

	fn from_bounds<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		lb: C,
		ub: C,
		enc: IntVarEncoding,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		if lb == ub {
			IntVarEnc::Const(lb)
		} else {
			match enc {
				IntVarEncoding::Ord => IntVarOrd::from_bounds(db, lb, ub, lbl).into(),
				_ => todo!(),
			}
		}
	}

	fn from_dom<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: &[C],
		enc: IntVarEncoding,
		lbl: String,
	) -> Result<IntVarEnc<DB::Lit, C>> {
		match dom {
			[] => Err(Unsatisfiable),
			[d] => Ok(IntVarEnc::Const(*d)),
			dom => Ok(match enc {
				IntVarEncoding::Ord => IntVarOrd::from_dom(db, dom, lbl).into(),
				_ => todo!(),
			}),
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
#[derive(PartialEq)]
pub(crate) enum Consistency {
	None,
	Bounds,
	Domain,
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
		let var = self.new_var(x.dom().iter(..).map(|d| d.end - C::one()).collect());
		self.vars.insert(var.id, x);
		var
	}

	pub fn new_var(&mut self, dom: BTreeSet<C>) -> IntVar<C> {
		self.var_ids += 1;
		IntVar {
			id: self.var_ids,
			dom,
		}
	}

	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result {
		for con in &self.cons {
			let Lin { xs, cmp } = con;
			assert!(
				con.xs.len() == 3
					&& con.xs.iter().map(|(c, _)| c).collect::<Vec<_>>()
						== [&C::one(), &C::one(), &-C::one()]
			);

			for (_, x) in xs {
				self.vars.entry(x.borrow().id).or_insert_with(|| {
					let enc = x.borrow().encode(db);
					enc
				});
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

	pub(crate) fn propagate(&mut self, consistency: Consistency, mut queue: Vec<usize>) {
		if consistency == Consistency::None {
			return;
		}
		while let Some(con) = queue.pop() {
			let changed = self.cons[con].propagate(&consistency);
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
		let mut i = 0;
		let mut changed = vec![];
		match consistency {
			Consistency::None => unreachable!(),
			Consistency::Bounds => loop {
				let mut fixpoint = true;
				i += 1;
				if i > 10 {
					panic!();
				}
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
						println!("Pruned {}", size - x.size());
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
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct IntVar<C: Coefficient> {
	pub(crate) id: usize,
	pub(crate) dom: BTreeSet<C>,
}

impl<C: Coefficient> IntVar<C> {
	fn encode<DB: ClauseDatabase>(&self, db: &mut DB) -> IntVarEnc<DB::Lit, C> {
		if self.size() == 1 {
			IntVarEnc::Const(*self.dom.first().unwrap())
		} else {
			IntVarEnc::Ord(IntVarOrd::from_dom(
				db,
				self.dom
					.iter()
					.sorted()
					.cloned()
					.collect::<Vec<_>>()
					.as_slice(),
				"x".to_string(),
			))
		}
	}

	fn ge(&mut self, bound: &C) {
		self.dom = self.dom.split_off(bound);
	}

	fn le(&mut self, bound: &C) {
		self.dom.split_off(&(*bound + C::one()));
	}

	fn size(&self) -> usize {
		self.dom.len()
	}

	fn lb(&self, c: &C) -> C {
		*c * *(if c.is_negative() {
			self.dom.last()
		} else {
			self.dom.first()
		})
		.unwrap()
	}

	fn ub(&self, c: &C) -> C {
		*c * *(if c.is_negative() {
			self.dom.first()
		} else {
			self.dom.last()
		})
		.unwrap()
	}
}
