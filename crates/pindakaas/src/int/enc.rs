use std::{
	collections::HashSet,
	fmt,
	fmt::Display,
	ops::{Not, Range},
};

use iset::{interval_map, interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use rustc_hash::{FxBuildHasher, FxHashMap};

use super::display_dom;
use crate::{
	helpers::{as_binary, emit_clause, is_powers_of_two, new_var, unsigned_binary_range_ub},
	int::{IntVar, TernLeConstraint, TernLeEncoder},
	linear::{LimitComp, LinExp, Part, PosCoeff},
	CheckError, Checker, ClauseDatabase, Coeff, Encoder, Lit, Result, Unsatisfiable, Valuation,
};

#[allow(
	variant_size_differences,
	reason = "bool is 1 byte, but Lit will always require more"
)]
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LitOrConst {
	Lit(Lit),
	Const(bool),
}

impl From<Lit> for LitOrConst {
	fn from(item: Lit) -> Self {
		LitOrConst::Lit(item)
	}
}

impl From<bool> for LitOrConst {
	fn from(item: bool) -> Self {
		LitOrConst::Const(item)
	}
}

impl Display for LitOrConst {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LitOrConst::Const(b) => write!(f, "{b}"),
			LitOrConst::Lit(l) => write!(f, "{l}"),
		}
	}
}

impl Not for LitOrConst {
	type Output = LitOrConst;
	fn not(self) -> Self::Output {
		match self {
			LitOrConst::Lit(l) => (!l).into(),
			LitOrConst::Const(b) => (!b).into(),
		}
	}
}

impl Display for IntVarOrd {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:O ∈ {}",
			self.lbl,
			display_dom(&self.dom().iter(..).map(|d| d.end - 1).collect())
		)
	}
}

pub(crate) const GROUND_BINARY_AT_LB: bool = false;

impl Display for IntVarBin {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(
			f,
			"{}:B ∈ {} [{}]",
			self.lbl,
			display_dom(&self.dom().iter(..).map(|d| d.end - 1).collect()),
			self.lits()
		)
	}
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarOrd {
	pub(crate) xs: IntervalMap<Coeff, Lit>,
	pub(crate) lbl: String,
}

impl IntVarOrd {
	pub(crate) fn from_bounds<DB: ClauseDatabase>(
		db: &mut DB,
		lb: Coeff,
		ub: Coeff,
		lbl: String,
	) -> Self {
		Self::from_dom(db, (lb..=ub).collect_vec().as_slice(), lbl)
	}

	pub(crate) fn from_dom<DB: ClauseDatabase>(db: &mut DB, dom: &[Coeff], lbl: String) -> Self {
		Self::from_syms(
			db,
			dom.iter()
				.tuple_windows()
				.map(|(a, b)| (a + 1)..(b + 1))
				.collect(),
			lbl,
		)
	}

	pub(crate) fn from_syms<DB: ClauseDatabase>(
		db: &mut DB,
		syms: IntervalSet<Coeff>,
		lbl: String,
	) -> Self {
		Self::from_views(db, syms.into_iter(..).map(|c| (c, None)).collect(), lbl)
	}

	pub(crate) fn from_views<DB: ClauseDatabase>(
		db: &mut DB,
		views: IntervalMap<Coeff, Option<Lit>>,
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
				#[cfg(any(feature = "tracing", test))]
				let lbl = format!("{lbl}>={}..{}", v.start, v.end - 1);
				(v, lit.unwrap_or_else(|| new_var!(db, lbl)))
			})
			.collect::<IntervalMap<_, _>>();
		Self { xs, lbl }
	}

	pub(crate) fn consistency(&self) -> ImplicationChainConstraint {
		ImplicationChainConstraint {
			lits: self.xs.values(..).cloned().collect_vec(),
		}
	}

	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB) -> Result {
		ImplicationChainEncoder::default()._encode(db, &self.consistency())
	}

	pub(crate) fn div(&self, c: Coeff) -> IntVarEnc {
		assert!(c == 2, "Can only divide IntVarOrd by 2");
		let xs: IntervalMap<_, _> = self
			.xs
			.iter(..)
			.filter(|(c, _)| (c.end - 1) % 2 == 0)
			.map(|(c, l)| (((c.end - 1) / (1 + 1)), *l))
			.map(|(c, l)| (c..(c + 1), l))
			.collect();

		if xs.is_empty() {
			IntVarEnc::Const(self.lb() / c)
		} else {
			IntVarOrd {
				xs,
				lbl: self.lbl.clone(),
			}
			.into()
		}
	}

	pub(crate) fn dom(&self) -> IntervalSet<Coeff> {
		std::iter::once(self.lb()..(self.lb() + 1))
			.chain(self.xs.intervals(..))
			.collect()
	}

	pub(crate) fn leqs(&self) -> Vec<(Range<Coeff>, Vec<Vec<Lit>>)> {
		self.xs
			.iter(..)
			.map(|(v, x)| ((v.start - 1)..(v.end - 1), vec![vec![!x]]))
			.chain(std::iter::once((self.ub()..self.ub() + 1, vec![])))
			.collect()
	}

	pub(crate) fn geqs(&self) -> Vec<(Range<Coeff>, Vec<Vec<Lit>>)> {
		std::iter::once((self.lb()..(self.lb() + 1), vec![]))
			.chain(self.xs.iter(..).map(|(v, x)| (v, vec![vec![*x]])))
			.collect()
	}

	pub(crate) fn lb(&self) -> Coeff {
		self.xs.range().unwrap().start - 1
	}

	pub(crate) fn ub(&self) -> Coeff {
		self.xs.range().unwrap().end - 1
	}

	pub(crate) fn leq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		let v = v.start + 1; // [x<=v] = [x < v+1]
		if v <= self.lb() {
			vec![vec![]]
		} else if v > self.ub() {
			vec![]
		} else {
			match self.xs.overlap(v).collect_vec()[..] {
				[(_, x)] => vec![vec![!x]],
				_ => panic!("No or multiples literals at {v:?} for var {self:?}"),
			}
		}
	}

	pub(crate) fn geq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		let v = v.end - 1;
		if v <= self.lb() {
			vec![]
		} else if v > self.ub() {
			vec![vec![]]
		} else {
			match self.xs.overlap(v).collect_vec()[..] {
				[(_, x)] => vec![vec![*x]],
				_ => panic!("No or multiples literals at {v:?} for var {self:?}"),
			}
		}
	}

	#[cfg(test)]
	pub(crate) fn lits(&self) -> usize {
		self.xs.len()
	}
}

impl From<&IntVarOrd> for LinExp {
	fn from(value: &IntVarOrd) -> Self {
		let mut acc = value.lb();
		LinExp::default()
			.add_chain(
				&value
					.xs
					.iter(..)
					.map(|(iv, lit)| {
						let v = iv.end - 1 - acc;
						acc += v;
						(*lit, v)
					})
					.collect_vec(),
			)
			.add_constant(value.lb())
	}
}

pub(crate) struct ImplicationChainConstraint {
	lits: Vec<Lit>,
}

#[derive(Default)]
pub(crate) struct ImplicationChainEncoder {}

impl ImplicationChainEncoder {
	pub(crate) fn _encode<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
		ic: &ImplicationChainConstraint,
	) -> Result {
		for (a, b) in ic.lits.iter().copied().tuple_windows() {
			emit_clause!(db, [!b, a])?;
		}
		Ok(())
	}
}

impl Checker for ImplicationChainConstraint {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<(), CheckError> {
		for (a, b) in self.lits.iter().copied().tuple_windows() {
			if sol.value(a).unwrap_or(true) & !sol.value(b).unwrap_or(false) {
				return Err(Unsatisfiable.into());
			}
		}
		Ok(())
	}
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarBin {
	pub(crate) xs: Vec<Lit>,
	lb: Coeff,
	ub: Coeff,
	lbl: String,
}

impl IntVarBin {
	// TODO change to with_label or something
	pub(crate) fn from_bounds<DB: ClauseDatabase>(
		db: &mut DB,
		lb: Coeff,
		ub: Coeff,
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

	pub(crate) fn from_terms(
		terms: Vec<(Lit, PosCoeff)>,
		lb: PosCoeff,
		ub: PosCoeff,
		lbl: String,
	) -> Self {
		debug_assert!(is_powers_of_two(terms.iter().map(|(_, c)| **c)));
		Self {
			xs: terms.into_iter().map(|(l, _)| l).collect(),
			lb: *lb, // TODO support non-zero
			ub: *ub,
			lbl,
		}
	}

	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB) -> Result {
		let encoder = TernLeEncoder::default();
		if !GROUND_BINARY_AT_LB {
			encoder.encode(
				db,
				&TernLeConstraint {
					x: &IntVarEnc::Const(self.lb),
					y: &IntVarEnc::Const(0),
					cmp: LimitComp::LessEq,
					z: &IntVarEnc::Bin(self.clone()),
				},
			)?;
		}
		encoder.encode(
			db,
			&TernLeConstraint {
				x: &IntVarEnc::Bin(self.clone()),
				y: &IntVarEnc::Const(0),
				cmp: LimitComp::LessEq,
				z: &IntVarEnc::Const(self.ub),
			},
		)
	}

	fn div(&self, _: Coeff) -> IntVarEnc {
		todo!()
	}

	fn dom(&self) -> IntervalSet<Coeff> {
		(self.lb..=self.ub).map(|i| i..(i + 1)).collect()
	}

	pub(crate) fn lb(&self) -> Coeff {
		self.lb
	}

	pub(crate) fn ub(&self) -> Coeff {
		self.ub
	}

	pub(crate) fn geq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		self.ineq(v, true)
	}

	pub(crate) fn leq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		self.ineq(v, false)
	}

	fn ineq(&self, v: Range<Coeff>, geq: bool) -> Vec<Vec<Lit>> {
		// TODO could *maybe* be domain lb/ub
		let v = if GROUND_BINARY_AT_LB {
			(v.start - self.lb())..(v.end - self.lb())
		} else {
			v
		};

		// The range 0..(2^n)-1 covered by the (unsigned) binary representation
		let range_lb = 0;
		let range_ub = unsigned_binary_range_ub(self.lits() as u32);

		let range = std::cmp::max(range_lb - 1, v.start)..std::cmp::min(v.end, range_ub + 1 + 1);
		range
			.filter_map(|v| {
				let v = if geq { v - 1 } else { v + 1 };
				if v < range_lb {
					(!geq).then_some(vec![])
				} else if v > range_ub {
					geq.then_some(vec![])
				} else {
					Some(
						as_binary(PosCoeff::new(v), Some(self.lits() as u32))
							.into_iter()
							.zip(self.xs.iter())
							// if >=, find 0s, if <=, find 1s
							.filter_map(|(b, x)| (b != geq).then_some(x))
							.map(|x| if geq { *x } else { !x })
							.collect(),
					)
				}
			})
			.collect()
	}

	pub(crate) fn lits(&self) -> usize {
		self.xs.len()
	}

	pub(crate) fn add<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		encoder: &TernLeEncoder,
		y: Coeff,
	) -> Result<Self> {
		if y == 0 {
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

impl From<&IntVarBin> for LinExp {
	fn from(value: &IntVarBin) -> Self {
		let mut k = 1;
		let terms = value
			.xs
			.iter()
			.map(|x| {
				let term = (*x, k);
				k *= 2;
				term
			})
			.collect_vec();
		let lin_exp =
			LinExp::default().add_bounded_log_encoding(terms.as_slice(), value.lb, value.ub);
		if GROUND_BINARY_AT_LB {
			lin_exp.add_constant(value.lb)
		} else {
			lin_exp
		}
	}
}

#[derive(Debug, Clone)]
pub(crate) enum IntVarEnc {
	Ord(IntVarOrd),
	Bin(IntVarBin),
	Const(Coeff),
}

const COUPLE_DOM_PART_TO_ORD: bool = false;

impl IntVarEnc {
	/// Constructs (one or more) IntVar `ys` for linear expression `xs` so that ∑ xs ≦ ∑ ys
	pub(crate) fn from_part<DB: ClauseDatabase>(
		db: &mut DB,
		xs: &Part,
		ub: PosCoeff,
		lbl: String,
	) -> Vec<Self> {
		match xs {
			Part::Amo(terms) => {
				let terms: Vec<(Coeff, Lit)> = terms
					.iter()
					.copied()
					.map(|(lit, coef)| (*coef, lit))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: FxHashMap<Coeff, Vec<Lit>> =
					FxHashMap::with_capacity_and_hasher(terms.len(), FxBuildHasher);
				for (coef, lit) in terms {
					debug_assert!(coef <= *ub);
					h.entry(coef).or_default().push(lit);
				}

				let dom = std::iter::once((0, vec![]))
					.chain(h)
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					.tuple_windows()
					.map(|((prev, _), (coef, lits))| {
						let interval = (prev + 1)..(coef + 1);
						if lits.len() == 1 {
							(interval, Some(lits[0]))
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								emit_clause!(db, [!lit, o]).unwrap();
							}
							(interval, Some(o))
						}
					})
					.collect::<IntervalMap<_, _>>();
				vec![IntVarEnc::Ord(IntVarOrd::from_views(db, dom, lbl))]
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = 0; // running sum
				let dom = std::iter::once(&(terms[0].0, PosCoeff::new(0)))
					.chain(terms.iter())
					.map(|&(lit, coef)| {
						acc += *coef;
						debug_assert!(acc <= *ub);
						(acc, lit)
					})
					.tuple_windows()
					.map(|((prev, _), (coef, lit))| ((prev + 1)..(coef + 1), Some(lit)))
					.collect::<IntervalMap<_, _>>();
				vec![IntVarEnc::Ord(IntVarOrd::from_views(db, dom, lbl))]
			}
			Part::Dom(terms, l, u) => {
				// TODO account for bounds (or even better, create IntVarBin)
				// TODO old method (which at least respected bounds)
				if COUPLE_DOM_PART_TO_ORD {
					let x_bin = IntVarBin::from_terms(terms.to_vec(), *l, *u, String::from("x"));
					let x_ord = IntVarEnc::Ord(IntVarOrd::from_bounds(
						db,
						x_bin.lb(),
						x_bin.ub(),
						String::from("x"),
					));

					TernLeEncoder::default()
						.encode(
							db,
							&TernLeConstraint::new(
								&x_ord,
								&IntVarEnc::Const(0),
								LimitComp::LessEq,
								&x_bin.into(),
							),
						)
						.unwrap();
					vec![x_ord]
				} else {
					terms
						.iter()
						.enumerate()
						.map(|(i, (lit, coef))| {
							IntVarEnc::Ord(IntVarOrd::from_views(
								db,
								interval_map! { 1..(**coef+1) => Some(*lit) },
								format!("{lbl}^{i}"),
							))
						})
						.collect()
				}
			} // TODO Not so easy to transfer a binary encoded int var
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

	pub(crate) fn add<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		encoder: &TernLeEncoder,
		y: &IntVarEnc,
		lb: Option<Coeff>,
		ub: Option<Coeff>,
		// cmp: &LimitComp,
		// enc: &'a mut dyn Encoder<DB, TernLeConstraint<'a, DB, C>>,
	) -> Result<IntVarEnc> {
		let comp_lb = self.lb() + y.lb();
		let lb = std::cmp::max(lb.unwrap_or(comp_lb), comp_lb);

		let comp_ub = self.ub() + y.ub();
		let ub = std::cmp::min(ub.unwrap_or(comp_ub), comp_ub);

		match (self, y) {
			(IntVarEnc::Const(a), IntVarEnc::Const(b)) => Ok(IntVarEnc::Const(*a + *b)),
			// TODO only used in sorters which enforce the constraints later!
			(IntVarEnc::Const(c), x) | (x, IntVarEnc::Const(c)) if (*c == 0) => Ok(x.clone()),
			(IntVarEnc::Ord(x), IntVarEnc::Ord(y)) => Ok(IntVarEnc::Ord(IntVarOrd::from_syms(
				db,
				ord_plus_ord_le_ord_sparse_dom(
					x.dom().iter(..).map(|d| d.end - 1).collect(),
					y.dom().iter(..).map(|d| d.end - 1).collect(),
					lb,
					ub,
				),
				format!("{}+{}", x.lbl, y.lbl),
			))),
			(IntVarEnc::Ord(x), IntVarEnc::Const(y)) | (IntVarEnc::Const(y), IntVarEnc::Ord(x)) => {
				let xs =
					x.xs.iter(..)
						.map(|(c, l)| ((c.start + *y)..(c.end + *y), *l))
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

	pub(crate) fn leqs(&self) -> Vec<(Range<Coeff>, Vec<Vec<Lit>>)> {
		match self {
			IntVarEnc::Ord(o) => o.leqs(),
			x => x
				.dom()
				.into_iter(..)
				.map(|c| (c.clone(), x.leq(c)))
				.collect(),
		}
	}

	pub(crate) fn geqs(&self) -> Vec<(Range<Coeff>, Vec<Vec<Lit>>)> {
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
	pub(crate) fn leq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.leq(v),
			IntVarEnc::Bin(b) => b.leq(v),
			IntVarEnc::Const(c) => {
				let v = v.start + 1; // [x<=v] = [x < v+1]
				if v <= *c {
					vec![vec![]]
				} else {
					vec![]
				}
			}
		}
	}

	/// Returns a clause constraining `x>=v`, which is None if true and empty if false
	pub(crate) fn geq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		match self {
			IntVarEnc::Ord(o) => o.geq(v),
			IntVarEnc::Bin(b) => b.geq(v),
			IntVarEnc::Const(c) => {
				let v = v.end - 1;
				if v <= *c {
					vec![]
				} else {
					vec![vec![]]
				}
			}
		}
	}

	pub(crate) fn div(&self, c: Coeff) -> IntVarEnc {
		match self {
			IntVarEnc::Ord(o) => o.div(c),
			IntVarEnc::Bin(b) => b.div(c),
			&IntVarEnc::Const(m) => IntVarEnc::Const(m / c),
		}
	}

	/// Returns a partitioned domain
	pub(crate) fn dom(&self) -> IntervalSet<Coeff> {
		match self {
			IntVarEnc::Ord(o) => o.dom(),
			IntVarEnc::Bin(b) => b.dom(),
			&IntVarEnc::Const(c) => interval_set!(c..(c + 1)),
		}
	}

	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB) -> Result {
		match self {
			IntVarEnc::Ord(o) => o.consistent(db),
			IntVarEnc::Bin(b) => b.consistent(db),
			IntVarEnc::Const(_) => Ok(()),
		}
	}

	pub(crate) fn lb(&self) -> Coeff {
		match self {
			IntVarEnc::Ord(o) => o.lb(),
			IntVarEnc::Bin(b) => b.lb(),
			IntVarEnc::Const(c) => *c,
			// _ => self.dom().range().unwrap().start - 1,
		}
	}

	pub(crate) fn ub(&self) -> Coeff {
		match self {
			IntVarEnc::Ord(o) => o.ub(),
			IntVarEnc::Bin(b) => b.ub(),
			IntVarEnc::Const(c) => *c,
			// _ => self.dom().range().unwrap().end - 1,
		}
	}

	/// Return number of lits in encoding
	#[cfg(test)]
	pub(crate) fn lits(&self) -> usize {
		match self {
			IntVarEnc::Ord(o) => o.lits(),
			IntVarEnc::Bin(b) => b.lits(),
			IntVarEnc::Const(_) => 0,
		}
	}
}

impl From<&IntVarEnc> for LinExp {
	fn from(value: &IntVarEnc) -> Self {
		match value {
			IntVarEnc::Ord(o) => o.into(),
			IntVarEnc::Bin(b) => b.into(),
			&IntVarEnc::Const(c) => c.into(),
		}
	}
}

impl From<IntVarBin> for IntVarEnc {
	fn from(b: IntVarBin) -> Self {
		Self::Bin(b)
	}
}

impl From<IntVarOrd> for IntVarEnc {
	fn from(o: IntVarOrd) -> Self {
		Self::Ord(o)
	}
}

impl Display for IntVarEnc {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			IntVarEnc::Ord(o) => o.fmt(f),
			IntVarEnc::Bin(b) => b.fmt(f),
			IntVarEnc::Const(o) => write!(f, "{o:?}"),
		}
	}
}
pub(crate) fn ord_plus_ord_le_ord_sparse_dom(
	a: Vec<Coeff>,
	b: Vec<Coeff>,
	l: Coeff,
	u: Coeff,
) -> IntervalSet<Coeff> {
	// TODO optimize by dedup (if already sorted?)
	HashSet::<Coeff>::from_iter(a.iter().flat_map(|a| {
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
	.map(|(a, b)| (a + 1)..(b + 1))
	.collect::<IntervalSet<_>>()
}
