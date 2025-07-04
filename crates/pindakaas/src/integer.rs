use std::{
	cell::RefCell,
	cmp::{max, min},
	collections::BTreeSet,
	fmt::{self, Display},
	iter::once,
	ops::Range,
	rc::Rc,
};

use iset::{interval_map, interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};

use crate::{
	bool_linear::{BoolLinExp, LimitComp, Part, PosCoeff},
	helpers::{
		add_clauses_for, as_binary, is_powers_of_two, negate_cnf, new_named_lit,
		unsigned_binary_range_ub,
	},
	BoolVal, Checker, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Lit, Result,
	Unsatisfiable, Valuation,
};

const COUPLE_DOM_PART_TO_ORD: bool = false;
const ENCODE_REDUNDANT_X_O_Y_O_Z_B: bool = true;
pub(crate) const GROUND_BINARY_AT_LB: bool = false;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Consistency {
	None,
	#[default]
	Bounds,
	Domain,
}

pub(crate) struct ImplicationChainConstraint {
	lits: Vec<Lit>,
}

#[derive(Default)]
pub(crate) struct ImplicationChainEncoder {}

// TODO perhaps id can be used by replacing vars HashMap to just vec
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IntVar {
	pub(crate) id: usize,
	pub(crate) dom: BTreeSet<Coeff>,
	add_consistency: bool,
	pub(crate) views: FxHashMap<Coeff, (usize, Coeff)>,
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarBin {
	pub(crate) xs: Vec<Lit>,
	lb: Coeff,
	ub: Coeff,
	lbl: String,
}

#[derive(Debug, Clone)]
pub(crate) enum IntVarEnc {
	Ord(IntVarOrd),
	Bin(IntVarBin),
	Const(Coeff),
}

#[derive(Debug, Clone)]
pub(crate) struct IntVarOrd {
	pub(crate) xs: IntervalMap<Coeff, Lit>,
	pub(crate) lbl: String,
}

#[derive(Debug)]
pub(crate) struct Lin {
	pub(crate) xs: Vec<(Coeff, Rc<RefCell<IntVar>>)>,
	pub(crate) cmp: LimitComp,
}

#[derive(Debug, Default)]
pub(crate) struct Model {
	vars: FxHashMap<usize, IntVarEnc>,
	pub(crate) cons: Vec<Lin>,
	var_ids: usize,
}

#[derive(Debug)]
pub(crate) struct TernLeConstraint<'a> {
	pub(crate) x: &'a IntVarEnc,
	pub(crate) y: &'a IntVarEnc,
	pub(crate) cmp: LimitComp,
	pub(crate) z: &'a IntVarEnc,
}

#[derive(Debug, Default)]
pub(crate) struct TernLeEncoder {}

pub(crate) fn display_dom(dom: &BTreeSet<Coeff>) -> String {
	const ELIPSIZE: usize = 8;
	let (lb, ub) = (*dom.first().unwrap(), *dom.last().unwrap());
	if dom.len() > ELIPSIZE && dom.len() == (ub - lb + 1) as usize {
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

/// Uses lexicographic constraint to constrain x:B >= k
#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "lex_geq", skip_all)
)]
pub(crate) fn lex_geq_const<DB: ClauseDatabase + ?Sized>(
	db: &mut DB,
	x: &[Option<Lit>],
	k: PosCoeff,
	bits: usize,
) -> Result {
	let k = as_binary(k, Some(bits as u32));
	for i in 0..bits {
		if k[i] && x[i].is_some() {
			db.add_clause((i..bits).filter_map(|j| if j == i || !k[j] { x[j] } else { None }))?;
		}
	}
	Ok(())
}

/// Uses lexicographic constraint to constrain x:B ≦ k
#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "lex_lesseq_const", skip_all)
)]
pub(crate) fn lex_leq_const<DB: ClauseDatabase + ?Sized>(
	db: &mut DB,
	x: &[Option<Lit>],
	k: PosCoeff,
	bits: usize,
) -> Result {
	let k = as_binary(k, Some(bits as u32));
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	for i in 0..bits {
		if !k[i] && x[i].is_some() {
			db.add_clause(
				(i..bits)
					.filter_map(|j| if j == i || k[j] { x[j] } else { None })
					.map(|lit| !lit),
			)?;
		}
	}
	Ok(())
}

/// Constrains the slice `z`, to be the result of adding `x` to `y`, all encoded using the log encoding.
///
/// TODO: Should this use the IntEncoding::Log input??
pub(crate) fn log_enc_add<DB: ClauseDatabase + ?Sized>(
	db: &mut DB,
	x: &[Lit],
	y: &[Lit],
	cmp: &LimitComp,
	z: &[Lit],
) -> Result {
	log_enc_add_(
		db,
		&x.iter().copied().map(BoolVal::from).collect_vec(),
		&y.iter().copied().map(BoolVal::from).collect_vec(),
		cmp,
		&z.iter().copied().map(BoolVal::from).collect_vec(),
	)
}

#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("{x:?} + {y:?} {cmp} {z:?}"))))]
pub(crate) fn log_enc_add_<DB: ClauseDatabase + ?Sized>(
	db: &mut DB,
	x: &[BoolVal],
	y: &[BoolVal],
	cmp: &LimitComp,
	z: &[BoolVal],
) -> Result {
	let n = itertools::max([x.len(), y.len(), z.len()]).unwrap();

	let bit =
		|x: &[BoolVal], i: usize| -> BoolVal { x.get(i).copied().unwrap_or(BoolVal::Const(false)) };

	match cmp {
		LimitComp::Equal => {
			let c = &once(BoolVal::Const(false))
				.chain((1..n).map(|_i| {
					BoolVal::Lit(new_named_lit!(db, crate::trace::subscripted_name("c", _i)))
				}))
				.collect_vec();
			for i in 0..n {
				// sum circuit
				db.add_clause([bit(x, i), bit(y, i), bit(c, i), !bit(z, i)])?;
				db.add_clause([bit(x, i), !bit(y, i), !bit(c, i), !bit(z, i)])?;
				db.add_clause([!bit(x, i), bit(y, i), !bit(c, i), !bit(z, i)])?;
				db.add_clause([!bit(x, i), !bit(y, i), bit(c, i), !bit(z, i)])?;

				db.add_clause([!bit(x, i), !bit(y, i), !bit(c, i), bit(z, i)])?;
				db.add_clause([!bit(x, i), bit(y, i), bit(c, i), bit(z, i)])?;
				db.add_clause([bit(x, i), !bit(y, i), bit(c, i), bit(z, i)])?;
				db.add_clause([bit(x, i), bit(y, i), !bit(c, i), bit(z, i)])?;

				// carry circuit
				db.add_clause([bit(x, i), bit(y, i), !bit(c, i + 1)])?;
				db.add_clause([bit(x, i), bit(c, i), !bit(c, i + 1)])?;
				db.add_clause([bit(y, i), bit(c, i), !bit(c, i + 1)])?;
				db.add_clause([!bit(x, i), !bit(y, i), bit(c, i + 1)])?;
				db.add_clause([!bit(x, i), !bit(c, i), bit(c, i + 1)])?;
				db.add_clause([!bit(y, i), !bit(c, i), bit(c, i + 1)])?;
			}
			Ok(())
		}
		LimitComp::LessEq => {
			let c = &(0..n)
				.map(|_i| BoolVal::Lit(new_named_lit!(db, crate::trace::subscripted_name("c", _i))))
				.chain(once(BoolVal::Const(true)))
				.collect_vec();

			// higher i -> more significant
			for i in 0..n {
				// c = all more significant bits are equal AND current one is
				// if up to i is equal, all preceding must be equal
				db.add_clause([!bit(c, i), bit(c, i + 1)])?;
				// if up to i is equal, x<->z
				db.add_clause([!bit(c, i), !bit(x, i), bit(z, i)])?;
				db.add_clause([!bit(c, i), !bit(z, i), bit(x, i)])?;

				// if not up to i is equal, either preceding bit was not equal, or x!=z
				db.add_clause([bit(c, i), !bit(c, i + 1), bit(x, i), bit(z, i)])?;
				db.add_clause([bit(c, i), !bit(c, i + 1), !bit(x, i), !bit(z, i)])?;

				// if preceding bits are equal, then x<=z
				db.add_clause([!bit(c, i + 1), !bit(x, i), bit(z, i)])?;
			}

			db.add_clause([!bit(x, n - 1), bit(z, n - 1)])?;

			Ok(())
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
	FxHashSet::<Coeff>::from_iter(a.iter().flat_map(|a| {
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

impl Checker for ImplicationChainConstraint {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result {
		for (a, b) in self.lits.iter().copied().tuple_windows() {
			if sol.value(a) & !sol.value(b) {
				return Err(Unsatisfiable);
			}
		}
		Ok(())
	}
}

impl ImplicationChainEncoder {
	pub(crate) fn _encode<DB: ClauseDatabase + ?Sized>(
		&mut self,
		db: &mut DB,
		ic: &ImplicationChainConstraint,
	) -> Result {
		for (a, b) in ic.lits.iter().copied().tuple_windows() {
			db.add_clause([!b, a])?;
		}
		Ok(())
	}
}

impl IntVar {
	fn encode<DB: ClauseDatabase + ?Sized>(
		&self,
		db: &mut DB,
		views: &mut FxHashMap<(usize, Coeff), Lit>,
		prefer_order: bool,
	) -> IntVarEnc {
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
					.map(|(a, b)| (a + 1)..(b + 1))
					.map(|v| (v.clone(), views.get(&(self.id, v.end - 1)).cloned()))
					.collect::<IntervalMap<_, _>>();
				IntVarEnc::Ord(IntVarOrd::from_views(db, dom, "x".to_owned()))
			} else {
				let y = IntVarBin::from_bounds(
					db,
					*self.dom.first().unwrap(),
					*self.dom.last().unwrap(),
					"x".to_owned(),
				);
				IntVarEnc::Bin(y)
			};

			if self.add_consistency {
				x.consistent(db).unwrap();
			}

			for view in self
				.views
				.iter()
				.map(|(c, (id, val))| ((*id, *val), x.geq(*c..(*c + 1))))
			{
				// TODO refactor
				if !view.1.is_empty() {
					let _ = views.insert(view.0, view.1[0][0]);
				}
			}
			x
		}
	}

	fn ge(&mut self, bound: &Coeff) {
		self.dom = self.dom.split_off(bound);
	}

	pub(crate) fn lb(&self, c: &Coeff) -> Coeff {
		*c * *(if c.is_negative() {
			self.dom.last()
		} else {
			self.dom.first()
		})
		.unwrap()
	}

	fn le(&mut self, bound: &Coeff) {
		let _ = self.dom.split_off(&(*bound + 1));
	}

	fn prefer_order(&self, cutoff: Option<Coeff>) -> bool {
		match cutoff {
			None => true,
			Some(0) => false,
			Some(cutoff) => (self.dom.len() as Coeff) < cutoff,
		}
	}

	pub(crate) fn required_bits(lb: Coeff, ub: Coeff) -> u32 {
		const ZERO: Coeff = 0;
		if GROUND_BINARY_AT_LB {
			ZERO.leading_zeros() - ((ub - lb).leading_zeros())
		} else {
			ZERO.leading_zeros() - (ub.leading_zeros())
		}
	}

	pub(crate) fn size(&self) -> usize {
		self.dom.len()
	}

	pub(crate) fn ub(&self, c: &Coeff) -> Coeff {
		*c * *(if c.is_negative() {
			self.dom.first()
		} else {
			self.dom.last()
		})
		.unwrap()
	}
}

impl Display for IntVar {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "x{} ∈ {}", self.id, display_dom(&self.dom))
	}
}

impl IntVarBin {
	pub(crate) fn add<DB: ClauseDatabase + ?Sized>(
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

	pub(crate) fn consistent<DB: ClauseDatabase + ?Sized>(&self, db: &mut DB) -> Result {
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
	// TODO change to with_label or something
	pub(crate) fn from_bounds<DB: ClauseDatabase + ?Sized>(
		db: &mut DB,
		lb: Coeff,
		ub: Coeff,
		lbl: String,
	) -> Self {
		Self {
			xs: (0..IntVar::required_bits(lb, ub))
				.map(|_i| new_named_lit!(db, format!("{}^{}", lbl, _i)))
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

	pub(crate) fn geq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		self.ineq(v, true)
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

		let range = max(range_lb - 1, v.start)..min(v.end, range_ub + 1 + 1);
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
							.map(|&x| if geq { x } else { !x })
							.collect(),
					)
				}
			})
			.collect()
	}

	pub(crate) fn lb(&self) -> Coeff {
		self.lb
	}

	pub(crate) fn leq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		self.ineq(v, false)
	}

	pub(crate) fn lits(&self) -> usize {
		self.xs.len()
	}

	pub(crate) fn ub(&self) -> Coeff {
		self.ub
	}
}

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

impl IntVarEnc {
	pub(crate) fn add<DB: ClauseDatabase + ?Sized>(
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
		let lb = max(lb.unwrap_or(comp_lb), comp_lb);

		let comp_ub = self.ub() + y.ub();
		let ub = min(ub.unwrap_or(comp_ub), comp_ub);

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

	pub(crate) fn consistent<DB: ClauseDatabase + ?Sized>(&self, db: &mut DB) -> Result {
		match self {
			IntVarEnc::Ord(o) => o.consistent(db),
			IntVarEnc::Bin(b) => b.consistent(db),
			IntVarEnc::Const(_) => Ok(()),
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
	/// Constructs (one or more) IntVar `ys` for linear expression `xs` so that ∑ xs ≦ ∑ ys
	pub(crate) fn from_part<DB: ClauseDatabase + ?Sized>(
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

				let dom = once((0, vec![]))
					.chain(h)
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					.tuple_windows()
					.map(|((prev, _), (coef, lits))| {
						let interval = (prev + 1)..(coef + 1);
						if lits.len() == 1 {
							(interval, Some(lits[0]))
						} else {
							let o = new_named_lit!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								db.add_clause([!lit, o]).unwrap();
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
				let dom = once(&(terms[0].0, PosCoeff::new(0)))
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

	pub(crate) fn lb(&self) -> Coeff {
		match self {
			IntVarEnc::Ord(o) => o.lb(),
			IntVarEnc::Bin(b) => b.lb(),
			IntVarEnc::Const(c) => *c,
			// _ => self.dom().range().unwrap().start - 1,
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

	/// Return number of lits in encoding
	#[cfg(test)]
	pub(crate) fn lits(&self) -> usize {
		match self {
			IntVarEnc::Ord(o) => o.lits(),
			IntVarEnc::Bin(b) => b.lits(),
			IntVarEnc::Const(_) => 0,
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

impl IntVarOrd {
	pub(crate) fn consistency(&self) -> ImplicationChainConstraint {
		ImplicationChainConstraint {
			lits: self.xs.values(..).cloned().collect_vec(),
		}
	}

	pub(crate) fn consistent<DB: ClauseDatabase + ?Sized>(&self, db: &mut DB) -> Result {
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
		once(self.lb()..(self.lb() + 1))
			.chain(self.xs.intervals(..))
			.collect()
	}
	pub(crate) fn from_bounds<DB: ClauseDatabase + ?Sized>(
		db: &mut DB,
		lb: Coeff,
		ub: Coeff,
		lbl: String,
	) -> Self {
		Self::from_dom(db, (lb..=ub).collect_vec().as_slice(), lbl)
	}

	pub(crate) fn from_dom<DB: ClauseDatabase + ?Sized>(
		db: &mut DB,
		dom: &[Coeff],
		lbl: String,
	) -> Self {
		Self::from_syms(
			db,
			dom.iter()
				.tuple_windows()
				.map(|(a, b)| (a + 1)..(b + 1))
				.collect(),
			lbl,
		)
	}

	pub(crate) fn from_syms<DB: ClauseDatabase + ?Sized>(
		db: &mut DB,
		syms: IntervalSet<Coeff>,
		lbl: String,
	) -> Self {
		Self::from_views(db, syms.into_iter(..).map(|c| (c, None)).collect(), lbl)
	}

	pub(crate) fn from_views<DB: ClauseDatabase + ?Sized>(
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
				(v, lit.unwrap_or_else(|| new_named_lit!(db, lbl)))
			})
			.collect::<IntervalMap<_, _>>();
		Self { xs, lbl }
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

	pub(crate) fn geqs(&self) -> Vec<(Range<Coeff>, Vec<Vec<Lit>>)> {
		once((self.lb()..(self.lb() + 1), vec![]))
			.chain(self.xs.iter(..).map(|(v, x)| (v, vec![vec![*x]])))
			.collect()
	}

	pub(crate) fn lb(&self) -> Coeff {
		self.xs.range().unwrap().start - 1
	}

	pub(crate) fn leq(&self, v: Range<Coeff>) -> Vec<Vec<Lit>> {
		let v = v.start + 1; // [x<=v] = [x < v+1]
		if v <= self.lb() {
			vec![vec![]]
		} else if v > self.ub() {
			vec![]
		} else {
			match self.xs.overlap(v).collect_vec()[..] {
				[(_, &x)] => vec![vec![!x]],
				_ => panic!("No or multiples literals at {v:?} for var {self:?}"),
			}
		}
	}

	pub(crate) fn leqs(&self) -> Vec<(Range<Coeff>, Vec<Vec<Lit>>)> {
		self.xs
			.iter(..)
			.map(|(v, &x)| ((v.start - 1)..(v.end - 1), vec![vec![!x]]))
			.chain(once((self.ub()..self.ub() + 1, vec![])))
			.collect()
	}

	#[cfg(test)]
	pub(crate) fn lits(&self) -> usize {
		self.xs.len()
	}

	pub(crate) fn ub(&self) -> Coeff {
		self.xs.range().unwrap().end - 1
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

impl Lin {
	pub(crate) fn lb(&self) -> Coeff {
		self.xs.iter().map(|(c, x)| x.borrow().lb(c)).sum::<i64>()
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
								.filter(|&(j, (_c_j, _x_j))| (i != j))
								.map(|(_j, (c_j, x_j))| {
									x_j.borrow()
										.dom
										.iter()
										.map(|d_j_k| *c_j * *d_j_k)
										.collect_vec()
								})
								.multi_cartesian_product()
								.any(|rs| *c_i * *d_i + rs.into_iter().sum::<i64>() == 0)
							{
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
	pub(crate) fn tern(
		x: Rc<RefCell<IntVar>>,
		y: Rc<RefCell<IntVar>>,
		cmp: LimitComp,
		z: Rc<RefCell<IntVar>>,
	) -> Self {
		Lin {
			xs: vec![(1, x), (1, y), (-1, z)],
			cmp,
		}
	}

	pub(crate) fn ub(&self) -> Coeff {
		self.xs.iter().map(|(c, x)| x.borrow().ub(c)).sum::<i64>()
	}
}

impl Display for Lin {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let disp_x = |x: &(Coeff, Rc<RefCell<IntVar>>)| -> String {
			let (coef, x) = x;
			assert!(coef.abs() == 1);
			let x = x.borrow();

			format!("{x}")
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

impl From<&IntVarBin> for BoolLinExp {
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
			BoolLinExp::default().add_bounded_log_encoding(terms.as_slice(), value.lb, value.ub);
		if GROUND_BINARY_AT_LB {
			lin_exp.add_constant(value.lb)
		} else {
			lin_exp
		}
	}
}

impl From<&IntVarEnc> for BoolLinExp {
	fn from(value: &IntVarEnc) -> Self {
		match value {
			IntVarEnc::Ord(o) => o.into(),
			IntVarEnc::Bin(b) => b.into(),
			&IntVarEnc::Const(c) => c.into(),
		}
	}
}

impl From<&IntVarOrd> for BoolLinExp {
	fn from(value: &IntVarOrd) -> Self {
		let mut acc = value.lb();
		BoolLinExp::default()
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

impl Model {
	pub(crate) fn add_int_var_enc(&mut self, x: IntVarEnc) -> IntVar {
		let var = self.new_var(x.dom().iter(..).map(|d| d.end - 1).collect(), false);
		let _ = self.vars.insert(var.id, x);
		var
	}

	pub(crate) fn encode<DB: ClauseDatabase + ?Sized>(
		&mut self,
		db: &mut DB,
		cutoff: Option<Coeff>,
	) -> Result {
		let mut all_views = FxHashMap::default();
		for con in &self.cons {
			let Lin { xs, cmp } = con;
			assert!(
				con.xs.len() == 3 && con.xs.iter().map(|(c, _)| c).collect_vec() == [&1, &1, &-1]
			);

			for (_, x) in xs {
				let x = x.borrow();
				let _ = self
					.vars
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

	pub(crate) fn new_constant(&mut self, c: Coeff) -> IntVar {
		self.new_var(BTreeSet::from([c]), false)
	}

	pub(crate) fn new_var(&mut self, dom: BTreeSet<Coeff>, add_consistency: bool) -> IntVar {
		self.var_ids += 1;
		IntVar {
			id: self.var_ids,
			dom,
			add_consistency,
			views: FxHashMap::default(),
		}
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
				.collect_vec();
			queue.append(&mut cons);
		}
	}
}

impl Display for Model {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for con in &self.cons {
			writeln!(f, "{con}")?;
		}
		Ok(())
	}
}

impl<'a> TernLeConstraint<'a> {
	fn check(x: Coeff, y: Coeff, cmp: &LimitComp, z: Coeff) -> bool {
		match cmp {
			LimitComp::LessEq => x + y <= z,
			LimitComp::Equal => x + y == z,
		}
	}

	pub(crate) fn is_fixed(&self) -> Result<bool, Unsatisfiable> {
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
	pub(crate) fn new(
		x: &'a IntVarEnc,
		y: &'a IntVarEnc,
		cmp: LimitComp,
		z: &'a IntVarEnc,
	) -> Self {
		Self { x, y, cmp, z }
	}
}

impl Checker for TernLeConstraint<'_> {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result {
		let x = BoolLinExp::from(self.x).value(sol)?;
		let y = BoolLinExp::from(self.y).value(sol)?;
		let z = BoolLinExp::from(self.z).value(sol)?;
		if Self::check(x, y, &self.cmp, z) {
			Ok(())
		} else {
			todo!()
			// Err(CheckError::Fail(format!(
			// 	"Failed constraint {self} since {x}+{y} # {z}"
			// )))
		}
	}
}

impl Display for TernLeConstraint<'_> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} + {} {} {}", self.x, self.y, self.cmp, self.z)
	}
}

impl<DB: ClauseDatabase + ?Sized> Encoder<DB, TernLeConstraint<'_>> for TernLeEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "tern_le_encoder", skip_all, fields(constraint = format!("{} + {} {} {}", tern.x, tern.y, tern.cmp, tern.z)))
	)]
	fn encode(&self, db: &mut DB, tern: &TernLeConstraint) -> Result {
		#[cfg(debug_assertions)]
		{
			const PRINT_TESTCASES: bool = false;
			if PRINT_TESTCASES {
				println!(" // {tern}");
				let x = tern.x.dom().iter(..).map(|iv| iv.end - 1).collect_vec();
				let y = tern.y.dom().iter(..).map(|iv| iv.end - 1).collect_vec();
				let z = tern.z.dom().iter(..).map(|iv| iv.end - 1).collect_vec();
				println!(
					"mod _test_{}_{}_{} {{\n\ttest_int_lin!($encoder, &[{}], &[{}], $cmp, &[{}]);\n}}\n",
					x.iter().join(""),
					y.iter().join(""),
					z.iter().join(""),
					x.iter().join(", "),
					y.iter().join(", "),
					z.iter().join(", "),
				);
			}
		}

		let TernLeConstraint { x, y, cmp, z } = tern;

		match (x, y, z) {
			(IntVarEnc::Const(_), IntVarEnc::Const(_), IntVarEnc::Const(_)) => {
				if tern.check(&|_| unreachable!()).is_ok() {
					Ok(())
				} else {
					Err(Unsatisfiable)
				}
			}
			(IntVarEnc::Const(x_con), IntVarEnc::Const(y_con), IntVarEnc::Bin(z_bin)) => {
				let lhs = *x_con + *y_con;
				match cmp {
					// put z_bin on the left, const on the right
					LimitComp::LessEq => lex_geq_const(
						db,
						z_bin.xs.iter().map(|x| Some(*x)).collect_vec().as_slice(),
						PosCoeff::new(if GROUND_BINARY_AT_LB {
							lhs - z_bin.lb()
						} else {
							lhs
						}),
						z_bin.lits(),
					),
					LimitComp::Equal => self.encode(
						db,
						&TernLeConstraint {
							x: z,
							y: &IntVarEnc::Const(0),
							cmp: cmp.clone(),
							z: &IntVarEnc::Const(lhs),
						},
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

				let rhs = PosCoeff::new(if GROUND_BINARY_AT_LB {
					*z_con - *y_con - x_bin.lb()
				} else {
					*z_con - *y_con
				});
				match cmp {
					LimitComp::LessEq => lex_leq_const(
						db,
						x_bin.xs.iter().map(|x| Some(*x)).collect_vec().as_slice(),
						rhs,
						x_bin.lits(),
					),
					LimitComp::Equal => as_binary(rhs, Some(x_bin.lits() as u32))
						.into_iter()
						.zip(x_bin.xs.iter().copied())
						.try_for_each(|(b, x)| db.add_clause([if b { x } else { !x }])),
				}
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y_const), IntVarEnc::Bin(z_bin))
			| (IntVarEnc::Const(y_const), IntVarEnc::Bin(x_bin), IntVarEnc::Bin(z_bin)) => {
				let x_bin = if matches!(cmp, LimitComp::LessEq) {
					let x_bin = x_bin.add(db, self, *y_const)?;
					x_bin.consistent(db)?;
					x_bin
				} else {
					x_bin.clone()
				};
				log_enc_add_(
					db,
					&x_bin.xs.iter().cloned().map(BoolVal::from).collect_vec(),
					&as_binary(PosCoeff::new(*y_const), Some(x_bin.lits() as u32))
						.into_iter()
						.map(BoolVal::Const)
						.collect_vec(),
					cmp,
					&z_bin.xs.iter().cloned().map(BoolVal::from).collect_vec(),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Bin(y_bin), IntVarEnc::Bin(z_bin)) => {
				// y and z are also bin ~ use adder
				match cmp {
					LimitComp::Equal => log_enc_add(db, &x_bin.xs, &y_bin.xs, cmp, &z_bin.xs),
					LimitComp::LessEq => {
						let xy = x.add(db, self, y, None, Some(z.ub()))?;
						xy.consistent(db)?; // TODO can be removed if grounding is correct
						self.encode(
							db,
							&TernLeConstraint::new(&xy, &IntVarEnc::Const(0), LimitComp::LessEq, z),
						)
					}
				}
			}
			(IntVarEnc::Bin(_), IntVarEnc::Bin(_), _) => {
				// y/y is bin but z is not bin ~ redundantly encode y + z_bin in 0..z # z and z_bin <= z
				// TODO better coupling ;
				let z_bin = x.add(db, self, y, None, Some(z.ub()))?;
				z_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(&z_bin, &IntVarEnc::Const(0), cmp.clone(), z),
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
						&IntVarEnc::Const(0), // TODO maybe - lb
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
				let xy_ord = x.add(db, self, y, None, None)?;
				// TODO why necessary?
				xy_ord.consistent(db)?;

				// TODO `x:O.add(y:O)` does not add clauses yet
				self.encode(db, &TernLeConstraint::new(x, y, cmp.clone(), &xy_ord))?;

				self.encode(
					db,
					&TernLeConstraint::new(&xy_ord, &IntVarEnc::Const(0), cmp.clone(), z),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(c), IntVarEnc::Ord(_))
			| (IntVarEnc::Const(c), IntVarEnc::Bin(x_bin), IntVarEnc::Ord(_)) => {
				let z = z.add(db, self, &IntVarEnc::Const(-c), Some(z.lb()), Some(z.ub()))?;

				// x + c <= z == z-c >= x == /\ (z'<=a -> x<=a)
				for (c_a, z_leq_c_a) in z.leqs() {
					// TODO alt; just propagate by adding lex constraint
					let c_a = if z_leq_c_a.is_empty() {
						c_a.start..(x.ub() + 1)
					} else {
						c_a
					};

					let x_leq_c_a = x_bin.leq(c_a.clone());
					add_clauses_for(db, vec![negate_cnf(z_leq_c_a.clone()), x_leq_c_a])?;
				}
				if cmp == &LimitComp::Equal {
					for (c_a, z_geq_c_a) in z.geqs() {
						let c_a = if z_geq_c_a.is_empty() {
							x.lb()..c_a.end
						} else {
							c_a
						};
						let x_geq_c_a = x_bin.geq(c_a.clone());
						add_clauses_for(db, vec![negate_cnf(z_geq_c_a.clone()), x_geq_c_a])?;
					}
				}
				Ok(())
			}
			(x, y, z) => {
				// couple or constrain x:E + y:E <= z:E
				for (c_a, x_geq_c_a) in x.geqs() {
					for (c_b, y_geq_c_b) in y.geqs() {
						// TODO is the max actually correct/good?
						let c_c =
							(max(c_a.start, c_b.start))..(((c_a.end - 1) + (c_b.end - 1)) + 1);

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
							let c_c = (c_a.start + c_b.start)..(c_a.end - 1 + c_b.end - 1) + 1;

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
				Ok(())
			}
		}
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use std::num::NonZeroI32;

	use iset::{interval_set, IntervalSet};
	use traced_test::test;

	use crate::{
		bool_linear::{BoolLinExp, LimitComp},
		helpers::tests::{assert_solutions, expect_file, make_valuation},
		integer::{IntVarBin, IntVarEnc, IntVarOrd, TernLeConstraint, TernLeEncoder},
		ClauseDatabase, Cnf, Coeff, Encoder, Lit, Var, VarRange,
	};

	#[test]
	fn bin_geq_2_test() {
		let mut cnf = Cnf::default();
		let x = IntVarBin::from_bounds(&mut cnf, 0, 12, "x".to_owned());
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &IntVarEnc::Bin(x),
					y: &IntVarEnc::Const(0),
					cmp: LimitComp::LessEq,
					z: &IntVarEnc::Const(6),
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_geq_2_test.sol"],
		);
	}

	#[test]
	fn bin_le_bin_test() {
		let mut cnf = Cnf::default();
		let n = 5;
		let lb = 0;
		let ub = ((2_i32.pow(n)) - 1) as Coeff;

		let (x, y, z) = (
			get_bin_x(&mut cnf, lb, ub, true, "x".to_owned()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			get_bin_x(&mut cnf, lb, ub, true, "z".to_owned()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					// cmp: LimitComp::Equal,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_le_bin_test.sol"],
		);
	}

	#[test]
	fn bin_le_test() {
		let mut cnf = Cnf::default();
		let n = 4;
		let lb = 0;
		let ub = ((2_i32.pow(n)) - 1) as Coeff;

		let (x, y, z) = (
			get_bin_x(&mut cnf, lb, ub, true, "x".to_owned()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			IntVarEnc::Const(14),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					// cmp: LimitComp::Equal,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["int/constrain/bin_le_test.sol"]);
	}

	#[test]
	fn bin_plus_bin_eq_bin_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_bin_x(&mut cnf, 0, 2, true, "x".to_owned()),
			get_bin_x(&mut cnf, 0, 3, true, "y".to_owned()),
			get_bin_x(&mut cnf, 0, 5, true, "z".to_owned()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::Equal,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_plus_bin_eq_bin_test.sol"],
		);
	}

	#[test]
	fn bin_plus_bin_le_bin_test() {
		let mut cnf = Cnf::default();
		let n = 2;
		let (x, y, z) = (
			get_bin_x(
				&mut cnf,
				0,
				((2_i32.pow(n)) - 1) as Coeff,
				true,
				"x".to_owned(),
			),
			get_bin_x(
				&mut cnf,
				0,
				((2_i32.pow(n)) - 1) as Coeff,
				true,
				"y".to_owned(),
			),
			get_bin_x(
				&mut cnf,
				0,
				((2_i32.pow(n + 1)) - 2) as Coeff,
				true,
				"z".to_owned(),
			),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_plus_bin_le_bin_test.sol"],
		);
	}

	#[test]
	fn constant_test() {
		let c = IntVarEnc::Const(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(6..7), Vec::<Vec<_>>::new());
		assert_eq!(c.geq(45..46), vec![vec![]]);
	}

	fn get_bin_x<DB: ClauseDatabase + ?Sized>(
		db: &mut DB,
		lb: Coeff,
		ub: Coeff,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc {
		let x = IntVarBin::from_bounds(db, lb, ub, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}

	fn get_ord_x<DB: ClauseDatabase + ?Sized>(
		db: &mut DB,
		dom: IntervalSet<Coeff>,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc {
		let x = IntVarOrd::from_syms(db, dom, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Ord(x)
	}

	#[test]
	fn ord_geq_test() {
		let mut cnf = Cnf::default();
		let x = get_ord_x(
			&mut cnf,
			interval_set!(3..5, 5..7, 7..11),
			true,
			"x".to_owned(),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);

		assert_eq!(x.lits(), 3);
		assert_eq!(x.lb(), 2);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(6..7), vec![vec![Lit(NonZeroI32::new(2).unwrap())]]);
		assert_eq!(x.geq(4..7), vec![vec![Lit(NonZeroI32::new(2).unwrap())]]);

		let x_lin = BoolLinExp::from(&x);
		assert!(x_lin.value(&make_valuation(&[1, -2, 3])).is_err());
		assert!(x_lin.value(&make_valuation(&[-1, 2, -3])).is_err());
		assert_eq!(x_lin.value(&make_valuation(&[-1, -2, -3])), Ok(2));
		assert_eq!(x_lin.value(&make_valuation(&[1, -2, -3])), Ok(4));
		assert_eq!(x_lin.value(&make_valuation(&[1, 2, -3])), Ok(6));
		assert_eq!(x_lin.value(&make_valuation(&[1, 2, 3])), Ok(10));

		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &IntVarEnc::Const(0),
					cmp: LimitComp::LessEq,
					z: &IntVarEnc::Const(6),
				},
			)
			.unwrap();
		assert_solutions(&cnf, vars, &expect_file!["int/constrain/ord_geq_test.sol"])
	}

	#[test]
	fn ord_le_bin_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_ord_x(&mut cnf, interval_set!(1..2, 2..7), true, "x".to_owned()),
			// TODO 'gapped' in interval_set:
			// get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
			IntVarEnc::Const(0),
			get_bin_x(&mut cnf, 0, 7, true, "z".to_owned()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/ord_le_bin_test.sol"],
		);
	}

	#[test]
	fn ord_plus_ord_le_bin_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_ord_x(&mut cnf, interval_set!(1..3), true, "x".to_owned()),
			get_ord_x(&mut cnf, interval_set!(1..4), true, "y".to_owned()),
			get_bin_x(&mut cnf, 0, 6, true, "z".to_owned()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/ord_plus_ord_le_bin_test.sol"],
		);
	}

	#[test]
	fn ord_plus_ord_le_ord_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_ord_x(&mut cnf, interval_set!(1..2, 2..7), true, "x".to_owned()),
			get_ord_x(&mut cnf, interval_set!(2..3, 3..5), true, "y".to_owned()),
			get_ord_x(&mut cnf, interval_set!(0..4, 4..11), true, "z".to_owned()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);

		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/ord_plus_ord_le_ord_test.sol"],
		);
	}
}
