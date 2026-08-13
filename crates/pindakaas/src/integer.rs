// The integer variable and its Boolean encodings. Nothing outside their own
// tests reaches these yet; the constraint encoding that uses them is the next
// change.
#[allow(
	dead_code,
	reason = "used once the integer constraint encoding is reachable from the pseudo-Boolean entry point"
)]
pub(crate) mod var;

use std::{
	cmp::{max, min},
	fmt::{self, Display},
	iter::once,
	ops::Bound,
};

use itertools::Itertools;
use rangelist::{IntervalIterator, RangeList};

use crate::{
	bool_linear::{BoolLinExp, LimitComp, PosCoeff},
	helpers::{as_binary, bit, new_named_lit},
	integer::var::BinEnc,
	propositional_logic::{Formula, TseitinEncoder},
	BoolVal, Checker, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Lit, Result,
	Unsatisfiable, Valuation,
};

const ENCODE_REDUNDANT_X_O_Y_O_Z_B: bool = true;
pub(crate) const GROUND_BINARY_AT_LB: bool = false;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Consistency {
	#[default]
	None,
	Bounds,
	Domain,
}

pub(crate) struct ImplicationChainConstraint {
	lits: Vec<Lit>,
}

#[derive(Default)]
pub(crate) struct ImplicationChainEncoder {}

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
	pub(crate) dom: RangeList<Coeff>,
	pub(crate) xs: Vec<Lit>,
	pub(crate) lbl: String,
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

pub(crate) fn display_dom(dom: &RangeList<Coeff>) -> String {
	const ELIPSIZE: usize = 8;
	let card = dom.card().unwrap();
	let lb = *dom.min().unwrap();
	let ub = *dom.max().unwrap();
	if card > ELIPSIZE && dom.iter().len() == 1 {
		format!("{}..{}", lb, ub)
	} else if card > ELIPSIZE {
		format!(
			"{{{},..,{ub}}} ({}|{})",
			dom.iter().flatten().take(ELIPSIZE).join(","),
			card,
			BinEnc::required_bits(if GROUND_BINARY_AT_LB { ub - lb } else { ub })
		)
	} else {
		format!("{{{}}}", dom.iter().flatten().join(","))
	}
}

/// Uses lexicographic constraint to constrain x:B >= k
#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "lex_geq", skip_all)
)]
pub(crate) fn lex_geq_const<Db>(db: &mut Db, x: &[BoolVal], k: PosCoeff, bits: usize) -> Result
where
	Db: ClauseDatabase + ?Sized,
{
	let k = as_binary(k, Some(bits as u32));
	// For every one bit in k:
	// - either the `x` bit is also one, or
	// - a higher `x` bit is one that was zero in k.
	for i in 0..bits {
		if k[i] {
			db.add_clause((i..bits).filter(|&j| j == i || !k[j]).map(|j| bit(x, j)))?;
		}
	}
	Ok(())
}

/// Uses lexicographic constraint to constrain x:B ≦ k
#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "lex_lesseq_const", skip_all)
)]
pub(crate) fn lex_leq_const<Db>(db: &mut Db, x: &[BoolVal], k: PosCoeff, bits: usize) -> Result
where
	Db: ClauseDatabase + ?Sized,
{
	let k = as_binary(k, Some(bits as u32));
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	for i in 0..bits {
		if !k[i] {
			db.add_clause((i..bits).filter(|&j| j == i || k[j]).map(|j| !bit(x, j)))?;
		}
	}
	Ok(())
}

/// Constrains the slice `z`, to be the result of adding `x` to `y`, all encoded
/// using the log encoding.
///
/// TODO: Should this use the IntEncoding::Log input??
pub(crate) fn log_enc_add<Db>(
	db: &mut Db,
	x: &[Lit],
	y: &[Lit],
	cmp: &LimitComp,
	z: &[Lit],
) -> Result
where
	Db: ClauseDatabase + ?Sized,
{
	log_enc_add_(
		db,
		&x.iter().copied().map(BoolVal::from).collect_vec(),
		&y.iter().copied().map(BoolVal::from).collect_vec(),
		cmp,
		&z.iter().copied().map(BoolVal::from).collect_vec(),
	)
}

#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("{x:?} + {y:?} {cmp} {z:?}"))))]
pub(crate) fn log_enc_add_<Db>(
	db: &mut Db,
	x: &[BoolVal],
	y: &[BoolVal],
	cmp: &LimitComp,
	z: &[BoolVal],
) -> Result
where
	Db: ClauseDatabase + ?Sized,
{
	let n = itertools::max([x.len(), y.len(), z.len()]).unwrap();

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

pub(crate) fn ord_plus_ord_le_ord_sparse_dom<I1, I2>(
	a: I1,
	b: I2,
	l: Coeff,
	u: Coeff,
) -> RangeList<Coeff>
where
	I1: IntoIterator<Item = Coeff>,
	I2: IntoIterator<Item = Coeff>,
	I2::IntoIter: Clone,
{
	a.into_iter()
		.cartesian_product(b)
		.filter_map(|(a, b)| {
			if a + b >= l && a + b <= u {
				Some(a + b)
			} else {
				None
			}
		})
		.map(|v| v..=v)
		.collect()
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
		let mut dom_it = value.dom.iter().flatten();
		let _ = dom_it.next();
		BoolLinExp::default()
			.add_chain(
				&dom_it
					.zip_eq(&value.xs)
					.map(|(iv, lit)| {
						let v = iv - acc;
						acc += v;
						(*lit, v)
					})
					.collect_vec(),
			)
			.add_constant(value.lb())
	}
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
	pub(crate) fn _encode<Db>(&mut self, db: &mut Db, ic: &ImplicationChainConstraint) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		for (a, b) in ic.lits.iter().copied().tuple_windows() {
			db.add_clause([!b, a])?;
		}
		Ok(())
	}
}

impl IntVarBin {
	pub(crate) fn add<Db>(&self, db: &mut Db, encoder: &TernLeEncoder, y: Coeff) -> Result<Self>
	where
		Db: ClauseDatabase + ?Sized,
	{
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

	pub(crate) fn consistent<Db>(&self, db: &mut Db) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
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

	fn dom(&self) -> RangeList<Coeff> {
		(self.lb..=self.ub).into()
	}

	// TODO change to with_label or something
	pub(crate) fn from_bounds<Db>(db: &mut Db, lb: Coeff, ub: Coeff, lbl: String) -> Self
	where
		Db: ClauseDatabase + ?Sized,
	{
		Self {
			xs: (0..BinEnc::required_bits(if GROUND_BINARY_AT_LB { ub - lb } else { ub }))
				.map(|_i| new_named_lit!(db, format!("{}^{}", lbl, _i)))
				.collect(),
			lb,
			ub,
			lbl,
		}
	}

	pub(crate) fn geq(&self, v: Coeff) -> Formula<BoolVal> {
		self.ineq(v, true)
	}

	fn ineq(&self, v: Coeff, geq: bool) -> Formula<BoolVal> {
		// TODO could *maybe* be domain lb/ub
		let v = if GROUND_BINARY_AT_LB {
			v - self.lb()
		} else {
			v
		};

		// The range 0..(2^n)-1 covered by the (unsigned) binary representation
		let range_lb = 0;
		let range_ub = BinEnc::largest_in(self.lits() as u32);

		if v <= range_lb {
			Formula::Atom(BoolVal::Const(geq))
		} else if v >= range_ub {
			Formula::Atom(BoolVal::Const(!geq))
		} else {
			// generalized from `lex_leq_const`
			let v = as_binary(PosCoeff::new(v), Some(self.lits() as u32));
			let mut conj = Vec::new();
			for (i, _) in v.iter().enumerate().filter(|(_, &v)| v == geq) {
				let mut disj = Vec::new();
				for (j, _) in v
					.iter()
					.enumerate()
					.skip(i)
					.filter(|&(j, &v)| j == i || v != geq)
				{
					let lit = self.xs[j];
					disj.push(Formula::Atom(BoolVal::Lit(if geq { lit } else { !lit })));
				}
				conj.push(if disj.len() == 1 {
					disj.pop().unwrap()
				} else {
					Formula::Or(disj)
				});
			}
			if conj.len() == 1 {
				conj.pop().unwrap()
			} else {
				Formula::And(conj)
			}
		}
	}

	pub(crate) fn lb(&self) -> Coeff {
		self.lb
	}

	pub(crate) fn leq(&self, v: Coeff) -> Formula<BoolVal> {
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
			display_dom(&self.dom()),
			self.lits()
		)
	}
}

impl IntVarEnc {
	pub(crate) fn add<Db>(
		&self,
		db: &mut Db,
		encoder: &TernLeEncoder,
		y: &IntVarEnc,
		lb: Option<Coeff>,
		ub: Option<Coeff>,
		// cmp: &LimitComp,
		// enc: &'a mut dyn Encoder<Db, TernLeConstraint<'a, Db, C>>,
	) -> Result<IntVarEnc>
	where
		Db: ClauseDatabase + ?Sized,
	{
		let comp_lb = self.lb() + y.lb();
		let lb = max(lb.unwrap_or(comp_lb), comp_lb);

		let comp_ub = self.ub() + y.ub();
		let ub = min(ub.unwrap_or(comp_ub), comp_ub);

		match (self, y) {
			(IntVarEnc::Const(a), IntVarEnc::Const(b)) => Ok(IntVarEnc::Const(*a + *b)),
			// TODO only used in sorters which enforce the constraints later!
			(IntVarEnc::Const(c), x) | (x, IntVarEnc::Const(c)) if (*c == 0) => Ok(x.clone()),
			(IntVarEnc::Ord(x), IntVarEnc::Ord(y)) => Ok(IntVarEnc::Ord(IntVarOrd::from_dom(
				db,
				ord_plus_ord_le_ord_sparse_dom(
					x.dom().iter().flatten(),
					y.dom().iter().flatten(),
					lb,
					ub,
				),
				format!("{}+{}", x.lbl, y.lbl),
			))),
			(IntVarEnc::Ord(x), &IntVarEnc::Const(y))
			| (&IntVarEnc::Const(y), IntVarEnc::Ord(x)) => {
				let dom = x
					.dom
					.iter()
					.map(|r| *r.start() + y..=*r.end() + y)
					.collect();
				Ok(IntVarOrd {
					dom,
					xs: x.xs.clone(),
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

	pub(crate) fn consistent<Db>(&self, db: &mut Db) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
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
	pub(crate) fn dom(&self) -> RangeList<Coeff> {
		match self {
			IntVarEnc::Ord(o) => o.dom(),
			IntVarEnc::Bin(b) => b.dom(),
			&IntVarEnc::Const(c) => (c..=c).into(),
		}
	}

	/// Returns a clause constraining `x>=v`, which is None if true and empty if
	/// false
	pub(crate) fn geq(&self, v: Coeff) -> Formula<BoolVal> {
		match self {
			IntVarEnc::Ord(o) => o.geq(v),
			IntVarEnc::Bin(b) => b.geq(v),
			&IntVarEnc::Const(c) => Formula::Atom(BoolVal::Const(v <= c)),
		}
	}

	pub(crate) fn geqs(&self) -> Vec<(Coeff, Formula<BoolVal>)> {
		match self {
			IntVarEnc::Ord(o) => o.geqs(),
			x => x.dom().iter().flatten().map(|c| (c, x.geq(c))).collect(),
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

	/// Returns cnf constraining `x<=v`, which is empty if true and contains
	/// empty if false
	pub(crate) fn leq(&self, v: Coeff) -> Formula<BoolVal> {
		match self {
			IntVarEnc::Ord(o) => o.leq(v),
			IntVarEnc::Bin(b) => b.leq(v),
			&IntVarEnc::Const(c) => Formula::Atom(BoolVal::Const(v >= c)),
		}
	}

	pub(crate) fn leqs(&self) -> Vec<(Coeff, Formula<BoolVal>)> {
		match self {
			IntVarEnc::Ord(o) => o.leqs(),
			x => x.dom().iter().flatten().map(|c| (c, x.leq(c))).collect(),
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
			lits: self.xs.clone(),
		}
	}

	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		ImplicationChainEncoder::default()._encode(db, &self.consistency())
	}

	pub(crate) fn div(&self, c: Coeff) -> IntVarEnc {
		assert_eq!(c, 2, "Can only divide IntVarOrd by 2");
		let mut last = self.lb() / c;
		let mut xs = Vec::new();
		for (d, &l) in self.dom().iter().flatten().skip(1).zip_eq(&self.xs) {
			let nd = d / c;
			if nd == last {
				continue;
			}
			last = nd;
			xs.push(l);
		}
		let dom = self
			.dom()
			.iter()
			.map(|r| r.start() / c..=r.end() / 2)
			.collect();

		if xs.is_empty() {
			IntVarEnc::Const(self.lb() / c)
		} else {
			IntVarOrd {
				dom,
				xs,
				lbl: self.lbl.clone(),
			}
			.into()
		}
	}

	pub(crate) fn dom(&self) -> RangeList<Coeff> {
		self.dom.clone()
	}

	pub(crate) fn from_bounds<Db>(db: &mut Db, lb: Coeff, ub: Coeff, lbl: String) -> Self
	where
		Db: ClauseDatabase + ?Sized,
	{
		Self::from_dom(db, (lb..=ub).into(), lbl)
	}

	pub(crate) fn from_dom<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		dom: RangeList<Coeff>,
		lbl: String,
	) -> Self {
		let card = dom.card().unwrap();
		Self::from_views(db, dom, vec![None; card - 1], lbl)
	}

	pub(crate) fn from_views<Db>(
		db: &mut Db,
		dom: RangeList<Coeff>,
		views: Vec<Option<Lit>>,
		lbl: String,
	) -> Self
	where
		Db: ClauseDatabase + ?Sized,
	{
		assert!(!dom.is_empty());
		assert_eq!(dom.card().unwrap() - 1, views.len(), "Expecting the same number of views as there are inequalities literals to represent the domain");

		let mut dom_it = dom.iter().flatten();
		// No need for a `<=lb` literal, since it would be `true` and thus redundant.
		let mut _lb = dom_it.next().unwrap();

		let xs = dom_it
			.zip_eq(views)
			.map(|(_v, lit)| {
				#[cfg(any(feature = "tracing", test))]
				let lbl = format!("{lbl}>={}", _v);
				lit.unwrap_or_else(|| new_named_lit!(db, lbl))
			})
			.collect();

		Self { dom, xs, lbl }
	}

	pub(crate) fn geq(&self, v: Coeff) -> Formula<BoolVal> {
		Formula::Atom(if v <= self.lb() {
			BoolVal::Const(true)
		} else if v > self.ub() {
			BoolVal::Const(false)
		} else {
			let pos = self.dom.first_position_bound(&Bound::Included(v)).unwrap() - 1;
			BoolVal::Lit(self.xs[pos])
		})
	}

	pub(crate) fn geqs(&self) -> Vec<(Coeff, Formula<BoolVal>)> {
		self.dom()
			.iter()
			.flatten()
			.zip_eq(
				once(Formula::Atom(BoolVal::Const(true)))
					.chain(self.xs.iter().map(|&l| Formula::Atom(BoolVal::Lit(l)))),
			)
			.collect()
	}

	pub(crate) fn lb(&self) -> Coeff {
		*self.dom.min().unwrap()
	}

	pub(crate) fn leq(&self, v: Coeff) -> Formula<BoolVal> {
		let v = v + 1; // [x<=v] = [x < v+1]
		Formula::Atom(if v <= self.lb() {
			BoolVal::Const(false)
		} else if v > self.ub() {
			BoolVal::Const(true)
		} else {
			let pos = self.dom.first_position_bound(&Bound::Included(v)).unwrap() - 1;
			BoolVal::Lit(!self.xs[pos])
		})
	}

	pub(crate) fn leqs(&self) -> Vec<(Coeff, Formula<BoolVal>)> {
		self.dom()
			.iter()
			.flatten()
			.zip_eq(
				self.xs
					.iter()
					.map(|&l| Formula::Atom(BoolVal::Lit(!l)))
					.chain(once(Formula::Atom(BoolVal::Const(true)))),
			)
			.collect()
	}

	#[cfg(test)]
	pub(crate) fn lits(&self) -> usize {
		self.xs.len()
	}

	pub(crate) fn ub(&self) -> Coeff {
		*self.dom.max().unwrap()
	}
}

impl Display for IntVarOrd {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}:O ∈ {}", self.lbl, display_dom(&self.dom()))
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

impl<Db> Encoder<Db, TernLeConstraint<'_>> for TernLeEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "tern_le_encoder", skip_all, fields(constraint = format!("{} + {} {} {}", tern.x, tern.y, tern.cmp, tern.z)))
	)]
	fn encode(&self, db: &mut Db, tern: &TernLeConstraint) -> Result {
		#[cfg(debug_assertions)]
		{
			const PRINT_TESTCASES: bool = false;
			if PRINT_TESTCASES {
				println!(" // {tern}");
				let x = tern
					.x
					.dom()
					.iter()
					.flatten()
					.map(|v| v.to_string())
					.collect_vec();
				let y = tern
					.y
					.dom()
					.iter()
					.flatten()
					.map(|v| v.to_string())
					.collect_vec();
				let z = tern
					.z
					.dom()
					.iter()
					.flatten()
					.map(|v| v.to_string())
					.collect_vec();
				println!(
					"mod _test_{}_{}_{} {{\n\ttest_int_lin!($encoder, &[{}], &[{}], $cmp, &[{}]);\n}}\n",
					x.clone().join(""),
					y.clone().join(""),
					z.clone().join(""),
					x.join(", "),
					y.join(", "),
					z.join(", "),
				);
			}
		}

		let TernLeConstraint { x, y, cmp, z } = tern;

		match (x, y, z) {
			(IntVarEnc::Const(_), IntVarEnc::Const(_), IntVarEnc::Const(_)) => {
				if tern.check(&|_| unreachable!()).is_ok() {
					Ok(())
				} else {
					db.contradiction()?;
					unreachable!();
				}
			}
			(IntVarEnc::Const(x_con), IntVarEnc::Const(y_con), IntVarEnc::Bin(z_bin)) => {
				let lhs = *x_con + *y_con;
				match cmp {
					// put z_bin on the left, const on the right
					LimitComp::LessEq => lex_geq_const(
						db,
						z_bin
							.xs
							.iter()
							.copied()
							.map(BoolVal::Lit)
							.collect_vec()
							.as_slice(),
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
						x_bin
							.xs
							.iter()
							.copied()
							.map(BoolVal::Lit)
							.collect_vec()
							.as_slice(),
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
				// y/y is bin but z is not bin ~ redundantly encode y + z_bin in 0..z # z and
				// z_bin <= z TODO better coupling ;
				let z_bin = x.add(db, self, y, None, Some(z.ub()))?;
				z_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(&z_bin, &IntVarEnc::Const(0), cmp.clone(), z),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Ord(y_ord), _)
			| (IntVarEnc::Ord(y_ord), IntVarEnc::Bin(x_bin), _) => {
				// y is order and z is bin or const ~ redundant y_bin = y_ord and x_bin + y_bin
				// # z
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
					let c_a = if z_leq_c_a == Formula::Atom(BoolVal::Const(true)) {
						x.ub() + 1
					} else {
						c_a
					};

					let x_leq_c_a = x_bin.leq(c_a);
					TseitinEncoder.encode(db, &Formula::Or(vec![!z_leq_c_a, x_leq_c_a]))?;
				}
				if cmp == &LimitComp::Equal {
					for (c_a, z_geq_c_a) in z.geqs() {
						let x_geq_c_a = x_bin.geq(c_a);
						TseitinEncoder.encode(db, &Formula::Or(vec![!z_geq_c_a, x_geq_c_a]))?;
					}
				}
				Ok(())
			}
			(x, y, z) => {
				// couple or constrain x:E + y:E <= z:E
				for (c_a, x_geq_c_a) in x.geqs() {
					for (c_b, y_geq_c_b) in y.geqs() {
						let z_geq_c_c = z.geq(c_a + c_b);

						TseitinEncoder.encode(
							db,
							&Formula::Or(vec![!x_geq_c_a.clone(), !y_geq_c_b, z_geq_c_c]),
						)?;
					}
				}

				// x<=a /\ y<=b -> z<=a+b
				if cmp == &LimitComp::Equal {
					for (c_a, x_leq_c_a) in x.leqs() {
						for (c_b, y_leq_c_b) in y.leqs() {
							let z_leq_c_c = z.leq(c_a + c_b);

							TseitinEncoder.encode(
								db,
								&Formula::Or(vec![!x_leq_c_a.clone(), !y_leq_c_b, z_leq_c_c]),
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

	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		bool_linear::{BoolLinExp, LimitComp, PosCoeff},
		helpers::tests::{
			all_bin_solutions, assert_solutions, bin_lits, expect_file, make_valuation,
		},
		integer::{
			lex_geq_const, lex_leq_const, IntVarBin, IntVarEnc, IntVarOrd, TernLeConstraint,
			TernLeEncoder,
		},
		propositional_logic::Formula,
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Encoder, Lit, Var, VarRange,
	};

	#[test]
	fn lex_const_bounds_a_binary_encoding() {
		for k in 0..8 {
			for (leq, expected) in [
				(true, (0..=k).collect::<Vec<Coeff>>()),
				(false, (k..8).collect()),
			] {
				let mut cnf = Cnf::default();
				let x = bin_lits(&mut cnf, 3);
				let k = PosCoeff::new(k);
				if leq {
					lex_leq_const(&mut cnf, &x, k, 3).unwrap();
				} else {
					lex_geq_const(&mut cnf, &x, k, 3).unwrap();
				}
				let solutions: Vec<Coeff> = all_bin_solutions(&cnf, &[&x])
					.into_iter()
					.map(|s| s[0])
					.collect();
				assert_eq!(solutions, expected, "{} {k}", if leq { "<=" } else { ">=" });
			}
		}
	}

	#[test]
	fn lex_geq_const_with_a_fixed_zero_bit() {
		// The clause for a one bit of `k` is not satisfied when the matching
		// `x` bit is fixed to zero: it just loses that disjunct and still has
		// to be enforced by the remaining higher bits.
		let mut cnf = Cnf::default();
		let x = vec![
			BoolVal::Lit(cnf.new_lit()),
			BoolVal::Const(false),
			BoolVal::Lit(cnf.new_lit()),
		];
		lex_geq_const(&mut cnf, &x, PosCoeff::new(2), 3).unwrap();

		let solutions: Vec<Coeff> = all_bin_solutions(&cnf, &[&x])
			.into_iter()
			.map(|s| s[0])
			.collect();
		// Representable values are {0, 1, 4, 5}; only 4 and 5 are at least 2.
		assert_eq!(solutions, vec![4, 5]);
	}

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
		assert_eq!(c.geq(6), Formula::Atom(BoolVal::Const(true)));
		assert_eq!(c.geq(45), Formula::Atom(BoolVal::Const(false)));
	}

	fn get_bin_x<Db>(db: &mut Db, lb: Coeff, ub: Coeff, consistent: bool, lbl: String) -> IntVarEnc
	where
		Db: ClauseDatabase + ?Sized,
	{
		let x = IntVarBin::from_bounds(db, lb, ub, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}

	fn get_ord_x<Db>(db: &mut Db, dom: RangeList<Coeff>, consistent: bool, lbl: String) -> IntVarEnc
	where
		Db: ClauseDatabase + ?Sized,
	{
		let x = IntVarOrd::from_dom(db, dom, lbl);
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
			RangeList::from_iter([2..=2, 4..=4, 6..=6, 10..=10]),
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
		assert_eq!(
			x.geq(6),
			Formula::Atom(BoolVal::Lit(Lit(NonZeroI32::new(2).unwrap())))
		);
		assert_eq!(
			x.geq(5),
			Formula::Atom(BoolVal::Lit(Lit(NonZeroI32::new(2).unwrap())))
		);

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
			get_ord_x(
				&mut cnf,
				RangeList::from_iter([0..=0, 1..=1, 6..=6]),
				true,
				"x".to_owned(),
			),
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
			get_ord_x(
				&mut cnf,
				RangeList::from_iter([0..=0, 2..=2]),
				true,
				"x".to_owned(),
			),
			get_ord_x(
				&mut cnf,
				RangeList::from_iter([0..=0, 3..=3]),
				true,
				"y".to_owned(),
			),
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
			get_ord_x(
				&mut cnf,
				RangeList::from_iter([0..=0, 1..=1, 6..=6]),
				true,
				"x".to_owned(),
			),
			get_ord_x(
				&mut cnf,
				RangeList::from_iter([1..=1, 2..=2, 4..=4]),
				true,
				"y".to_owned(),
			),
			get_ord_x(
				&mut cnf,
				RangeList::from_iter([-1..=-1, 3..=3, 10..=10]),
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
			&expect_file!["int/constrain/ord_plus_ord_le_ord_test.sol"],
		);
	}
}
