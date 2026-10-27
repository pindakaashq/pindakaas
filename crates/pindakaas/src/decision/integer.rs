//! Integer decision variables, their Boolean encodings, and the bit-level
//! constraints shared between them.
//!
//! An [`IntVar`] is created with the domain it ranges over and holds whichever
//! Boolean encodings its constraints ask for: order literals for a sequential
//! decomposition, bits for an adder, a one-hot view for an at-most-one group.
//! Each is built on first request rather than up front, and the moment a second
//! appears it is channelled against the first, so that every view agrees on the
//! value. A constraint can therefore read whichever view suits it without
//! committing in advance, and without a second variable to hold the other.
//!
//! Channelling costs clauses in proportion to the size of the domain, so a
//! variable large enough to want a binary encoding is one to keep from
//! acquiring a second view at all.
//!
//! # Literals that already exist
//!
//! A variable can be built on literals already in the formula: a group of
//! pseudo-Boolean terms, a view onto another variable, anything whose structure
//! already says what it says. Every `from_*` and `with_*` method **takes those
//! literals at their word**, emitting nothing to make them mean it — no
//! implication chain for an order encoding, no exactly-one for a direct one, no
//! bounds for a binary one. Where they do not mean it, the encoding built on
//! them is wrong, and nothing will say so.
//!
//! That is the right default because such literals nearly always come from a
//! structure that has constrained them already, and saying it twice costs
//! clauses for nothing. Where it does not hold — most often because some of the
//! literals were freshly made — ask for the clauses with [`IntVar::constrain`].
//!
//! # Views
//!
//! An [`IntVar`] is an affine view `scale·x + offset` of a variable `x`, and
//! arithmetic with a constant gives another view of `x` without a clause or a
//! literal. Every view shares the domain and the encodings of `x`: narrowing a
//! view narrows `x`, and an encoding asked for through a view is created on
//! `x`. Arithmetic panics where the scale, the offset, or a value of the view
//! overflows a coefficient.

use std::{
	cell::RefCell,
	cmp::{max, min},
	fmt::{self, Display},
	iter::once,
	ops::{Add, Bound, Mul, Neg, Sub},
	rc::Rc,
};

use itertools::{Either, Itertools};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::FxHashMap;

use crate::{
	constraint::linear::{Comparator, PosCoeff},
	helpers::{as_binary, bit, div_ceil, div_floor, new_named_lit, new_named_var_range},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Lit, Result, Unsatisfiable, Var, VarRange,
};

/// Bits of `value - min`, least significant first.
///
/// The offset belongs to this view. Constant bits allow shifts and complements
/// without fresh literals.
#[derive(Clone, Debug)]
pub(crate) struct BinaryEncoding {
	x: Literals<BoolVal>,
	min: Coeff,
}

/// The direct encoding of an integer variable.
///
/// One literal per domain value, with exactly one holding. Supplied literals
/// are trusted; newly allocated views are constrained when requested.
#[derive(Clone, Debug)]
pub(crate) struct DirectEncoding {
	x: Literals<Lit>,
}

/// What a variable's existing encodings answer, of the questions
/// [`IntVar`] otherwise answers by creating one.
///
/// A question the domain settles is answered whatever has been encoded, and
/// anything else needs a view that speaks about it: an order view for a bound,
/// a direct view for a value, and either of them for a value at the ends of the
/// domain. Where nothing does, the answer is `None`, and asking [`IntVar`]
/// itself creates what it takes.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{decision::integer::IntVar, BoolVal, Cnf};
///
/// let mut cnf = Cnf::default();
/// let x = IntVar::new(0..=4);
/// // The domain says this much without any encoding.
/// assert!(matches!(x.encoded().at_least(0), Some(BoolVal::Const(true))));
/// assert!(x.encoded().at_least(2).is_none());
///
/// // Asking for it builds the order encoding, which then answers.
/// let _ = x.at_least(&mut cnf, 2)?;
/// assert!(x.encoded().at_least(2).is_some());
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Copy, Debug)]
pub struct EncodedViews<'a>(&'a IntVar);

/// An integer decision variable with Boolean views created on demand, or an
/// affine view `scale·x + offset` of one.
///
/// Cloning shares the variable; it does not copy it. See the [module
/// documentation](self) for views, channelling, and existing-literal
/// contracts.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{decision::integer::IntVar, Cnf};
///
/// let mut cnf = Cnf::default();
/// let x = IntVar::new(0..=4);
/// let y = -x.clone() * 2 + 5;
/// assert_eq!((y.min(), y.max()), (-3, 5));
/// // `y ≥ 0` is `x ≤ 2`, which is one literal of `x`.
/// assert_eq!(y.at_least(&mut cnf, 0)?, x.at_most(&mut cnf, 2)?);
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug)]
pub struct IntVar {
	state: Rc<RefCell<IntVarState>>,
	/// What the variable is multiplied by, which is never zero.
	scale: Coeff,
	/// What is added to the scaled variable.
	offset: Coeff,
}

/// Everything about a variable that can change after it is created.
#[derive(Debug)]
struct IntVarState {
	domain: RangeList<Coeff>,
	/// The name the literals of an encoding are called after. It is only ever
	/// read to name them, so it is not kept at all unless something is
	/// listening.
	#[cfg(any(feature = "tracing", test))]
	label: String,
	/// Whether the encodings are restricted to the domain. The order encoding
	/// is exact by construction unless it has no consistency constraint, so
	/// this only concerns the binary one.
	add_consistency: bool,
	/// Whether the order encoding gets its consistency constraint, which only
	/// the merges of a sorting network do without.
	order_consistency: bool,
	order: Option<OrderEncoding>,
	binary: Option<BinaryEncoding>,
	direct: Option<DirectEncoding>,
	/// How the binary encoding and the direct encoding each stand to the order
	/// encoding they meet through: `None` where nothing ties them yet, and
	/// otherwise how this encoding's value compares with the order encoding's.
	///
	/// A channel need not say the two are the same. One that only bounds this
	/// encoding above carries an upper bound over to it and nothing else, so
	/// what a channel is decides what a constraint on one end reaches at the
	/// other, and which of them can be believed about the value.
	channelled: [Option<Comparator>; 2],
	/// Whether clauses here already say the variable holds a value of its
	/// domain.
	///
	/// It has to be said once and only once. Saying it of any one encoding says
	/// it of every other through the channels between them, so the encoding
	/// that says it is whichever came first, and the rest are told nothing.
	constrained: bool,
	/// The bits of `c·(x − min)` for each coefficient a constraint has scaled
	/// the variable by.
	///
	/// Building one takes a graph of shifts and adders, so it is worth keeping:
	/// a coefficient met again — in this constraint or a later one, by this
	/// encoder or another — costs nothing, and a synthesis shares the steps it
	/// has in common with one already done.
	products: FxHashMap<Coeff, Vec<BoolVal>>,
	/// The encoding the variable's value is read from.
	///
	/// Every other encoding is somewhere between a bound and an equal, so only
	/// this one is known to say what the variable is worth. It is the first
	/// encoding the variable was given, and moves to the binary encoding when
	/// one arrives that is equal to it, that being the cheapest to read.
	lead: Option<Lead>,
}

/// The encoding a variable's value is read from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lead {
	Order,
	Binary,
	Direct,
}

/// The literals of an encoding.
///
/// Fresh literals use a compact range; supplied literals and fixed bits retain
/// their explicit representation.
#[derive(Clone, Debug)]
pub(crate) enum Literals<T> {
	Explicit(Vec<T>),
	Range(VarRange),
}

/// The order encoding of an integer variable.
///
/// There is one literal per domain value except the first, where `x[i]` holds
/// exactly when the variable is at least the `i+1`'th value of the domain. The
/// domain is kept alongside the literals so that a value can be resolved to a
/// literal without consulting the variable it came from.
#[derive(Clone, Debug)]
pub(crate) struct OrderEncoding {
	x: Literals<Lit>,
}

/// The view `x + shift` of a variable.
#[derive(Clone, Debug)]
pub(crate) struct ShiftedVar {
	state: Rc<RefCell<IntVarState>>,
	shift: Coeff,
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
	// `x` is at least `k` exactly where its complement is at most `k`'s.
	let complement = (0..bits).map(|j| !bit(x, j)).collect_vec();
	let ones = if bits >= Coeff::BITS as usize - 1 {
		Coeff::MAX
	} else {
		(1 << bits) - 1
	};
	lex_leq_const(db, &complement, PosCoeff::new(ones - *k), bits)
}

/// Constrain a number held as digits in a mixed radix base to be at most a
/// constant.
///
/// The digits are least significant first, each given as the pair of conditions
/// that it is at least, and that it exceeds, the digit of the constant. The
/// number exceeds the constant exactly where some digit does while every more
/// significant one is at least the constant's. The clauses of the `stated`
/// most significant digits are left out, for a caller that has said them
/// already.
#[cfg_attr(
	any(feature = "tracing", test),
	tracing::instrument(name = "lex_lesseq", skip_all)
)]
pub(crate) fn lex_leq<Db>(db: &mut Db, digits: &[(BoolVal, BoolVal)], stated: usize) -> Result
where
	Db: ClauseDatabase + ?Sized,
{
	let len = digits.len().saturating_sub(stated);
	for (i, &(_, greater)) in digits.iter().enumerate().take(len) {
		if greater == BoolVal::Const(false) {
			// The digit cannot exceed the constant's, so the clause holds.
			continue;
		}
		// Digits can share literals: a later clause, whose tail is part of
		// this one, says the same where its first literal is here or drops.
		let rest = &digits[i + 1..];
		let subsumed = rest.iter().any(|&(_, later)| {
			later == BoolVal::Const(true)
				|| later == greater
				|| rest.iter().any(|&(at_least, _)| at_least == later)
		});
		if !subsumed {
			db.add_clause(once(!greater).chain(rest.iter().map(|&(at_least, _)| !at_least)))?;
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
	// In base two a bit is at least `k`'s where `k`'s is zero, and exceeds it
	// where `k`'s is zero and it is set.
	let pairs = as_binary(k, Some(bits as u32))
		.into_iter()
		.enumerate()
		.map(|(j, set)| {
			let x_j = bit(x, j);
			if set {
				(x_j, BoolVal::Const(false))
			} else {
				(BoolVal::Const(true), x_j)
			}
		})
		.collect_vec();
	lex_leq(db, &pairs, 0)
}

impl BinaryEncoding {
	/// The encoding as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	pub(crate) fn as_weighted(&self) -> (Vec<(Lit, Coeff)>, Coeff) {
		let mut constant = self.min;
		let terms = self
			.x
			.iter()
			.enumerate()
			.filter_map(|(i, b)| {
				let weight = 1 << i;
				match b {
					BoolVal::Lit(l) => Some((l, weight)),
					// A bit that is fixed is worth what it is worth regardless.
					BoolVal::Const(true) => {
						constant += weight;
						None
					}
					BoolVal::Const(false) => None,
				}
			})
			.collect();
		(terms, constant)
	}

	/// The width of the encoding.
	pub(crate) fn bits(&self) -> usize {
		self.x.len()
	}

	/// Restrict the encoding to the values of `domain`.
	///
	/// The lower bound costs nothing when the bits count from it, which is how
	/// an encoding made for a variable is grounded. One taken from literals
	/// that were already there counts from wherever they do, and then it needs
	/// enforcing like any other.
	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		domain: &RangeList<Coeff>,
	) -> Result {
		let bits = self.x.to_vec();
		let floor = *domain.min().unwrap() - self.min;
		if floor > 0 {
			lex_geq_const(db, &bits, PosCoeff::new(floor), self.bits())?;
		}
		let span = *domain.max().unwrap() - self.min;
		lex_leq_const(db, &bits, PosCoeff::new(span), self.bits())?;
		for (below, above) in domain.iter().tuple_windows() {
			for v in (*below.end() + 1)..*above.start() {
				self.encode_neq(db, v)?;
			}
		}
		Ok(())
	}

	/// Forbid the encoding from taking the value `v`.
	pub(crate) fn encode_neq<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db, v: Coeff) -> Result {
		let k = as_binary(PosCoeff::new(v - self.min), Some(self.bits() as u32));
		db.add_clause(
			self.x
				.iter()
				.zip(k)
				.map(|(b, set)| if set { !b } else { b }),
		)
	}

	/// An encoding of bits already built, counting from `min`.
	pub(crate) fn from_bits(bits: Vec<BoolVal>, min: Coeff) -> Self {
		Self {
			x: Literals::Explicit(bits),
			min,
		}
	}

	/// The encoding of a two-valued variable, whose single order literal
	/// already distinguishes both values and so can stand in for every bit
	/// that tells them apart.
	pub(crate) fn from_two_valued(lit: Lit, domain: &RangeList<Coeff>) -> Self {
		let (lb, ub) = (*domain.min().unwrap(), *domain.max().unwrap());
		let x = Literals::Explicit(
			as_binary(PosCoeff::new(ub - lb), None)
				.into_iter()
				.map(|set| {
					if set {
						BoolVal::Lit(lit)
					} else {
						BoolVal::Const(false)
					}
				})
				.collect(),
		);
		Self { x, min: lb }
	}

	/// The largest value `bits` bits can hold, the inverse of
	/// [`Self::required_bits`].
	pub(crate) fn largest_in(bits: u32) -> Coeff {
		// Summed rather than `(1 << bits) - 1`, which overflows at the width of
		// a coefficient where the sum lands exactly on its largest value.
		const TWO: Coeff = 2;
		(0..bits).fold(0, |sum, i| sum + TWO.pow(i))
	}

	/// The `i`'th bit, where bits beyond the encoding's width are zero.
	pub(crate) fn lit_bit(&self, i: usize) -> BoolVal {
		self.x.get(i).unwrap_or(BoolVal::Const(false))
	}

	/// The value the bits count from, which is what all of them being zero
	/// stands for.
	pub(crate) fn min(&self) -> Coeff {
		self.min
	}

	/// Create the bits for `domain`, all of them free.
	pub(crate) fn new<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: &RangeList<Coeff>,
		_label: &str,
	) -> Self {
		let (lb, ub) = (*domain.min().unwrap(), *domain.max().unwrap());
		let x = Literals::Range(new_named_var_range!(
			db,
			Self::required_bits(ub - lb),
			|i| format!("{_label}^{i}")
		));
		Self { x, min: lb }
	}

	/// The number of bits needed to represent `0..=span`.
	pub(crate) fn required_bits(span: Coeff) -> usize {
		debug_assert!(
			span >= 0,
			"a domain cannot span a negative number of values"
		);
		(Coeff::BITS - span.leading_zeros()) as usize
	}

	/// The bits of the encoding, least significant first.
	pub(crate) fn to_vec(&self) -> Vec<BoolVal> {
		self.x.to_vec()
	}

	/// The value represented under an assignment.
	pub(crate) fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		self.min + crate::helpers::binary_value(&self.x.to_vec(), value)
	}
}

impl Add<IntVar> for Coeff {
	type Output = IntVar;

	fn add(self, rhs: IntVar) -> Self::Output {
		rhs + self
	}
}

impl Mul<IntVar> for Coeff {
	type Output = IntVar;

	fn mul(self, rhs: IntVar) -> Self::Output {
		rhs * self
	}
}

impl DirectEncoding {
	/// The encoding as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	///
	/// Exactly one literal holds, so the variable is worth whichever value that
	/// one stands for.
	pub(crate) fn as_weighted(&self, domain: &RangeList<Coeff>) -> (Vec<(Lit, Coeff)>, Coeff) {
		(
			domain
				.iter()
				.flatten()
				.zip(self.x.iter())
				.map(|(v, l)| (l, v))
				.collect(),
			0,
		)
	}

	/// Restrict the encoding to holding for exactly one value.
	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		if self.lit_single().is_some() {
			// A literal and its negation already hold for exactly one value.
			return Ok(());
		}
		db.add_clause(self.x.iter())?;
		for (i, a) in self.x.iter().enumerate() {
			for b in self.x.iter().skip(i + 1) {
				db.add_clause([!a, !b])?;
			}
		}
		Ok(())
	}

	/// Create a direct encoding from the literals it is already on, one for
	/// each value of `domain` in order.
	pub(crate) fn from_literals(domain: &RangeList<Coeff>, x: Vec<Lit>) -> Self {
		assert_eq!(
			x.len(),
			domain.card().unwrap(),
			"a direct encoding has a literal for every value"
		);
		Self {
			x: Literals::Explicit(x),
		}
	}

	/// Values paired with guards for a sequential decomposition.
	///
	/// Each guard holds unless the variable takes that value. The least
	/// contribution has a false guard because its demand is unconditional.
	pub(crate) fn iter<'a>(
		&'a self,
		domain: &'a RangeList<Coeff>,
		geq: bool,
	) -> impl Iterator<Item = (Coeff, BoolVal)> + 'a {
		let step = |(i, (d, l)): (usize, (Coeff, Lit))| {
			(
				d,
				if i == 0 {
					BoolVal::Const(false)
				} else {
					BoolVal::Lit(!l)
				},
			)
		};
		if geq {
			Either::Left(self.walk(domain).enumerate().map(step))
		} else {
			let walk = self.walk(domain).collect_vec();
			Either::Right(walk.into_iter().rev().enumerate().map(step))
		}
	}

	/// Whether the variable takes exactly `v`.
	pub(crate) fn lit_equals(&self, domain: &RangeList<Coeff>, v: Coeff) -> BoolVal {
		match domain.iter().flatten().position(|d| d == v) {
			None => BoolVal::Const(false),
			Some(pos) => BoolVal::Lit(self.x.get(pos).unwrap()),
		}
	}

	/// The literal for the larger of two values, where the literal for the
	/// smaller is its negation.
	pub(crate) fn lit_single(&self) -> Option<Lit> {
		let (a, b) = (self.x.get(0)?, self.x.get(1)?);
		(self.x.len() == 2 && a == !b).then_some(b)
	}

	/// The value represented under an assignment.
	pub(crate) fn value<F: crate::Valuation + ?Sized>(
		&self,
		domain: &RangeList<Coeff>,
		value: &F,
	) -> Coeff {
		domain
			.iter()
			.flatten()
			.zip(self.x.iter())
			.find(|(_, l)| value.value(*l))
			.expect("a direct encoding holds for one of its values")
			.0
	}

	/// Every value of `domain` paired with the literal for taking it.
	pub(crate) fn walk<'a>(
		&'a self,
		domain: &'a RangeList<Coeff>,
	) -> impl Iterator<Item = (Coeff, Lit)> + 'a {
		domain.iter().flatten().zip(self.x.iter())
	}
}

impl EncodedViews<'_> {
	/// Whether the variable is at least `v`, or `None` where no encoding says.
	pub fn at_least(&self, v: Coeff) -> Option<BoolVal> {
		// Mapping a value far outside the view onto the variable can overflow.
		if v <= self.0.min() {
			return Some(BoolVal::Const(true));
		} else if v > self.0.max() {
			return Some(BoolVal::Const(false));
		}
		let (v, negated) = self.0.at_least_of_base(v);
		let lit = self.base_at_least(v)?;
		Some(if negated { !lit } else { lit })
	}

	/// Whether the variable is at most `v`, or `None` where no encoding says.
	pub fn at_most(&self, v: Coeff) -> Option<BoolVal> {
		// `v + 1` overflows at the greatest coefficient.
		if v >= self.0.max() {
			return Some(BoolVal::Const(true));
		}
		self.at_least(v + 1).map(|lit| !lit)
	}

	/// Whether the variable itself is at least `v`, or `None` where no
	/// encoding says.
	fn base_at_least(&self, v: Coeff) -> Option<BoolVal> {
		let state = self.0.state.borrow();
		if v <= *state.domain.min().unwrap() {
			Some(BoolVal::Const(true))
		} else if v > *state.domain.max().unwrap() {
			Some(BoolVal::Const(false))
		} else {
			state
				.order
				.as_ref()
				.map(|order| order.lit_at_least(&state.domain, v))
		}
	}

	/// Whether the variable itself takes `v`, or `None` where no encoding
	/// says.
	fn base_equals(&self, v: Coeff) -> Option<BoolVal> {
		let (min, max) = {
			let state = self.0.state.borrow();
			if !state.domain.contains(&v) {
				return Some(BoolVal::Const(false));
			} else if state.domain.card().unwrap() == 1 {
				return Some(BoolVal::Const(true));
			} else if let Some(direct) = state.direct.as_ref() {
				return Some(direct.lit_equals(&state.domain, v));
			} else if state.order.is_none() {
				return None;
			}
			(*state.domain.min().unwrap(), *state.domain.max().unwrap())
		};
		// Only where the order encoding is the one already there, since
		// otherwise the direct encoding answers in one literal anyway.
		if v == max {
			self.base_at_least(v)
		} else if v == min {
			self.base_at_least(v + 1).map(|lit| !lit)
		} else {
			None
		}
	}

	/// Whether the variable takes `v`, or `None` where no encoding says.
	pub fn equals(&self, v: Coeff) -> Option<BoolVal> {
		if v < self.0.min() || v > self.0.max() {
			return Some(BoolVal::Const(false));
		}
		match self.0.equals_of_base(v) {
			// A value the view steps over is never taken.
			None => Some(BoolVal::Const(false)),
			Some(v) => self.base_equals(v),
		}
	}
}

impl IntVar {
	/// The view `a·self + b` for a nonzero `a`, see the [module
	/// documentation](self) for when it panics. A falling view needs the
	/// variable's order consistency constraint.
	fn affine(&self, a: Coeff, b: Coeff) -> Self {
		debug_assert_ne!(a, 0, "a view scaled by zero is a constant, not a view");
		// See `mapped` for why a falling view needs order consistency.
		debug_assert!(
			a > 0 || self.state.borrow().order_consistency,
			"a falling view of {self} needs its order consistency"
		);
		let (lb, ub) = self.base_ends();
		let checked = || {
			let scale = a.checked_mul(self.scale)?;
			let offset = a.checked_mul(self.offset)?.checked_add(b)?;
			// The ends of the domain bound every value of the view.
			for v in [lb, ub] {
				let _ = scale.checked_mul(v)?.checked_add(offset)?;
			}
			Some((scale, offset))
		};
		let Some((scale, offset)) = checked() else {
			panic!("the view {a}·({self}){b:+} overflows a coefficient");
		};
		Self {
			state: Rc::clone(&self.state),
			scale,
			offset,
		}
	}

	/// The variable as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	///
	/// Read through whichever encoding it has, so that a constraint wanting
	/// literals rather than integers gets the ones already standing for it.
	/// Through a view, each weight is multiplied by its scale.
	pub(crate) fn as_weighted<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<(Vec<(Lit, Coeff)>, Coeff), Unsatisfiable> {
		let encoded = {
			let state = self.state.borrow();
			match (
				state.direct.as_ref(),
				state.order.as_ref(),
				state.binary.as_ref(),
			) {
				(.., Some(bin)) => Some(bin.as_weighted()),
				(Some(dir), ..) => Some(dir.as_weighted(&state.domain)),
				(_, Some(ord), _) => Some(ord.as_weighted(&state.domain)),
				_ => None,
			}
		};
		let (lits, constant) = match encoded {
			Some(weighted) => weighted,
			// Nothing has been asked of it yet. The binary encoding is the one
			// that costs least to make.
			None => self.binary_encoding(db)?.as_weighted(),
		};
		if self.is_base() {
			return Ok((lits, constant));
		}
		let lits = lits
			.into_iter()
			.map(|(lit, weight)| (lit, weight * self.scale))
			.collect();
		Ok((lits, self.through(constant)))
	}

	/// Refuse another encoding for a variable without its order consistency
	/// constraint, since channelling would read its one-sided literals as a
	/// value.
	fn assert_order_consistency(&self, encoding: &str) {
		assert!(
			self.state.borrow().order_consistency,
			"{} has no order consistency constraint, so it cannot take a {encoding} encoding",
			self.label()
		);
	}

	/// Returns a [`BoolVal`] indicating whether the variable is at least `v`.
	///
	/// The answer is a constant where the domain settles it, and otherwise one
	/// literal of the order encoding, which is created if the variable has not
	/// been asked for one before.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when creating or channelling the order encoding
	/// contradicts the database.
	pub fn at_least<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<BoolVal, Unsatisfiable> {
		if let Some(lit) = self.encoded().at_least(v) {
			return Ok(lit);
		}
		let (v, negated) = self.at_least_of_base(v);
		let order = self.order_encoding(db)?;
		let lit = order.lit_at_least(&self.state.borrow().domain, v);
		Ok(if negated { !lit } else { lit })
	}

	/// The value `b` of the variable itself such that `self ≥ v` is `x ≥ b`, or
	/// `¬(x ≥ b)` where the flag is set.
	fn at_least_of_base(&self, v: Coeff) -> (Coeff, bool) {
		if self.scale > 0 {
			(div_ceil(v - self.offset, self.scale), false)
		} else {
			(div_floor(v - self.offset, self.scale) + 1, true)
		}
	}

	/// Returns a [`BoolVal`] indicating whether the variable is at most `v`,
	/// which is whether it fails to reach the value after it.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] under the conditions documented by
	/// [`IntVar::at_least`].
	pub fn at_most<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<BoolVal, Unsatisfiable> {
		// `v + 1` overflows at the greatest coefficient.
		if v >= self.max() {
			return Ok(BoolVal::Const(true));
		}
		Ok(!self.at_least(db, v + 1)?)
	}

	/// The variable the view is on.
	pub(crate) fn base(&self) -> IntVar {
		IntVar {
			state: Rc::clone(&self.state),
			scale: 1,
			offset: 0,
		}
	}

	/// The least and the greatest value of the variable itself.
	fn base_ends(&self) -> (Coeff, Coeff) {
		let state = self.state.borrow();
		(*state.domain.min().unwrap(), *state.domain.max().unwrap())
	}

	/// The label of the variable itself, which its literals are named after.
	fn base_label(&self) -> String {
		#[cfg(any(feature = "tracing", test))]
		return self.state.borrow().label.clone();
		#[cfg(not(any(feature = "tracing", test)))]
		return String::new();
	}

	/// The term `c·self` as `(c·scale, x, c·offset)`: a term over the variable
	/// itself, and a constant.
	pub(crate) fn base_term(&self, c: Coeff) -> (Coeff, IntVar, Coeff) {
		let (Some(scale), Some(offset)) = (c.checked_mul(self.scale), c.checked_mul(self.offset))
		else {
			panic!("the term {c}·({self}) overflows a coefficient");
		};
		(scale, self.base(), offset)
	}

	/// The bits of the binary encoding, least significant first, with `weight`
	/// and `constant` such that the view is `weight·Σ 2ⁱ·bitᵢ + constant`.
	///
	/// A bit is a constant where the domain leaves it no choice. The binary
	/// encoding is created if the variable has not been asked for one before.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when creating, constraining, or channelling the binary
	/// encoding contradicts the database.
	pub(crate) fn binary_bits<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<(Vec<BoolVal>, Coeff, Coeff), Unsatisfiable> {
		let binary = self.binary_encoding(db)?;
		Ok((binary.to_vec(), self.scale, self.through(binary.min())))
	}

	/// The binary encoding of the variable itself, over its own domain,
	/// created if this is the first request for it.
	fn binary_encoding<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result<BinaryEncoding> {
		if let Some(bin) = self.state.borrow().binary.as_ref() {
			return Ok(bin.clone());
		}
		// Take what is needed out of the variable before touching the database,
		// so that no borrow is held while clauses are emitted.
		let (domain, view) = {
			let state = self.state.borrow();
			let view = state
				.order
				.as_ref()
				.and_then(OrderEncoding::lit_single)
				.map(|l| BinaryEncoding::from_two_valued(l, &state.domain));
			(state.domain.clone(), view)
		};

		// A two-valued variable needs no channelling: its order literal is
		// already the whole of its binary encoding.
		let derived = view.is_some();
		let bin = match view {
			Some(bin) => bin,
			None => {
				let bin = BinaryEncoding::new(db, &domain, &self.base_label());
				if self.needs_constraining() {
					bin.consistent(db, &domain)?;
					self.state.borrow_mut().constrained = true;
				}
				bin
			}
		};

		// A two-valued variable needs no tying: its order literal is already
		// the whole of its binary encoding.
		let tied = derived.then_some(Comparator::Equal);
		self.install_binary(db, bin.clone(), tied)?;
		Ok(bin)
	}

	/// What the view is worth when every bit of the binary encoding is zero,
	/// whether or not the encoding exists yet.
	pub(crate) fn binary_least(&self) -> Coeff {
		match self.state.borrow().binary.as_ref() {
			Some(bin) => self.through(bin.min()),
			None => self.through(self.base_ends().0),
		}
	}

	/// Returns the number of values in the domain.
	pub fn card(&self) -> usize {
		self.state.borrow().domain.card().unwrap()
	}

	/// Constrain the order and binary encodings to represent the same value.
	///
	/// For each bit, the values it separates form blocks of `2ⁱ` consecutive
	/// values, alternating between the bit being zero and one. Placing the
	/// variable in a block therefore fixes the bit, and conversely the bits of
	/// a value pin down which blocks it lies in, so the two directions come out
	/// of the same clauses. Blocks reaching past the domain fold away, since
	/// their bounds resolve to constants.
	fn channel<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (domain, ord, bin) = {
			let mut state = self.state.borrow_mut();
			match (state.order.as_ref(), state.binary.as_ref()) {
				(Some(ord), Some(bin)) if state.channelled[0] != Some(Comparator::Equal) => {
					let all = (state.domain.clone(), ord.clone(), bin.clone());
					state.channelled[0] = Some(Comparator::Equal);
					all
				}
				_ => return Ok(()),
			}
		};
		for i in 0..bin.bits() {
			let width = 1 << i;
			for k in 0..(1 << (bin.bits() - i)) {
				let below = bin.min() + width * k;
				db.add_clause([
					ord.lit_at_most(&domain, below - 1),
					ord.lit_at_least(&domain, below + width),
					if k % 2 == 0 {
						!bin.lit_bit(i)
					} else {
						bin.lit_bit(i)
					},
				])?;
			}
		}
		Ok(())
	}

	/// Constrain the order and direct encodings to represent the same value.
	///
	/// Taking a value means reaching it, and reaching a value without reaching
	/// the next is taking it. Those two are the whole of it, and they are one
	/// clause each per value.
	fn channel_direct<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (ord, dir, domain) = {
			let mut state = self.state.borrow_mut();
			match (state.order.as_ref(), state.direct.as_ref()) {
				(Some(ord), Some(dir)) if state.channelled[1] != Some(Comparator::Equal) => {
					let all = (ord.clone(), dir.clone(), state.domain.clone());
					state.channelled[1] = Some(Comparator::Equal);
					all
				}
				_ => return Ok(()),
			}
		};
		let mut walk = dir.walk(&domain).peekable();
		while let Some((v, takes)) = walk.next() {
			let (takes, reaches) = (BoolVal::Lit(takes), ord.lit_at_least(&domain, v));
			let beyond = walk.peek().map_or(BoolVal::Const(false), |&(n, _)| {
				ord.lit_at_least(&domain, n)
			});
			db.add_clause([!takes, reaches])?;
			db.add_clause([!takes, !beyond])?;
			db.add_clause([!reaches, beyond, takes])?;
		}
		Ok(())
	}

	/// Check that bits given for this variable can hold its domain and no more.
	fn check_bits(&self, bits: &[BoolVal], min: Coeff) {
		let domain = &self.state.borrow().domain;
		assert!(
			min <= *domain.min().unwrap(),
			"a binary encoding counts up from {min}, which is past the domain it is for"
		);
		assert_eq!(
			bits.len(),
			BinaryEncoding::required_bits(*domain.max().unwrap() - min),
			"a binary encoding has the bits its domain needs and no more"
		);
	}

	/// Add consistency clauses restricting the lead encoding to the domain.
	///
	/// Order uses an implication chain, direct uses quadratic exactly-one
	/// clauses, and binary excludes bounds and holes. Other views inherit this
	/// through equality channels. With no view, no clauses are emitted.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the required consistency clauses contradict the
	/// database.
	pub fn constrain<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (lead, order, direct, binary, domain) = {
			let mut state = self.state.borrow_mut();
			if state.constrained {
				return Ok(());
			}
			state.constrained = true;
			(
				state.lead,
				state.order.clone(),
				state.direct.clone(),
				state.binary.clone(),
				state.domain.clone(),
			)
		};
		match lead {
			Some(Lead::Order) => order.unwrap().consistent(db),
			Some(Lead::Direct) => direct.unwrap().consistent(db),
			Some(Lead::Binary) => binary.unwrap().consistent(db, &domain),
			None => Ok(()),
		}
	}

	/// The direct encoding of the variable itself, over its own domain, created
	/// if this is the first request for it.
	fn direct_encoding<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result<DirectEncoding> {
		if let Some(dir) = self.state.borrow().direct.as_ref() {
			return Ok(dir.clone());
		}
		let shared = self
			.state
			.borrow()
			.order
			.as_ref()
			.and_then(OrderEncoding::lit_single);
		if let Some(lit) = shared {
			// The order literal of a two-valued variable already says which
			// value it takes.
			let dir = DirectEncoding::from_literals(&self.state.borrow().domain, vec![!lit, lit]);
			self.install_direct(db, dir.clone(), Some(Comparator::Equal))?;
			return Ok(dir);
		}
		let domain = self.state.borrow().domain.clone();
		let vals = || domain.iter().flatten();
		debug_assert!(
			vals().count() > 1,
			"a variable with one value is that value, which no literal has to say"
		);
		let dir = if vals().count() == 2 {
			// A literal and its negation hold for exactly one of two values.
			let lit = new_named_lit!(
				db,
				format!("{}={}", self.base_label(), domain.max().unwrap())
			);
			DirectEncoding::from_literals(&domain, vec![!lit, lit])
		} else {
			DirectEncoding {
				x: Literals::Range(new_named_var_range!(db, vals().count(), |i| format!(
					"{}={}",
					self.base_label(),
					vals().nth(i).unwrap()
				))),
			}
		};
		if self.needs_constraining() {
			dir.consistent(db)?;
			self.state.borrow_mut().constrained = true;
		}
		self.install_direct(db, dir.clone(), None)?;
		Ok(dir)
	}

	/// The steps of a sequential decomposition over the direct encoding, which
	/// pin a value where [`IntVar::order_steps`] bounds it.
	pub(crate) fn direct_steps<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		geq: bool,
	) -> Result<Vec<(Coeff, BoolVal)>, Unsatisfiable> {
		let direct = self.direct_encoding(db)?;
		let state = self.state.borrow();
		// Collected, for the reason given on [`IntVar::order_steps`].
		Ok(direct
			.iter(&state.domain, geq == (self.scale > 0))
			.map(|(v, guard)| (self.through(v), guard))
			.collect())
	}

	/// Walks the direct encoding, pairing every value of the domain with a
	/// [`BoolVal`] indicating whether the variable takes it.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when creating or channelling the direct encoding
	/// contradicts the database.
	pub(crate) fn direct_walk<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<impl Iterator<Item = (Coeff, BoolVal)>, Unsatisfiable> {
		if self.card() == 1 {
			return Ok(vec![(self.min(), BoolVal::Const(true))].into_iter());
		}
		let direct = self.direct_encoding(db)?;
		let state = self.state.borrow();
		Ok(direct
			.walk(&state.domain)
			.map(|(v, l)| (self.through(v), BoolVal::Lit(l)))
			.collect_vec()
			.into_iter())
	}

	/// Returns the values the variable can take.
	pub fn domain(&self) -> RangeList<Coeff> {
		let state = self.state.borrow();
		if self.is_base() {
			return state.domain.clone();
		}
		let mut ranges = if self.scale.abs() == 1 {
			state
				.domain
				.iter()
				.map(|range| {
					let (a, b) = (self.through(*range.start()), self.through(*range.end()));
					min(a, b)..=max(a, b)
				})
				.collect_vec()
		} else {
			// A scale past one spaces the values out, so each is its own range.
			state
				.domain
				.iter()
				.flatten()
				.map(|v| self.through(v)..=self.through(v))
				.collect_vec()
		};
		if self.scale < 0 {
			// A view that falls runs the values the other way round.
			ranges.reverse();
		}
		RangeList::from_sorted_ranges(ranges)
	}

	/// What the variable's existing encodings answer, without creating one.
	pub fn encoded(&self) -> EncodedViews<'_> {
		EncodedViews(self)
	}

	/// Automatic domain constraints for newly created views.
	///
	/// Enabled by [`Self::new`]. Disabling it skips standalone binary and
	/// direct consistency clauses, but not the consistency constraint of an
	/// order encoding the library creates. Set this
	/// before requesting a view: it does not retrofit existing views. Use
	/// [`Self::constrain`] to constrain supplied literals. The `from_*`
	/// constructors disable it because their literals are assumed to be
	/// constrained already.
	pub fn enforce_consistency(self, enforce: bool) -> Self {
		debug_assert!(
			!self.has_binary_encoding(),
			"the binary encoding of {} is already made, so this would say nothing",
			self.label()
		);
		self.state.borrow_mut().add_consistency = enforce;
		self
	}

	/// Whether the variable takes `v`, as a literal or settled constant.
	///
	/// An existing order view answers at domain endpoints. Otherwise a direct
	/// view is created if needed; channelling costs clauses proportional to the
	/// domain size.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when creating or channelling the required encoding
	/// contradicts the database.
	pub fn equals<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<BoolVal, Unsatisfiable> {
		if let Some(lit) = self.encoded().equals(v) {
			return Ok(lit);
		}
		let v = self
			.equals_of_base(v)
			.expect("a value the view steps over is settled by the domain");
		let direct = self.direct_encoding(db)?;
		let state = self.state.borrow();
		Ok(direct.lit_equals(&state.domain, v))
	}

	/// The value of the variable itself that `self = v` asks about, or `None`
	/// where the view steps over `v`.
	fn equals_of_base(&self, v: Coeff) -> Option<Coeff> {
		let v = v - self.offset;
		(v % self.scale == 0).then(|| v / self.scale)
	}

	/// A variable on existing bits of `value - min`, least significant first.
	///
	/// `min` must not exceed the domain minimum; use exactly enough bits to
	/// represent `domain.max() - min`. Bits may be constants and must already
	/// respect domain bounds and holes. Use [`Self::constrain`] to enforce
	/// them.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when channelling this view to an existing encoding
	/// contradicts the database.
	pub fn from_binary_encoding<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: impl Into<RangeList<Coeff>>,
		bits: &[BoolVal],
		min: Coeff,
	) -> Result<Self, Unsatisfiable> {
		let x = Self::new(domain).enforce_consistency(false);
		x.check_bits(bits, min);
		let binary = BinaryEncoding::from_bits(bits.to_vec(), min);
		x.install_binary(db, binary, None)?;
		Ok(x)
	}

	/// Creates a variable held in a direct encoding on literals that already
	/// exist.
	///
	/// There is one literal per value of `domain`, in order, and `literals[i]`
	/// must hold exactly when the variable takes the `i`'th of them — which
	/// means exactly one of them holding. That is taken on trust and not
	/// emitted; see [`IntVar::constrain`] where it needs saying, though it is
	/// worth avoiding, the clauses for it being quadratic in the domain.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when channelling this view to an existing encoding
	/// contradicts the database.
	pub fn from_direct_encoding<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: impl Into<RangeList<Coeff>>,
		literals: &[Lit],
	) -> Result<Self, Unsatisfiable> {
		let x = Self::new(domain).enforce_consistency(false);
		let direct = DirectEncoding::from_literals(&x.state.borrow().domain, literals.to_vec());
		x.install_direct(db, direct, None)?;
		Ok(x)
	}

	/// Construct a variable from `(value, takes_value)` pairs.
	///
	/// A constant true fixes the domain; constant false entries are dropped.
	/// Literals are trusted as in [`Self::from_direct_encoding`]. The pairs may
	/// come in any order.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the walk contains no possible value or its
	/// literals cannot be channelled to an existing encoding.
	///
	/// # Panics
	///
	/// When a value is given more than one literal. Distinct literals worth
	/// the same, such as choices of equal weight, are not a direct encoding.
	pub fn from_direct_walk<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		walk: impl IntoIterator<Item = (Coeff, BoolVal)>,
	) -> Result<Self, Unsatisfiable> {
		let mut pairs = Vec::new();
		for (v, takes) in walk {
			match takes {
				BoolVal::Const(true) => return Ok(Self::new(v..=v)),
				BoolVal::Const(false) => {}
				BoolVal::Lit(l) => pairs.push((v, l)),
			}
		}
		if pairs.is_empty() {
			db.contradiction()?;
		}
		pairs.sort_by_key(|&(v, _)| v);
		if let Some(w) = pairs.windows(2).find(|w| w[0].0 == w[1].0) {
			panic!(
				"a direct walk has one literal per value, but {} has more",
				w[0].0
			);
		}
		let (values, literals): (Vec<_>, Vec<_>) = pairs.into_iter().unzip();
		let domain = RangeList::from_sorted_elements(values);
		Self::from_direct_encoding(db, domain, &literals)
	}

	/// Creates a variable held in an order encoding on literals that already
	/// exist.
	///
	/// There is one literal per value of `domain` beyond the first, in order,
	/// and `literals[i]` must hold exactly when the variable has reached the
	/// `i + 1`'th of them — which means each of them implying the one before.
	/// That chain is taken on trust and not emitted; see [`IntVar::constrain`]
	/// where it needs saying.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when channelling this view to an existing encoding
	/// contradicts the database.
	pub fn from_order_encoding<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: impl Into<RangeList<Coeff>>,
		literals: &[Lit],
	) -> Result<Self, Unsatisfiable> {
		let x = Self::new(domain).enforce_consistency(false);
		let order = {
			let state = x.state.borrow();
			OrderEncoding::from_literals(&state.domain, literals.to_vec())
		};
		x.install_order(db, order, [None; 2])?;
		Ok(x)
	}

	/// Creates a variable from what its order encoding says value by value.
	///
	/// Each pair is a value and whether the variable reaches it, least value
	/// first. A settled pair is domain rather than encoding: one that always
	/// holds puts every value below it out of reach, one that never holds does
	/// the same for it and everything above. A view onto another variable's
	/// literals can therefore be taken as it comes, untrimmed.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the walk contains no reachable value or its
	/// literals cannot be channelled to an existing encoding.
	pub fn from_order_walk<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		walk: impl IntoIterator<Item = (Coeff, BoolVal)>,
	) -> Result<Self, Unsatisfiable> {
		let (mut values, mut literals) = (Vec::new(), Vec::new());
		for (v, reaches) in walk {
			match reaches {
				BoolVal::Const(true) => {
					values.clear();
					literals.clear();
					values.push(v);
				}
				BoolVal::Const(false) => break,
				BoolVal::Lit(l) => {
					debug_assert!(
						!values.is_empty(),
						"a walk starts at the least value, which is always reached"
					);
					values.push(v);
					literals.push(l);
				}
			}
		}
		if values.is_empty() {
			db.contradiction()?;
		}
		let domain = RangeList::from_elements(values);
		Self::from_order_encoding(db, domain, &literals)
	}

	/// The variable `⌊x / 2⌋`, which reaches `w` exactly when `x` reaches
	/// `2·w`.
	///
	/// Its literals are `x`'s, every other one, so halving costs nothing.
	pub(crate) fn halved<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		x: &IntVar,
	) -> Result<Self, Unsatisfiable> {
		let walk = (0..=(x.max() / 2))
			.map(|w| Ok((w, x.at_least(db, 2 * w)?)))
			.collect::<Result<Vec<_>, Unsatisfiable>>()?;
		Ok(Self::from_order_walk(db, walk)?
			.inherit_order_consistency(x)
			.with_label(format_args!("{}/2", x.label())))
	}

	/// Reports whether the variable has a binary encoding.
	pub fn has_binary_encoding(&self) -> bool {
		self.state.borrow().binary.is_some()
	}

	/// Whether a direct encoding exists.
	pub fn has_direct_encoding(&self) -> bool {
		self.state.borrow().direct.is_some()
	}

	/// Reports whether the variable has an order encoding.
	pub fn has_order_encoding(&self) -> bool {
		self.state.borrow().order.is_some()
	}

	/// A view on the literals of `x`, which has no order consistency
	/// constraint where `x` has none.
	pub(crate) fn inherit_order_consistency(self, x: &IntVar) -> Self {
		let order_consistency = x.state.borrow().order_consistency;
		self.state.borrow_mut().order_consistency &= order_consistency;
		self
	}

	/// Give the variable a binary encoding it does not have yet.
	///
	/// See [`IntVar::with_order_encoding`] for `already_channelled`.
	fn install_binary<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		binary: BinaryEncoding,
		already_channelled: Option<Comparator>,
	) -> Result {
		self.assert_order_consistency("binary");
		{
			let mut state = self.state.borrow_mut();
			debug_assert!(
				state.binary.is_none(),
				"{} is already binary encoded",
				self.label()
			);
			state.binary = Some(binary);
			state.channelled[0] = already_channelled;
			state.lead = state.lead.or(Some(Lead::Binary));
		}
		self.reconcile(db)
	}

	/// Give the variable a direct encoding it does not have yet.
	///
	/// See [`IntVar::with_order_encoding`] for `already_channelled`.
	fn install_direct<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		direct: DirectEncoding,
		already_channelled: Option<Comparator>,
	) -> Result {
		self.assert_order_consistency("direct");
		{
			let mut state = self.state.borrow_mut();
			debug_assert!(
				state.direct.is_none(),
				"{} is already directly encoded",
				self.label()
			);
			state.direct = Some(direct);
			state.channelled[1] = already_channelled;
			state.lead = state.lead.or(Some(Lead::Direct));
		}
		self.reconcile(db)
	}

	/// Give the variable an order encoding it does not have yet.
	///
	/// `already_channelled` says how the binary and the direct encoding are
	/// known to stand to this one already, so that this does not tie again what
	/// is tied.
	fn install_order<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		order: OrderEncoding,
		already_channelled: [Option<Comparator>; 2],
	) -> Result {
		{
			let mut state = self.state.borrow_mut();
			debug_assert!(
				state.order.is_none(),
				"{} is already order encoded",
				self.label()
			);
			state.order = Some(order);
			state.channelled = already_channelled;
			state.lead = state.lead.or(Some(Lead::Order));
		}
		self.reconcile(db)
	}

	/// The view as `scale·(x + shift)`, for a view whose scale divides its
	/// offset, as it does where its least value is zero.
	pub(crate) fn into_scaled_shift(self) -> (Coeff, ShiftedVar) {
		debug_assert_eq!(
			self.offset % self.scale,
			0,
			"{self} is not a multiple of its variable plus a constant"
		);
		let shift = self.offset / self.scale;
		(
			self.scale,
			ShiftedVar {
				state: self.state,
				shift,
			},
		)
	}

	/// Whether `other` is the same view of the same variable.
	pub(crate) fn is(&self, other: &IntVar) -> bool {
		Rc::ptr_eq(&self.state, &other.state)
			&& self.scale == other.scale
			&& self.offset == other.offset
	}

	/// Whether this handle is the variable itself rather than a view of it.
	fn is_base(&self) -> bool {
		self.scale == 1 && self.offset == 0
	}

	/// Whether [`IntTernaryEncoder`] reads this variable on its direct
	/// literals, which it does only when it has no order encoding: an order
	/// literal says a bound in one literal, and guards in fewer clauses.
	///
	/// [`IntTernaryEncoder`]: crate::constraint::int_ternary::IntTernaryEncoder
	pub(crate) fn is_read_directly(&self) -> bool {
		self.has_direct_encoding() && !self.has_order_encoding()
	}

	/// The label of the variable, which is empty unless tracing is enabled —
	/// nothing else has a use for one, so nothing else pays to store it. A
	/// view adds its arithmetic, as in `2·x-3`. Use the [`Display`]
	/// implementation to name a variable in a message, which falls back to its
	/// address.
	pub fn label(&self) -> String {
		match self.base_label() {
			label if label.is_empty() => label,
			label => self.view_of(&label),
		}
	}

	/// The variable `f(x)` on the order literals of `x`, with `x` held to the
	/// values that `f` maps to at most `max`, or `None` where `f` neither rises
	/// nor falls over the domain of `x`.
	///
	/// It reaches an image where `x` reaches the first value mapping to it, or
	/// for a falling `f`, where `x` stays at most the last such value.
	///
	/// # Panics
	///
	/// When a falling `f` maps a value past `max`: only a rising `f` is
	/// bounded.
	pub(crate) fn mapped<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		x: &IntVar,
		f: impl Fn(Coeff) -> Coeff,
		max: Coeff,
	) -> Result<Option<Self>, Unsatisfiable> {
		let values = x.domain().iter().flatten().collect_vec();
		let images = values.iter().map(|&v| f(v)).collect_vec();
		let rising = images.iter().tuple_windows().all(|(a, b)| a <= b);
		if !rising && !images.iter().tuple_windows().all(|(a, b)| a >= b) {
			return Ok(None);
		}
		// A falling view negates the literals of `x`, which turns a literal
		// that can hold spuriously into one that can fail to.
		assert!(
			rising || x.state.borrow().order_consistency,
			"a falling view of {x} needs its order consistency"
		);
		if let Some(i) = images.iter().position(|&w| w > max) {
			assert!(rising, "only a rising view is bounded");
			let beyond = x.at_least(db, values[i])?;
			db.add_clause([!beyond])?;
		}
		let mut walk: Vec<(Coeff, BoolVal)> = Vec::with_capacity(values.len());
		for i in 0..values.len() {
			let i = if rising { i } else { values.len() - 1 - i };
			if images[i] > max {
				break;
			} else if walk.last().is_some_and(|&(w, _)| w == images[i]) {
				continue;
			}
			let reaches = if rising {
				x.at_least(db, values[i])?
			} else {
				x.at_most(db, values[i])?
			};
			walk.push((images[i], reaches));
		}
		// A view reads the literals of `x`, and so their order consistency.
		Ok(Some(
			Self::from_order_walk(db, walk)?.inherit_order_consistency(x),
		))
	}

	/// Returns the greatest value the variable can take.
	pub fn max(&self) -> Coeff {
		let (a, b) = self.through_ends();
		max(a, b)
	}

	/// Returns the least value the variable can take.
	pub fn min(&self) -> Coeff {
		let (a, b) = self.through_ends();
		min(a, b)
	}

	/// The view `min + max − x`, which counts the same domain from the other
	/// end.
	pub(crate) fn mirrored(&self) -> IntVar {
		-self.clone() + (self.min() + self.max())
	}

	/// Drop the values of the variable itself outside `min..=max`, with `None`
	/// for a side without a bound, reporting whether any went.
	///
	/// Order and direct literals of a dropped value are fixed by a unit clause
	/// and leave the variable, so nothing walks them again. A variable with a
	/// binary encoding is left as it is, since its bits count from the domain
	/// minimum.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when no value is left, or when a unit clause
	/// contradicts the database.
	fn narrow<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		min: Option<Coeff>,
		max: Option<Coeff>,
	) -> Result<bool, Unsatisfiable> {
		let mut state = self.state.borrow_mut();
		let state = &mut *state;
		let (lb, ub) = (*state.domain.min().unwrap(), *state.domain.max().unwrap());
		let (min, max) = (min.map_or(lb, |v| v.max(lb)), max.map_or(ub, |v| v.min(ub)));
		if min > ub || max < lb {
			// No value is left, which the database is told as well as the
			// caller.
			db.contradiction()?;
			return Err(Unsatisfiable);
		} else if (min == lb && max == ub) || state.binary.is_some() {
			return Ok(false);
		}
		let before = state.domain.clone();
		state.domain.tighten_min(min);
		let below = before.card().unwrap() - state.domain.card().unwrap();
		state.domain.tighten_max(max);
		let above = before.card().unwrap() - below - state.domain.card().unwrap();
		let mut units = Vec::new();
		if let Some(direct) = state.direct.as_mut() {
			let kept = below..direct.x.len() - above;
			for (i, lit) in direct.x.iter().enumerate() {
				if !kept.contains(&i) {
					db.add_clause([!lit])?;
					units.push(BoolVal::Lit(!lit));
				}
			}
			direct.x.trim(below, above);
		}
		if let Some(order) = state.order.as_mut() {
			// Order literals imply each other, so a unit clause at each end
			// settles the rest, unless the direct encoding shares the literal.
			let (min, max) = (*state.domain.min().unwrap(), *state.domain.max().unwrap());
			for unit in [
				order.lit_at_least(&before, min),
				order.lit_at_most(&before, max),
			] {
				if !units.contains(&unit) {
					db.add_clause([unit])?;
				}
			}
			order.x.trim(below, above);
		}
		Ok(below + above > 0)
	}

	/// Narrow the domain to the values where `self ≥ v` is `holds`, reporting
	/// whether any went.
	fn narrow_at_least<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
		holds: bool,
	) -> Result<bool, Unsatisfiable> {
		// Mapping a value past the view onto the variable can overflow.
		let (min, max) = (self.min(), self.max());
		if v <= min || v > max {
			if (v <= min) == holds {
				return Ok(false);
			}
			db.contradiction()?;
			return Err(Unsatisfiable);
		}
		let (b, negated) = self.at_least_of_base(v);
		if holds != negated {
			self.narrow(db, Some(b), None)
		} else {
			self.narrow(db, None, Some(b - 1))
		}
	}

	/// Whether an encoding being created has to be held to the domain itself.
	///
	/// It does when it is the variable's first, and does not when it is not:
	/// the channel [`Self::reconcile`] is about to build ties it to an encoding
	/// that already holds a value of the domain, whether by clauses here or by
	/// the promise a caller made about its literals.
	fn needs_constraining(&self) -> bool {
		let state = self.state.borrow();
		state.add_consistency
			&& !state.constrained
			&& state.order.is_none()
			&& state.binary.is_none()
			&& state.direct.is_none()
	}

	/// An integer variable with Boolean views created on demand.
	///
	/// New views are constrained to the domain by default; construction emits
	/// no clauses. Encoding may prune the domain before the first view commits
	/// it, so encoding order can affect size and propagation, not solutions.
	///
	/// # Examples
	///
	/// ```rust
	/// use pindakaas::decision::integer::IntVar;
	///
	/// let x = IntVar::new(-2..=7).with_label("x");
	/// assert_eq!(x.min(), -2);
	/// assert_eq!(x.max(), 7);
	/// # Ok::<(), pindakaas::Unsatisfiable>(())
	/// ```
	///
	/// # Panics
	///
	/// Debug builds reject an empty domain. An empty domain is invalid in every
	/// build and causes later domain queries to panic.
	pub fn new(domain: impl Into<RangeList<Coeff>>) -> Self {
		let domain = domain.into();
		debug_assert!(!domain.is_empty(), "an integer variable needs a domain");
		Self {
			state: Rc::new(RefCell::new(IntVarState {
				domain,
				#[cfg(any(feature = "tracing", test))]
				label: String::new(),
				add_consistency: true,
				order_consistency: true,
				order: None,
				binary: None,
				direct: None,
				channelled: [None; 2],
				constrained: false,
				products: FxHashMap::default(),
				lead: None,
			})),
			scale: 1,
			offset: 0,
		}
	}

	/// The order encoding of the variable itself, over its own domain, created
	/// if this is the first request for it.
	fn order_encoding<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result<OrderEncoding> {
		if let Some(ord) = self.state.borrow().order.as_ref() {
			return Ok(ord.clone());
		}
		let domain = self.state.borrow().domain.clone();
		// Only where the direct literals are each other's negation does the
		// second say the variable reaches its larger value without a channel.
		let shared = self
			.state
			.borrow()
			.direct
			.as_ref()
			.and_then(DirectEncoding::lit_single);
		if let Some(lit) = shared {
			let ord = OrderEncoding::from_literals(&domain, vec![lit]);
			self.install_order(db, ord.clone(), [None, Some(Comparator::Equal)])?;
			return Ok(ord);
		}
		let ord = OrderEncoding::new(db, &domain, &self.base_label());
		// Without it the literals describe no value, which only a variable
		// the merges of a sorting network read can do without.
		if self.state.borrow().order_consistency {
			ord.consistent(db)?;
			self.state.borrow_mut().constrained = true;
		}

		self.install_order(db, ord.clone(), [None; 2])?;
		Ok(ord)
	}

	/// The steps of a sequential decomposition over the order encoding.
	///
	/// Each step is a domain value paired with the clause that holds unless the
	/// variable has reached it, so that whatever the constraint then demands
	/// can be disjoined onto that clause.
	pub(crate) fn order_steps<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		geq: bool,
	) -> Result<Vec<(Coeff, BoolVal)>, Unsatisfiable> {
		let order = self.order_encoding(db)?;
		let state = self.state.borrow();
		// Collect before returning: a live borrow would prevent a constraint
		// from mentioning the same variable twice.
		Ok(order
			.iter(&state.domain, geq == (self.scale > 0))
			.map(|(v, guard)| (self.through(v), guard))
			.collect())
	}

	#[cfg(test)]
	/// Walks the order encoding, pairing every value of the domain with
	/// the [`BoolVal`] indicating whether the variable is at least it.
	///
	/// This is [`IntVar::at_least`] over the whole domain, and creates the
	/// order encoding for the same reason.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when creating or channelling the order encoding
	/// contradicts the database.
	pub(crate) fn order_walk<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<impl Iterator<Item = (Coeff, BoolVal)>, Unsatisfiable> {
		let domain = self.domain();
		Ok(domain
			.iter()
			.flatten()
			.map(|v| Ok((v, self.at_least(db, v)?)))
			.collect::<Result<Vec<_>, Unsatisfiable>>()?
			.into_iter())
	}

	/// Whether the variable is better held in binary than in order form.
	///
	/// An encoding it already has settles the question: reaching for the other
	/// one would mean paying to channel between them. Otherwise a variable is
	/// held in binary once its domain grows past `cutoff`, and always in order
	/// form when there is no cutoff.
	pub(crate) fn prefers_binary(&self, cutoff: Option<Coeff>) -> bool {
		let state = self.state.borrow();
		match (state.binary.is_some(), state.order.is_some(), cutoff) {
			(true, _, _) => true,
			(_, true, _) => false,
			(_, _, None) => false,
			// Heuristic: past the cutoff the order literals outnumber the bits.
			(_, _, Some(cutoff)) => state.domain.card().unwrap() as Coeff >= cutoff,
		}
	}

	/// The bits of `c·(x − min)` for a positive `c` where they are built, with
	/// `min` what the binary encoding counts from. Only the variable itself
	/// keeps products, see [`IntVar::base_term`].
	pub(crate) fn product(&self, c: Coeff) -> Option<Vec<BoolVal>> {
		debug_assert!(self.is_base(), "a product is kept by the variable itself");
		let state = self.state.borrow();
		// The bits of `1·x` are the binary encoding itself, so there is nothing
		// to remember separately.
		if c == 1 {
			return state.binary.as_ref().map(BinaryEncoding::to_vec);
		}
		state.products.get(&c).cloned()
	}

	/// Tie together whatever encodings the variable now has, so that every view
	/// of it reads the same value.
	///
	/// The order encoding is the go-between: tying a new encoding to it is
	/// enough for the new one to agree with everything already tied to it. A
	/// variable holding only the other two therefore gains one, which is the
	/// price of reading it two ways at once.
	fn reconcile<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (has_order_encoding, others) = {
			let state = self.state.borrow();
			(
				state.order.is_some(),
				usize::from(state.binary.is_some()) + usize::from(state.direct.is_some()),
			)
		};
		if others + usize::from(has_order_encoding) < 2 {
			return Ok(());
		}
		if !has_order_encoding {
			// Creating it reconciles in turn.
			let _ = self.order_encoding(db)?;
			return Ok(());
		}
		self.channel(db)?;
		self.channel_direct(db)?;
		// Binary is cheapest to read, but can lead only when channelled
		// equally.
		let mut state = self.state.borrow_mut();
		let equal = [
			state.channelled[0] == Some(Comparator::Equal),
			state.channelled[1] == Some(Comparator::Equal),
		];
		if state.binary.is_some() && equal[0] && (state.lead != Some(Lead::Direct) || equal[1]) {
			state.lead = Some(Lead::Binary);
		}
		Ok(())
	}

	#[cfg(test)]
	/// Give the variable a binary encoding, if it has none yet.
	pub(crate) fn require_binary_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result {
		self.binary_encoding(db).map(drop)
	}

	#[cfg(test)]
	/// Give the variable a direct encoding, if it has none yet.
	pub(crate) fn require_direct_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result {
		self.direct_encoding(db).map(drop)
	}

	/// Give the variable an order encoding, if it has none yet.
	pub(crate) fn require_order_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result {
		self.order_encoding(db).map(drop)
	}

	/// Drop the values above `v` from the domain, reporting whether any went.
	///
	/// See [`IntVar::narrow`] for what becomes of the literals.
	pub(crate) fn set_max<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<bool, Unsatisfiable> {
		// `v + 1` overflows at the greatest coefficient.
		if v >= self.max() {
			return Ok(false);
		}
		self.narrow_at_least(db, v + 1, false)
	}

	/// Drop the values below `v` from the domain, reporting whether any went.
	///
	/// See [`IntVar::narrow`] for what becomes of the literals.
	pub(crate) fn set_min<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<bool, Unsatisfiable> {
		self.narrow_at_least(db, v, true)
	}

	/// Remember the bits of `c·(x − min)`, so that the next constraint to scale
	/// the variable by `c` finds them. See [`IntVar::product`].
	pub(crate) fn set_product(&self, c: Coeff, bits: Vec<BoolVal>) {
		debug_assert!(self.is_base(), "a product is kept by the variable itself");
		debug_assert!(c > 1, "the bits of `x` are the encoding itself");
		let _ = self.state.borrow_mut().products.insert(c, bits);
	}

	/// What the view makes of the value `v` of the variable itself.
	fn through(&self, v: Coeff) -> Coeff {
		self.scale * v + self.offset
	}

	/// What the view makes of the least and the greatest value of the
	/// variable itself, in that order.
	fn through_ends(&self) -> (Coeff, Coeff) {
		let (lb, ub) = self.base_ends();
		(self.through(lb), self.through(ub))
	}

	/// The value read from the variable's leading encoding.
	///
	/// Without an encoding, the domain minimum is returned without consulting
	/// the assignment. The variable and its views must belong to the model's
	/// database; querying a value does not create an encoding.
	pub fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		let state = self.state.borrow();
		// Only the leading encoding is known to say what the variable is worth.
		// Another may merely bound it, if what ties them is one-directional.
		let v = match state.lead {
			Some(Lead::Binary) => state.binary.as_ref().unwrap().value(value),
			Some(Lead::Order) => state.order.as_ref().unwrap().value(&state.domain, value),
			Some(Lead::Direct) => state.direct.as_ref().unwrap().value(&state.domain, value),
			None => *state.domain.min().unwrap(),
		};
		self.through(v)
	}

	/// An identity of the variable the view is on, shared by all its views.
	pub(crate) fn variable_id(&self) -> usize {
		Rc::as_ptr(&self.state) as *const () as usize
	}

	/// The name of the view, given the name `base` of the variable itself.
	fn view_of(&self, base: &str) -> String {
		let scale = match self.scale {
			1 => String::new(),
			-1 => "-".to_owned(),
			c => format!("{c}·"),
		};
		let offset = match self.offset {
			0 => String::new(),
			k => format!("{k:+}"),
		};
		format!("{scale}{base}{offset}")
	}

	/// An additional binary view on existing bits.
	///
	/// The binary view must not exist yet; bits and offset follow
	/// [`Self::from_binary_encoding`], with the offset a value of the view.
	/// `already_channelled` records a caller-established relation to the order
	/// view: `Equal` skips that channel; inequalities do not replace equality
	/// and are strengthened. `None` adds missing channels, including an order
	/// view if needed.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the missing channel or binary consistency clauses
	/// contradict the database.
	///
	/// # Panics
	///
	/// When the view is not of the form `x + k`.
	pub fn with_binary_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		bits: &[BoolVal],
		min: Coeff,
		already_channelled: Option<Comparator>,
	) -> Result {
		assert_eq!(
			self.scale, 1,
			"bits can be given only to a view `x + k`, not to {self}"
		);
		let min = min - self.offset;
		self.check_bits(bits, min);
		let binary = BinaryEncoding::from_bits(bits.to_vec(), min);
		self.install_binary(db, binary, already_channelled)
	}

	/// An additional direct view on existing literals.
	///
	/// The variable must not already have this view. Literal semantics and
	/// trust requirements match [`Self::from_direct_encoding`], over the values
	/// of the view in order. See [`Self::with_binary_encoding`] for
	/// `already_channelled`.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the missing channel to an existing view
	/// contradicts the database.
	pub fn with_direct_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		literals: &[Lit],
		already_channelled: Option<Comparator>,
	) -> Result {
		let literals = if self.scale < 0 {
			literals.iter().rev().copied().collect()
		} else {
			literals.to_vec()
		};
		let direct = DirectEncoding::from_literals(&self.state.borrow().domain, literals);
		self.install_direct(db, direct, already_channelled)
	}

	/// Name the variable, so that the literals its encodings create are called
	/// after it.
	///
	/// Nothing is kept and the name is never read unless tracing is enabled,
	/// so a name passed as `format_args!` is never even formatted. Through a
	/// view, it names the variable the view is on.
	pub fn with_label(self, label: impl Display) -> Self {
		#[cfg(any(feature = "tracing", test))]
		{
			self.state.borrow_mut().label = label.to_string();
		}
		#[cfg(not(any(feature = "tracing", test)))]
		let _ = label;
		self
	}

	/// An additional order view on existing literals.
	///
	/// The variable must not already have this view. Literal semantics and
	/// trust requirements match [`Self::from_order_encoding`], over the values
	/// of the view in order. See [`Self::with_binary_encoding`] for
	/// `already_channelled`.
	///
	/// # Errors
	///
	/// [`Unsatisfiable`] when the missing channel to an existing view
	/// contradicts the database.
	pub fn with_order_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		literals: &[Lit],
		already_channelled: Option<Comparator>,
	) -> Result {
		let literals = if self.scale < 0 {
			literals.iter().rev().map(|&l| !l).collect()
		} else {
			literals.to_vec()
		};
		let order = {
			let state = self.state.borrow();
			OrderEncoding::from_literals(&state.domain, literals)
		};
		// The order encoding is the go-between, so what is said of it is said
		// of both pairs.
		self.install_order(db, order, [already_channelled; 2])
	}

	/// Leaves the consistency constraint out of the order encoding, for a sum
	/// that only the merges of a sorting network read.
	///
	/// Each literal then holds whenever the sum reaches its value, and may hold
	/// when it does not. A clause that reads a literal as a condition only
	/// gets stricter for it, but the variable can take no other encoding.
	pub(crate) fn without_order_consistency(self) -> Self {
		debug_assert!(
			!self.has_order_encoding(),
			"the order encoding of {} is already made, so this would say nothing",
			self.label()
		);
		self.state.borrow_mut().order_consistency = false;
		self
	}
}

impl Add<Coeff> for IntVar {
	type Output = IntVar;

	/// The view `x + k`.
	fn add(self, rhs: Coeff) -> Self::Output {
		self.affine(1, rhs)
	}
}

impl Display for IntVar {
	/// The tracing label, or an address-based identifier when unlabelled, with
	/// the view's arithmetic.
	///
	/// The fallback distinguishes shared handles only within a run.
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let base = match self.base_label() {
			label if label.is_empty() => format!("y@{:p}", Rc::as_ptr(&self.state)),
			label => label,
		};
		write!(f, "{}", self.view_of(&base))
	}
}

impl Mul<Coeff> for IntVar {
	type Output = IntVar;

	/// The view `c·x`, or a new constant zero where `c` is zero.
	fn mul(self, rhs: Coeff) -> Self::Output {
		if rhs == 0 {
			IntVar::new(0..=0)
		} else {
			self.affine(rhs, 0)
		}
	}
}

impl Neg for IntVar {
	type Output = IntVar;

	/// The view `-x`.
	fn neg(self) -> Self::Output {
		self.affine(-1, 0)
	}
}

impl Sub<Coeff> for IntVar {
	type Output = IntVar;

	/// The view `x - k`.
	fn sub(self, rhs: Coeff) -> Self::Output {
		let k = rhs
			.checked_neg()
			.unwrap_or_else(|| panic!("the view {self}-{rhs} overflows a coefficient"));
		self.affine(1, k)
	}
}

impl<T: Copy + From<Var>> Literals<T> {
	/// The `i`'th literal, if the encoding is that wide.
	pub(crate) fn get(&self, i: usize) -> Option<T> {
		match self {
			Literals::Explicit(x) => x.get(i).copied(),
			Literals::Range(r) => (i < r.len()).then(|| r.index(i).into()),
		}
	}

	/// The literals, in order.
	pub(crate) fn iter(&self) -> impl Iterator<Item = T> + '_ {
		match self {
			Literals::Explicit(x) => Either::Left(x.iter().copied()),
			Literals::Range(r) => Either::Right(r.map(T::from)),
		}
	}

	/// The number of literals.
	pub(crate) fn len(&self) -> usize {
		match self {
			Literals::Explicit(x) => x.len(),
			Literals::Range(r) => r.len(),
		}
	}

	/// The literals as a slice, materialising a range into one.
	pub(crate) fn to_vec(&self) -> Vec<T> {
		self.iter().collect()
	}

	/// Drop `below` literals from the front and `above` from the back.
	fn trim(&mut self, below: usize, above: usize) {
		let mut x = self.to_vec();
		x.truncate(x.len() - above);
		let _ = x.drain(..below);
		*self = Literals::Explicit(x);
	}
}

impl OrderEncoding {
	/// The encoding as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	///
	/// Each literal is worth the step it takes from the value before it, so the
	/// ones that hold add up to how far past the first value it has reached.
	pub(crate) fn as_weighted(&self, domain: &RangeList<Coeff>) -> (Vec<(Lit, Coeff)>, Coeff) {
		let vals = domain.iter().flatten().collect_vec();
		(
			vals.iter()
				.zip(vals.iter().skip(1))
				.zip(self.x.iter())
				.map(|((below, above), l)| (l, above - below))
				.collect(),
			vals[0],
		)
	}

	/// Constrain consecutive literals, so that the encoding represents a single
	/// value of the domain.
	///
	/// Unlike the bounds and holes of a binary encoding this is not optional:
	/// without it there is no well defined value to speak of, and anything
	/// reading the encoding, channelling included, would be meaningless.
	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		for (prev, next) in self.x.iter().tuple_windows() {
			if prev.var() != next.var() {
				db.add_clause([!next, prev])?;
			}
		}
		Ok(())
	}

	/// An encoding on literals already created, one for each value of `domain`
	/// beyond the first, in order.
	pub(crate) fn from_literals(domain: &RangeList<Coeff>, x: Vec<Lit>) -> Self {
		assert_eq!(
			x.len() + 1,
			domain.card().unwrap(),
			"an order encoding has a literal for every value but the first"
		);
		Self {
			x: Literals::Explicit(x),
		}
	}

	/// Domain thresholds paired with guards for a sequential decomposition.
	///
	/// Each guard holds unless `d` is reached, from below when `geq`, from
	/// above otherwise. The always-reached endpoint has a false guard.
	pub(crate) fn iter<'a>(
		&'a self,
		domain: &'a RangeList<Coeff>,
		geq: bool,
	) -> impl Iterator<Item = (Coeff, BoolVal)> + 'a {
		let vals = domain.iter().flatten();
		if geq {
			Either::Left(vals.map(move |d| (d, self.lit_at_most(domain, d - 1))))
		} else {
			Either::Right(
				vals.rev()
					.map(move |d| (d, self.lit_at_least(domain, d + 1))),
			)
		}
	}

	/// Whether the variable is at least `v`.
	pub(crate) fn lit_at_least(&self, domain: &RangeList<Coeff>, v: Coeff) -> BoolVal {
		if v <= *domain.min().unwrap() {
			BoolVal::Const(true)
		} else if v > *domain.max().unwrap() {
			BoolVal::Const(false)
		} else {
			let pos = domain
				.first_position_bound(&Bound::Included(v))
				.expect("value within the domain bounds has a position");
			BoolVal::Lit(
				self.x
					.get(pos - 1)
					.expect("a domain value has an order literal"),
			)
		}
	}

	/// Whether the variable is at most `v`.
	pub(crate) fn lit_at_most(&self, domain: &RangeList<Coeff>, v: Coeff) -> BoolVal {
		!self.lit_at_least(domain, v + 1)
	}

	/// The single literal of a two-valued variable, which on its own already
	/// distinguishes both of its values.
	pub(crate) fn lit_single(&self) -> Option<Lit> {
		(self.x.len() == 1).then(|| self.x.get(0).unwrap())
	}

	/// Create the order literals for `domain`, reusing whatever literal `views`
	/// already provides for a value.
	pub(crate) fn new<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: &RangeList<Coeff>,
		_label: &str,
	) -> Self {
		let vals = || domain.iter().flatten().skip(1);
		Self {
			x: Literals::Range(new_named_var_range!(db, vals().count(), |i| {
				format!("{_label}≥{}", vals().nth(i).unwrap())
			})),
		}
	}

	/// The value represented under an assignment.
	pub(crate) fn value<F: crate::Valuation + ?Sized>(
		&self,
		domain: &RangeList<Coeff>,
		value: &F,
	) -> Coeff {
		let reached = self.x.iter().filter(|&l| value.value(l)).count();
		domain
			.iter()
			.flatten()
			.nth(reached)
			.expect("the order literals cannot reach past the domain")
	}
}

impl ShiftedVar {
	/// The view `sign·(x + shift)`, where `sign` is `1` or `-1`.
	pub(crate) fn signed(&self, sign: Coeff) -> IntVar {
		debug_assert!(sign == 1 || sign == -1, "a sign is one or minus one");
		IntVar {
			state: Rc::clone(&self.state),
			scale: sign,
			offset: sign * self.shift,
		}
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use std::rc::Rc;

	use itertools::{iproduct, Itertools};
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		constraint::linear::{Comparator, PosCoeff},
		decision::integer::{lex_geq_const, lex_leq_const, BinaryEncoding, IntVar, Lead},
		helpers::{
			binary_value,
			tests::{all_binary_solutions, binary_literals, expect_file, models},
		},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Lit, Unsatisfiable, Valuation,
	};

	#[test]
	fn a_channel_leaves_the_encoding_it_reaches_nothing_to_be_told() {
		// Only the lead has to hold a value of the domain, since the
		// channel carries holes and well-formedness both to the others.
		let domain = RangeList::from_elements([0, 1, 3]);
		let mut cnf = Cnf::default();
		let order_lits = cnf.new_var_range(2).iter_lits().collect_vec();
		let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &order_lits).unwrap();
		let direct_lits = cnf.new_var_range(3).iter_lits().collect_vec();
		x.with_direct_encoding(&mut cnf, &direct_lits, None)
			.unwrap();
		let bits = cnf
			.new_var_range(2)
			.iter_lits()
			.map(BoolVal::Lit)
			.collect_vec();
		x.with_binary_encoding(&mut cnf, &bits, 0, None).unwrap();
		assert_eq!(
			x.state.borrow().lead,
			Some(Lead::Binary),
			"the cheapest of the three to read"
		);

		let before = cnf.num_clauses();
		x.constrain(&mut cnf).unwrap();
		assert_eq!(
			cnf.num_clauses() - before,
			1,
			"the binary encoding's one hole, and nothing for the other two"
		);
		let read = {
			let (d, state) = (domain.clone(), x.state.borrow());
			let (order, direct, binary) = (
				state.order.clone().unwrap(),
				state.direct.clone().unwrap(),
				state.binary.clone().unwrap(),
			);
			move |v: &dyn Valuation| vec![order.value(&d, v), direct.value(&d, v), binary.value(v)]
		};
		assert_eq!(
			all_values(&cnf, &read),
			domain.iter().flatten().map(|d| vec![d; 3]).collect_vec(),
			"one model per value, and the three encodings agree on it"
		);
	}

	#[test]
	fn a_detected_variable_encodes_onto_the_literals_it_was_found_on() {
		let mut cnf = Cnf::default();
		let domain = RangeList::from_elements([0, 1, 3]);
		let found: Vec<_> = (0..2).map(|_| cnf.new_lit()).collect();
		let vars_before = cnf.num_vars();

		let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &found)
			.unwrap()
			.with_label("x");
		let ord = x.order_encoding(&mut cnf).unwrap();
		assert_eq!(
			cnf.num_vars(),
			vars_before,
			"the order encoding should reuse the literals it was given"
		);

		let bin = x.binary_encoding(&mut cnf).unwrap();
		let solutions = all_values(&cnf, &|v| vec![ord.value(&domain, v), bin.value(v)]);
		assert_eq!(
			solutions,
			domain
				.iter()
				.flatten()
				.map(|d| vec![d, d])
				.collect::<Vec<_>>()
		);
	}

	#[test]
	fn a_direct_encoding_represents_exactly_the_domain() {
		for domain in test_domains() {
			let mut cnf = Cnf::default();
			let dir = IntVar::new(domain.clone())
				.enforce_consistency(true)
				.with_label("x")
				.direct_encoding(&mut cnf)
				.unwrap();
			assert_eq!(
				all_values(&cnf, &|v| vec![dir.value(&domain, v)]),
				domain.iter().flatten().map(|d| vec![d]).collect::<Vec<_>>(),
				"direct encoding of {domain}"
			);
		}
	}

	#[test]
	fn a_direct_walk_settles_into_the_domain_too() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3).with_label("x");
		let walk = (-2..=6)
			.map(|v| (v, x.equals(&mut cnf, v).unwrap()))
			.collect_vec();

		let vars_before = cnf.num_vars();
		let y = IntVar::from_direct_walk(&mut cnf, walk).unwrap();
		assert_eq!(
			cnf.num_vars(),
			vars_before,
			"the walk was all of x's literals, so y needs none of its own"
		);
		assert_eq!(
			y.domain(),
			x.domain(),
			"the values never taken are not values"
		);
		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v)]),
			(0..=3).map(|d| vec![d, d]).collect_vec(),
			"a view reads as the variable it was taken from"
		);

		let mut cnf = Cnf::default();
		let k = IntVar::from_direct_walk(
			&mut cnf,
			[(1, BoolVal::Const(false)), (4, BoolVal::Const(true))],
		)
		.unwrap();
		assert_eq!(k.domain(), RangeList::from(4..=4));
		assert_eq!((cnf.num_vars(), cnf.num_clauses()), (0, 0));
	}

	#[test]
	#[should_panic(expected = "one literal per value")]
	fn a_direct_walk_takes_each_value_once() {
		let mut cnf = Cnf::default();
		let (a, b) = (cnf.new_lit(), cnf.new_lit());
		let _ = IntVar::from_direct_walk(&mut cnf, [(1, a.into()), (1, b.into())]);
	}

	#[test]
	fn a_direct_walk_takes_its_values_in_any_order() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=2);
		let walk = [2, 0, 1].map(|v| (v, x.equals(&mut cnf, v).unwrap()));
		let y = IntVar::from_direct_walk(&mut cnf, walk).unwrap();
		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v)]),
			(0..=2).map(|d| vec![d, d]).collect_vec(),
			"each literal stands for the value it came with"
		);
	}

	/// A view that falls negates the order literals, which only means the
	/// opposite bound where the literals have their consistency constraint.
	#[test]
	#[cfg(debug_assertions)]
	#[should_panic(expected = "needs its order consistency")]
	fn a_falling_view_needs_order_consistency() {
		let _ = -IntVar::new(0..=3).without_order_consistency();
	}

	#[test]
	fn a_question_the_domain_settles_costs_nothing() {
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();
			let (min, max) = (values[0], values[values.len() - 1]);
			let mut cnf = Cnf::default();
			let x = IntVar::new(domain.clone());

			assert_eq!(x.at_least(&mut cnf, min).unwrap(), BoolVal::Const(true));
			assert_eq!(
				x.at_least(&mut cnf, max + 1).unwrap(),
				BoolVal::Const(false)
			);
			assert_eq!(x.at_most(&mut cnf, max).unwrap(), BoolVal::Const(true));
			assert_eq!(x.at_most(&mut cnf, min - 1).unwrap(), BoolVal::Const(false));
			assert_eq!(x.equals(&mut cnf, max + 1).unwrap(), BoolVal::Const(false));
			assert_eq!(
				cnf.num_vars(),
				0,
				"nothing had to be encoded to answer over {domain:?}"
			);
		}
	}

	#[test]
	fn a_single_encoding_represents_exactly_the_domain() {
		for domain in test_domains() {
			let mut ord_cnf = Cnf::default();
			let ord = IntVar::new(domain.clone())
				.enforce_consistency(true)
				.with_label("x")
				.order_encoding(&mut ord_cnf)
				.unwrap();
			let mut bin_cnf = Cnf::default();
			let bin = IntVar::new(domain.clone())
				.enforce_consistency(true)
				.with_label("x")
				.binary_encoding(&mut bin_cnf)
				.unwrap();

			let expected: Vec<Vec<Coeff>> = domain.iter().flatten().map(|d| vec![d]).collect();
			assert_eq!(
				all_values(&ord_cnf, &|v| vec![ord.value(&domain, v)]),
				expected,
				"order encoding of {domain}"
			);
			assert_eq!(
				all_values(&bin_cnf, &|v| vec![bin.value(v)]),
				expected,
				"binary encoding of {domain}"
			);
		}
	}

	#[test]
	fn a_tied_encoding_is_constrained_through_its_channel() {
		// Constraining every view would repeat what the biconditional channels
		// say.
		let domain = RangeList::from_elements([0, 1, 3]);
		let mut cnf = Cnf::default();
		let order_lits = cnf.new_var_range(2).iter_lits().collect_vec();
		let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &order_lits).unwrap();
		let direct_lits = cnf.new_var_range(3).iter_lits().collect_vec();
		x.with_direct_encoding(&mut cnf, &direct_lits, None)
			.unwrap();

		let before = cnf.num_clauses();
		x.constrain(&mut cnf).unwrap();
		assert_eq!(
			cnf.num_clauses() - before,
			1,
			"the chain of the order encoding, and nothing for the direct one"
		);

		let read = {
			let (d, state) = (domain.clone(), x.state.borrow());
			let (order, direct) = (state.order.clone().unwrap(), state.direct.clone().unwrap());
			move |v: &dyn Valuation| vec![order.value(&d, v), direct.value(&d, v)]
		};
		assert_eq!(
			all_values(&cnf, &read),
			domain.iter().flatten().map(|d| vec![d, d]).collect_vec(),
			"the channel carries the constraint to the direct encoding"
		);
	}

	#[test]
	fn a_two_valued_direct_encoding_is_one_literal() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(RangeList::from_elements([0, 5])).enforce_consistency(true);
		let direct = x.direct_encoding(&mut cnf).unwrap();
		assert_eq!(
			(cnf.num_vars(), cnf.num_clauses()),
			(1, 0),
			"one literal and its negation say which of two values is taken"
		);
		let _ = x.order_encoding(&mut cnf).unwrap();
		assert_eq!(
			(cnf.num_vars(), cnf.num_clauses()),
			(1, 0),
			"the order view shares it"
		);
		let domain = RangeList::from_elements([0, 5]);
		let read = move |v: &dyn Valuation| vec![direct.value(&domain, v)];
		assert_eq!(all_values(&cnf, &read), vec![vec![0], vec![5]]);
	}

	#[test]
	fn a_two_valued_variable_shares_its_literal() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(RangeList::from_elements([0, 5]))
			.enforce_consistency(true)
			.with_label("x");
		let _ = x.order_encoding(&mut cnf).unwrap();
		let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());

		// The order literal already tells the two values apart, so the binary
		// encoding is a view onto it rather than fresh bits to channel against.
		let _ = x.binary_encoding(&mut cnf).unwrap();
		assert_eq!(
			(cnf.num_vars(), cnf.num_clauses()),
			(vars, clauses),
			"a two-valued variable should not pay for a second encoding"
		);
	}

	#[test]
	fn a_two_valued_variable_shares_its_literal_between_order_and_direct() {
		let mut cnf = Cnf::default();
		let lit = cnf.new_lit();
		let domain = RangeList::from_elements([0, 5]);
		let x = IntVar::from_direct_encoding(&mut cnf, domain.clone(), &[!lit, lit]).unwrap();
		assert_eq!(x.at_least(&mut cnf, 5).unwrap(), BoolVal::Lit(lit));
		let y = IntVar::from_order_encoding(&mut cnf, domain.clone(), &[lit]).unwrap();
		let direct = y.direct_encoding(&mut cnf).unwrap();
		assert_eq!(direct.lit_equals(&domain, 0), BoolVal::Lit(!lit));
		assert_eq!(
			(cnf.num_vars(), cnf.num_clauses()),
			(1, 0),
			"the literal already says both, so neither view should cost anything"
		);
	}

	#[test]
	fn a_variable_built_on_given_literals_takes_exactly_its_domain() {
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();

			let mut cnf = Cnf::default();
			let lits = cnf
				.new_var_range(values.len() - 1)
				.iter_lits()
				.collect_vec();
			let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &lits).unwrap();
			x.constrain(&mut cnf).unwrap();
			assert_eq!(
				all_values(&cnf, &|v| vec![x.value(v)]),
				values.iter().map(|&d| vec![d]).collect_vec(),
				"an order encoding on given literals over {domain:?}"
			);

			let mut cnf = Cnf::default();
			let lits = cnf.new_var_range(values.len()).iter_lits().collect_vec();
			let x = IntVar::from_direct_encoding(&mut cnf, domain.clone(), &lits).unwrap();
			x.constrain(&mut cnf).unwrap();
			assert_eq!(
				all_values(&cnf, &|v| vec![x.value(v)]),
				values.iter().map(|&d| vec![d]).collect_vec(),
				"a direct encoding on given literals over {domain:?}"
			);

			let mut cnf = Cnf::default();
			let (min, max) = (values[0], values[values.len() - 1]);
			let bits = binary_literals(&mut cnf, BinaryEncoding::required_bits(max - min));
			let x = IntVar::from_binary_encoding(&mut cnf, domain.clone(), &bits, min).unwrap();
			x.constrain(&mut cnf).unwrap();
			assert_eq!(
				all_values(&cnf, &|v| vec![x.value(v)]),
				values.iter().map(|&d| vec![d]).collect_vec(),
				"a binary encoding on given bits over {domain:?}"
			);
		}
	}

	#[test]
	fn a_variable_may_appear_twice_in_one_constraint() {
		// Reading the same variable more than once, as `x + x` would, must not
		// trip over the borrow the accessors take internally.
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3).enforce_consistency(true).with_label("x");
		let y = x.clone();
		let encs = [
			x.binary_encoding(&mut cnf).unwrap(),
			y.binary_encoding(&mut cnf).unwrap(),
		];
		let ords = [
			x.order_encoding(&mut cnf).unwrap(),
			y.order_encoding(&mut cnf).unwrap(),
		];

		let domain = x.domain();
		let solutions = all_values(&cnf, &|v| {
			vec![
				encs[0].value(v),
				encs[1].value(v),
				ords[0].value(&domain, v),
				ords[1].value(&domain, v),
			]
		});
		assert_eq!(
			solutions,
			(0..4).map(|d| vec![d; 4]).collect::<Vec<_>>(),
			"both handles are the same variable and must read alike"
		);
	}

	#[test]
	fn a_variable_times_zero_is_the_constant_zero() {
		let x = IntVar::new(1..=3);
		let zero = x.clone() * 0 + 4;
		assert_eq!(zero.domain(), RangeList::from(4..=4));
		assert!(!Rc::ptr_eq(&zero.state, &x.state), "a constant of its own");
	}

	#[test]
	fn a_variable_with_one_value_costs_nothing() {
		for k in [-3, 0, 7] {
			let mut cnf = Cnf::default();
			let x = IntVar::new(k..=k).enforce_consistency(true);

			assert_eq!(x.at_least(&mut cnf, k).unwrap(), BoolVal::Const(true));
			assert_eq!(x.at_most(&mut cnf, k).unwrap(), BoolVal::Const(true));
			assert_eq!(x.equals(&mut cnf, k).unwrap(), BoolVal::Const(true));
			assert_eq!(
				x.order_walk(&mut cnf).unwrap().collect_vec(),
				vec![(k, BoolVal::Const(true))]
			);
			assert_eq!(
				x.direct_walk(&mut cnf).unwrap().collect_vec(),
				vec![(k, BoolVal::Const(true))]
			);
			assert_eq!(x.binary_bits(&mut cnf).unwrap(), (Vec::new(), 1, k));
			assert_eq!(x.value(&|_: Lit| false), k);

			assert_eq!(
				(cnf.num_vars(), cnf.num_clauses()),
				(0, 0),
				"the constant {k} cost literals or clauses"
			);
		}
	}

	/// See [`a_variable_without_order_consistency_takes_no_direct_encoding`].
	#[test]
	#[should_panic(expected = "has no order consistency constraint")]
	fn a_variable_without_order_consistency_takes_no_binary_encoding() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3).without_order_consistency();
		let _ = x.order_encoding(&mut cnf).unwrap();
		let _ = x.binary_encoding(&mut cnf);
	}

	/// A variable without its order consistency constraint has literals that
	/// describe no value, so channelling another encoding to them is refused.
	#[test]
	#[should_panic(expected = "has no order consistency constraint")]
	fn a_variable_without_order_consistency_takes_no_direct_encoding() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3).without_order_consistency();
		let _ = x.order_encoding(&mut cnf).unwrap();
		let _ = x.direct_encoding(&mut cnf);
	}

	#[test]
	fn a_view_answers_with_the_literals_of_its_variable() {
		for domain in test_domains() {
			let values = domain.iter().flatten().collect_vec();
			for (a, b) in iproduct!([-3, -2, -1, 1, 2, 3], [-5, 0, 4]) {
				let mut cnf = Cnf::default();
				let x = IntVar::new(domain.clone()).with_label("x");
				let y = x.clone() * a + b;
				let asked = (y.min() - 2..=y.max() + 2)
					.map(|v| {
						(
							v,
							y.at_least(&mut cnf, v).unwrap(),
							y.at_most(&mut cnf, v).unwrap(),
							y.equals(&mut cnf, v).unwrap(),
						)
					})
					.collect_vec();
				// Two values are told apart by the one order literal, which the
				// direct encoding would only share.
				assert!(
					x.has_order_encoding() && (x.has_direct_encoding() || values.len() == 2),
					"the view asked its variable for the encodings"
				);
				// Asked again, nothing is created: every answer was one of the
				// variable's literals.
				let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());
				for &(v, ..) in &asked {
					let _ = y.at_least(&mut cnf, v).unwrap();
					let _ = y.equals(&mut cnf, v).unwrap();
				}
				assert_eq!((cnf.num_vars(), cnf.num_clauses()), (vars, clauses));

				let mut seen = models(&cnf, |sol| {
					let (xv, yv) = (x.value(sol), y.value(sol));
					assert_eq!(yv, a * xv + b, "{a}·x{b:+} at x = {xv}");
					for &(v, at_least, at_most, equals) in &asked {
						let view = format!("{a}·x{b:+} at x = {xv} against {v}");
						assert_eq!(holds(at_least, sol), yv >= v, "at least, {view}");
						assert_eq!(holds(at_most, sol), yv <= v, "at most, {view}");
						assert_eq!(holds(equals, sol), yv == v, "equals, {view}");
					}
					xv
				});
				seen.sort_unstable();
				seen.dedup();
				assert_eq!(
					seen, values,
					"the variable keeps exactly its domain under {a}·x{b:+}"
				);
			}
		}
	}

	#[test]
	fn a_view_at_the_edge_of_the_coefficients_narrows_without_overflow() {
		for (y, past) in [
			(IntVar::new(0..=Coeff::MAX) - 5, Coeff::MAX - 4),
			(-IntVar::new((Coeff::MIN + 1)..=0) - 5, Coeff::MAX - 4),
		] {
			let mut cnf = Cnf::default();
			assert_eq!(y.set_min(&mut cnf, past), Err(Unsatisfiable), "{y}");
			assert_eq!(y.set_max(&mut cnf, y.min() - 1), Err(Unsatisfiable), "{y}");
		}
	}

	#[test]
	fn a_view_costs_nothing_and_maps_the_domain() {
		for domain in test_domains() {
			let values = domain.iter().flatten().collect_vec();
			for (a, b) in iproduct!([-3, -1, 1, 2], [-5, 0, 4]) {
				let mut cnf = Cnf::default();
				let x = IntVar::new(domain.clone()).with_label("x");
				let y = x.clone() * a + b;
				let mapped = values.iter().map(|&v| a * v + b).sorted().collect_vec();
				assert_eq!(
					y.domain(),
					RangeList::from_sorted_elements(mapped.iter().copied()),
					"{a}·x{b:+} over {domain}"
				);
				assert_eq!(
					(y.min(), y.max(), y.card()),
					(mapped[0], mapped[mapped.len() - 1], values.len())
				);
				assert!(
					!y.has_order_encoding() && !y.has_direct_encoding() && !y.has_binary_encoding(),
					"a view of an unencoded variable is unencoded"
				);
				// A question the domain settles is settled through the view.
				assert_eq!(y.at_least(&mut cnf, y.min()).unwrap(), BoolVal::Const(true));
				assert_eq!(
					y.at_most(&mut cnf, y.min() - 1).unwrap(),
					BoolVal::Const(false)
				);
				if a.abs() > 1 {
					let skipped = y.min() + 1;
					assert_eq!(y.equals(&mut cnf, skipped).unwrap(), BoolVal::Const(false));
				}
				assert_eq!((cnf.num_vars(), cnf.num_clauses()), (0, 0), "{a}·x{b:+}");

				// The operators compose into one view of the same variable.
				let (min, max) = (y.min(), y.max());
				assert!((-(-y.clone())).is(&y));
				assert!((y.clone() + 7 - 7).is(&y));
				assert!((y.clone() * -2 + 3).is(&(-(y.clone() * 2) + 3)));
				assert_eq!(
					(y.clone() * -2).domain(),
					RangeList::from_sorted_elements(mapped.iter().rev().map(|v| -2 * v))
				);
				assert_eq!(
					(-y.clone() + (min + max)).value(&|_: Lit| false),
					min + max - y.value(&|_: Lit| false)
				);
			}
		}
	}

	#[test]
	fn a_view_is_labelled_by_its_arithmetic() {
		let x = IntVar::new(0..=9).with_label("x");
		assert_eq!((x.clone() + 3).label(), "x+3");
		assert_eq!((x.clone() - 3).label(), "x-3");
		assert_eq!((x.clone() * 2).label(), "2·x");
		assert_eq!((-x.clone()).label(), "-x");
		assert_eq!((-x.clone() + 9).label(), "-x+9");
		assert_eq!(((x.clone() + 3) * -2 + 1).label(), "-2·x-5");
		assert_eq!((x.clone() * 1 + 0).label(), "x");
		assert_eq!((IntVar::new(0..=1) * 2 + 1).label(), "", "unlabelled");
		assert!(
			(x.clone() * 1 + 0).is(&x),
			"the same view of the same variable"
		);
		assert!(!(x.clone() + 1).is(&x), "a different view");
	}

	/// A bound far outside a view is settled by the view's own bounds, before
	/// mapping it onto the variable could overflow.
	#[test]
	fn a_view_settles_extreme_bounds_without_overflow() {
		for (a, b) in [(1, 5), (-1, 5), (3, -7), (-3, Coeff::MAX - 20)] {
			let mut cnf = Cnf::default();
			let x = IntVar::new(0..=4);
			let y = x.clone() * a + b;
			let view = format!("{a}·x{b:+}");
			assert_eq!(
				y.encoded().at_least(Coeff::MIN),
				Some(BoolVal::Const(true)),
				"{view}"
			);
			assert_eq!(
				y.encoded().at_least(Coeff::MAX),
				Some(BoolVal::Const(false)),
				"{view}"
			);
			assert_eq!(
				y.encoded().equals(Coeff::MIN),
				Some(BoolVal::Const(false)),
				"{view}"
			);
			assert_eq!(
				y.encoded().equals(Coeff::MAX),
				Some(BoolVal::Const(false)),
				"{view}"
			);
			for (v, at_most) in [(Coeff::MAX, true), (Coeff::MIN, false)] {
				let settled = Some(BoolVal::Const(at_most));
				assert_eq!(y.encoded().at_most(v), settled, "{view}");
				assert_eq!(y.at_most(&mut cnf, v).ok(), settled, "{view}");
			}
			assert_eq!(y.set_min(&mut cnf, Coeff::MIN), Ok(false), "{view}");
			assert_eq!(y.set_max(&mut cnf, Coeff::MAX), Ok(false), "{view}");
			assert_eq!(
				y.set_min(&mut cnf, Coeff::MAX),
				Err(Unsatisfiable),
				"{view}"
			);
			let mut cnf = Cnf::default();
			assert_eq!(
				y.set_max(&mut cnf, Coeff::MIN),
				Err(Unsatisfiable),
				"{view}"
			);
		}
	}

	#[test]
	#[should_panic(expected = "overflows a coefficient")]
	fn a_view_shifted_past_the_least_coefficient_is_refused() {
		let _ = IntVar::new(0..=3) - Coeff::MIN;
	}

	#[test]
	#[should_panic(expected = "overflows a coefficient")]
	fn a_view_that_overflows_is_refused() {
		let _ = IntVar::new(0..=3) * Coeff::MAX * 2;
	}

	#[test]
	#[should_panic(expected = "overflows a coefficient")]
	fn a_view_whose_values_overflow_is_refused() {
		let _ = IntVar::new(0..=Coeff::MAX / 2) * 4;
	}

	/// A view on the literals of a variable without order consistency has none
	/// either.
	#[test]
	#[should_panic(expected = "has no order consistency constraint")]
	fn a_view_without_order_consistency_takes_no_direct_encoding() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=7).without_order_consistency();
		let up = (x.clone() + 1);
		let half = IntVar::halved(&mut cnf, &up).unwrap();
		let _ = half.direct_encoding(&mut cnf);
	}

	#[test]
	fn a_walk_wider_than_the_variable_is_trimmed_to_it() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3).with_label("x");
		let walk = (-2..=6)
			.map(|v| (v, x.at_least(&mut cnf, v).unwrap()))
			.collect_vec();
		assert_eq!(
			walk.iter()
				.filter(|(_, b)| *b == BoolVal::Const(true))
				.count(),
			3,
			"-2, -1 and 0 are always reached"
		);
		assert!(walk.iter().any(|(_, b)| *b == BoolVal::Const(false)));

		let vars_before = cnf.num_vars();
		let y = IntVar::from_order_walk(&mut cnf, walk.clone()).unwrap();
		assert_eq!(
			cnf.num_vars(),
			vars_before,
			"the walk was all of x's literals, so y needs none of its own"
		);
		assert_eq!(y.domain(), x.domain(), "the settled ends are not values");

		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v)]),
			(0..=3).map(|d| vec![d, d]).collect_vec(),
			"a view reads as the variable it was taken from"
		);
	}

	#[test]
	fn a_width_and_the_values_it_holds_are_inverses() {
		for bits in 0..=8 {
			let largest = BinaryEncoding::largest_in(bits);
			assert_eq!(BinaryEncoding::required_bits(largest), bits as usize);
			if bits > 0 {
				assert_eq!(
					BinaryEncoding::required_bits(largest + 1),
					bits as usize + 1
				);
			}
		}
		// The widest a coefficient goes lands exactly on its largest value,
		// where computing it as a power of two would overflow.
		assert_eq!(BinaryEncoding::largest_in(Coeff::BITS - 1), Coeff::MAX);
	}

	#[test]
	fn all_three_encodings_agree_on_every_value() {
		// Whichever order they are asked for in, and whichever two or three of
		// them exist, every view of the variable must read the same value.
		for domain in test_domains() {
			for order in [[0, 1, 2], [2, 1, 0], [1, 2, 0], [2, 0, 1]] {
				let mut cnf = Cnf::default();
				let x = IntVar::new(domain.clone())
					.enforce_consistency(true)
					.with_label("x");
				let mut read: Vec<Box<dyn Fn(&dyn Valuation) -> Coeff>> = Vec::new();
				for which in order {
					match which {
						0 => {
							let (e, d) = (x.order_encoding(&mut cnf).unwrap(), domain.clone());
							read.push(Box::new(move |v| e.value(&d, v)));
						}
						1 => {
							let e = x.binary_encoding(&mut cnf).unwrap();
							read.push(Box::new(move |v| e.value(v)));
						}
						_ => {
							let (e, d) = (x.direct_encoding(&mut cnf).unwrap(), domain.clone());
							read.push(Box::new(move |v| e.value(&d, v)));
						}
					}
				}
				let solutions = all_values(&cnf, &|v| read.iter().map(|f| f(v)).collect());
				let expected: Vec<Vec<Coeff>> =
					domain.iter().flatten().map(|d| vec![d; 3]).collect();
				assert_eq!(
					solutions, expected,
					"domain {domain} asked in order {order:?}"
				);
			}
		}
	}

	/// Every model of `cnf`, as the values `read` takes from it, in order.
	fn all_values(cnf: &Cnf, read: &dyn Fn(&dyn Valuation) -> Vec<Coeff>) -> Vec<Vec<Coeff>> {
		let mut solutions = models(cnf, read);
		solutions.sort();
		solutions
	}

	#[test]
	fn an_encoding_asked_through_a_view_is_the_variable_s() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(RangeList::from_elements([0, 1, 3])).with_label("x");
		let y = x.clone() + 3;
		y.require_order_encoding(&mut cnf).unwrap();
		assert!(x.has_order_encoding() && y.has_order_encoding());
		let clauses = cnf.num_clauses();
		// `y = 4` is `x = 1`, which wants the direct encoding of `x`.
		let _ = y.equals(&mut cnf, 4).unwrap();
		assert!(x.has_direct_encoding());
		assert!(
			cnf.num_clauses() > clauses,
			"the direct encoding is channelled to the order encoding"
		);
		let vars = cnf.num_vars();
		let z = y.mirrored();
		// `9 − y ≥ 5` is `y ≤ 4`, which is a literal there already.
		assert_eq!(
			z.at_least(&mut cnf, 5).unwrap(),
			y.at_most(&mut cnf, 4).unwrap()
		);
		assert_eq!(cnf.num_vars(), vars);
		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v), z.value(v)]),
			vec![vec![0, 3, 6], vec![1, 4, 5], vec![3, 6, 3]],
			"every view reads the one variable"
		);
	}

	#[test]
	fn an_encoding_given_later_is_tied_to_the_one_already_there() {
		// The literals are the caller's, so nothing but the channel says the
		// two views agree — which is what `channel` is there to ask for.
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();
			let (min, max) = (values[0], values[values.len() - 1]);

			let mut cnf = Cnf::default();
			let lits = cnf
				.new_var_range(values.len() - 1)
				.iter_lits()
				.collect_vec();
			let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &lits).unwrap();
			x.constrain(&mut cnf).unwrap();
			let bits = binary_literals(&mut cnf, BinaryEncoding::required_bits(max - min));
			x.with_binary_encoding(&mut cnf, &bits, min, None).unwrap();
			let read = {
				let d = domain.clone();
				let (ord, bin) = {
					let state = x.state.borrow();
					(state.order.clone().unwrap(), state.binary.clone().unwrap())
				};
				move |v: &dyn Valuation| vec![ord.value(&d, v), bin.value(v)]
			};
			assert_eq!(
				all_values(&cnf, &read),
				values.iter().map(|&d| vec![d, d]).collect_vec(),
				"an order and a binary encoding, both given, over {domain:?}"
			);

			let mut cnf = Cnf::default();
			let lits = cnf.new_var_range(values.len()).iter_lits().collect_vec();
			let x = IntVar::from_direct_encoding(&mut cnf, domain.clone(), &lits).unwrap();
			x.constrain(&mut cnf).unwrap();
			let ord_lits = cnf
				.new_var_range(values.len() - 1)
				.iter_lits()
				.collect_vec();
			x.with_order_encoding(&mut cnf, &ord_lits, None).unwrap();
			let read = {
				let d = domain.clone();
				let (ord, dir) = {
					let state = x.state.borrow();
					(state.order.clone().unwrap(), state.direct.clone().unwrap())
				};
				move |v: &dyn Valuation| vec![ord.value(&d, v), dir.value(&d, v)]
			};
			assert_eq!(
				all_values(&cnf, &read),
				values.iter().map(|&d| vec![d, d]).collect_vec(),
				"a direct and an order encoding, both given, over {domain:?}"
			);
		}
	}

	#[test]
	fn an_encoding_made_beside_another_is_told_nothing() {
		let domain = RangeList::from_elements([0, 1, 3]);
		let cost = |trusted: bool| {
			let mut cnf = Cnf::default();
			let x = IntVar::new(domain.clone());
			if trusted {
				let lits = cnf.new_var_range(2).iter_lits().collect_vec();
				x.with_order_encoding(&mut cnf, &lits, None).unwrap();
			} else {
				let _ = x.order_encoding(&mut cnf).unwrap();
			}
			let before = cnf.num_clauses();
			let _ = x.binary_encoding(&mut cnf).unwrap();
			cnf.num_clauses() - before
		};
		assert_eq!(
			cost(true),
			cost(false),
			"a promised order encoding carries as much as a constrained one"
		);
	}

	#[test]
	fn an_end_of_the_domain_is_taken_by_reaching_it() {
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();
			let (min, max) = (values[0], values[values.len() - 1]);
			let mut cnf = Cnf::default();
			let x = IntVar::new(domain.clone());
			let _ = x.at_least(&mut cnf, values[1]).unwrap();

			let vars_before = cnf.num_vars();
			let is_min = x.equals(&mut cnf, min).unwrap();
			let is_max = x.equals(&mut cnf, max).unwrap();
			assert_eq!(
				cnf.num_vars(),
				vars_before,
				"neither end of {domain:?} needed a direct encoding"
			);

			let solutions = all_values(&cnf, &|v| {
				vec![
					x.value(v),
					Coeff::from(holds(is_min, v)),
					Coeff::from(holds(is_max, v)),
				]
			});
			assert_eq!(
				solutions,
				values
					.iter()
					.map(|&d| vec![d, Coeff::from(d == min), Coeff::from(d == max)])
					.collect_vec(),
				"the ends of {domain:?}"
			);
		}
	}

	#[test]
	#[should_panic(expected = "only to a view `x + k`")]
	fn bits_are_not_given_through_a_scaled_view() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3);
		let bits = binary_literals(&mut cnf, 2);
		let _ = (x.clone() * 2).with_binary_encoding(&mut cnf, &bits, 0, None);
	}

	#[test]
	fn channelled_encodings_agree_on_every_value() {
		for domain in test_domains() {
			for bin_first in [false, true] {
				let mut cnf = Cnf::default();
				let x = IntVar::new(domain.clone())
					.enforce_consistency(true)
					.with_label("x");
				let (ord, bin) = if bin_first {
					let bin = x.binary_encoding(&mut cnf).unwrap();
					(x.order_encoding(&mut cnf).unwrap(), bin)
				} else {
					let ord = x.order_encoding(&mut cnf).unwrap();
					(ord, x.binary_encoding(&mut cnf).unwrap())
				};

				let solutions = all_values(&cnf, &|v| vec![ord.value(&domain, v), bin.value(v)]);
				let expected: Vec<Vec<Coeff>> =
					domain.iter().flatten().map(|d| vec![d, d]).collect();
				assert_eq!(
					solutions,
					expected,
					"domain {domain} channelled with {} first",
					if bin_first { "bin" } else { "ord" }
				);
			}
		}
	}

	#[test]
	fn constraining_a_literal_and_its_negation_costs_nothing() {
		let mut cnf = Cnf::default();
		let lit = cnf.new_lit();
		let domain = RangeList::from_elements([0, 5]);
		let x = IntVar::from_direct_encoding(&mut cnf, domain, &[!lit, lit]).unwrap();
		x.constrain(&mut cnf).unwrap();
		assert_eq!(
			cnf.num_clauses(),
			0,
			"exactly one of a literal and its negation holds without a clause"
		);
	}

	#[test]
	fn constraining_the_lead_holds_the_variable_to_its_domain() {
		let domain = RangeList::from_elements([0, 1, 3]);
		let expected = || domain.iter().flatten().map(|d| vec![d]).collect_vec();

		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(2).iter_lits().collect_vec();
		let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &lits).unwrap();
		x.constrain(&mut cnf).unwrap();
		assert_eq!(
			all_values(&cnf, &|v: &dyn Valuation| vec![x.value(v)]),
			expected()
		);

		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(3).iter_lits().collect_vec();
		let x = IntVar::from_direct_encoding(&mut cnf, domain.clone(), &lits).unwrap();
		x.constrain(&mut cnf).unwrap();
		assert_eq!(
			all_values(&cnf, &|v: &dyn Valuation| vec![x.value(v)]),
			expected()
		);

		// Two bits reach 2, which the domain does not have, and no further.
		let mut cnf = Cnf::default();
		let bits = cnf
			.new_var_range(2)
			.iter_lits()
			.map(BoolVal::Lit)
			.collect_vec();
		let x = IntVar::from_binary_encoding(&mut cnf, domain.clone(), &bits, 0).unwrap();
		x.constrain(&mut cnf).unwrap();
		assert_eq!(
			all_values(&cnf, &|v: &dyn Valuation| vec![x.value(v)]),
			expected()
		);
	}

	#[test]
	fn encodings_are_created_once() {
		let domain = RangeList::from_elements([0, 1, 3]);
		let mut cnf = Cnf::default();
		let x = IntVar::new(domain)
			.enforce_consistency(true)
			.with_label("x");

		let _ = x.order_encoding(&mut cnf).unwrap();
		let _ = x.binary_encoding(&mut cnf).unwrap();
		let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());

		let _ = x.order_encoding(&mut cnf).unwrap();
		let _ = x.binary_encoding(&mut cnf).unwrap();
		assert_eq!((cnf.num_vars(), cnf.num_clauses()), (vars, clauses));
	}

	#[test]
	fn every_way_of_reading_a_variable_agrees() {
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();
			let mut cnf = Cnf::default();
			let x = IntVar::new(domain.clone());

			let reaches = x.order_walk(&mut cnf).unwrap().collect_vec();
			let takes = x.direct_walk(&mut cnf).unwrap().collect_vec();
			let (bits, _, min) = x.binary_bits(&mut cnf).unwrap();
			assert_eq!(reaches.len(), values.len());
			assert_eq!(takes.len(), values.len());

			let solutions = all_values(&cnf, &|v| {
				vec![
					reaches
						.iter()
						.filter(|&&(_, b)| holds(b, v))
						.map(|&(d, _)| d)
						.max()
						.expect("the variable reaches its lowest value"),
					takes
						.iter()
						.find(|&&(_, b)| holds(b, v))
						.expect("the variable takes some value")
						.0,
					min + binary_value(&bits, v),
				]
			});
			assert_eq!(
				solutions,
				values.iter().map(|&d| vec![d; 3]).collect_vec(),
				"reaching, taking and the bits over {domain:?}"
			);
		}
	}

	/// Whether `b` holds under the assignment `v`.
	fn holds(b: BoolVal, v: &dyn Valuation) -> bool {
		match b {
			BoolVal::Const(c) => c,
			BoolVal::Lit(l) => v.value(l),
		}
	}

	#[test]
	fn lex_const_bounds_a_binary_encoding() {
		for k in 0..8 {
			for (leq, expected) in [
				(true, (0..=k).collect::<Vec<Coeff>>()),
				(false, (k..8).collect()),
			] {
				let mut cnf = Cnf::default();
				let x = binary_literals(&mut cnf, 3);
				let k = PosCoeff::new(k);
				if leq {
					lex_leq_const(&mut cnf, &x, k, 3).unwrap();
				} else {
					lex_geq_const(&mut cnf, &x, k, 3).unwrap();
				}
				let solutions: Vec<Coeff> = all_binary_solutions(&cnf, &[&x])
					.into_iter()
					.map(|s| s[0])
					.collect();
				assert_eq!(solutions, expected, "{} {k}", if leq { "<=" } else { ">=" });
			}
		}
	}

	#[test]
	fn lex_geq_const_with_a_fixed_zero_bit() {
		// A one bit of `k` whose `x` bit is fixed to zero loses that
		// disjunct, and the higher bits still have to carry the clause.
		let mut cnf = Cnf::default();
		let x = vec![
			BoolVal::Lit(cnf.new_lit()),
			BoolVal::Const(false),
			BoolVal::Lit(cnf.new_lit()),
		];
		lex_geq_const(&mut cnf, &x, PosCoeff::new(2), 3).unwrap();

		let solutions: Vec<Coeff> = all_binary_solutions(&cnf, &[&x])
			.into_iter()
			.map(|s| s[0])
			.collect();
		// Representable values are {0, 1, 4, 5}; only 4 and 5 are at least 2.
		assert_eq!(solutions, vec![4, 5]);
	}

	#[test]
	fn literals_given_through_a_view_are_read_the_way_the_view_runs() {
		let domain = RangeList::from_elements([0, 1, 3]);
		let expected = vec![vec![0, 3], vec![1, 2], vec![3, 0]];

		// `lits[0]` is `y ≥ 2`, which is `x ≤ 1`, and `lits[1]` is `y ≥ 3`,
		// which is `x ≤ 0`.
		let mut cnf = Cnf::default();
		let x = IntVar::new(domain.clone());
		let y = x.mirrored();
		let lits = cnf.new_var_range(2).iter_lits().collect_vec();
		y.with_order_encoding(&mut cnf, &lits, None).unwrap();
		assert_eq!(y.at_least(&mut cnf, 2).unwrap(), BoolVal::Lit(lits[0]));
		assert_eq!(x.at_least(&mut cnf, 3).unwrap(), BoolVal::Lit(!lits[0]));
		assert_eq!(x.at_least(&mut cnf, 1).unwrap(), BoolVal::Lit(!lits[1]));
		y.constrain(&mut cnf).unwrap();
		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v)]),
			expected
		);

		// `lits[i]` is `y` taking the `i`'th of its values, from the least.
		let mut cnf = Cnf::default();
		let x = IntVar::new(domain.clone());
		let y = x.mirrored();
		let lits = cnf.new_var_range(3).iter_lits().collect_vec();
		y.with_direct_encoding(&mut cnf, &lits, None).unwrap();
		assert_eq!(y.equals(&mut cnf, 0).unwrap(), BoolVal::Lit(lits[0]));
		assert_eq!(x.equals(&mut cnf, 3).unwrap(), BoolVal::Lit(lits[0]));
		assert_eq!(x.equals(&mut cnf, 0).unwrap(), BoolVal::Lit(lits[2]));
		y.constrain(&mut cnf).unwrap();
		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v)]),
			expected
		);

		// Bits count up from the least value of the view they are given to.
		let mut cnf = Cnf::default();
		let x = IntVar::new(domain.clone());
		let y = x.clone() + 5;
		let bits = binary_literals(&mut cnf, 2);
		y.with_binary_encoding(&mut cnf, &bits, 5, None).unwrap();
		y.constrain(&mut cnf).unwrap();
		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v)]),
			vec![vec![0, 5], vec![1, 6], vec![3, 8]]
		);
	}

	#[test]
	fn narrowing_a_shared_literal_fixes_it_once() {
		let mut cnf = Cnf::default();
		let lit = cnf.new_lit();
		let domain = RangeList::from_elements([0, 5]);
		let x = IntVar::from_direct_encoding(&mut cnf, domain, &[!lit, lit]).unwrap();
		let _ = x.at_least(&mut cnf, 5).unwrap();
		assert!(x.set_max(&mut cnf, 0).unwrap());
		assert_eq!(
			cnf.iter().collect_vec(),
			vec![&[!lit][..]],
			"the order and direct encodings share the literal, so one unit fixes it"
		);
	}

	#[test]
	fn narrowing_a_view_narrows_its_variable_and_every_other_view() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=9).with_label("x");
		let (y, z) = (x.clone() * 2 + 1, x.mirrored());
		x.require_order_encoding(&mut cnf).unwrap();
		// `2x + 1 ≤ 10` is `x ≤ 4`.
		assert!(y.set_max(&mut cnf, 10).unwrap());
		assert_eq!(x.domain(), RangeList::from(0..=4));
		assert_eq!(y.domain(), RangeList::from_sorted_elements([1, 3, 5, 7, 9]));
		assert_eq!(z.domain(), RangeList::from(5..=9));
		// `9 − x ≤ 7` is `x ≥ 2`.
		assert!(z.set_max(&mut cnf, 7).unwrap());
		assert_eq!(x.domain(), RangeList::from(2..=4));
		assert_eq!((y.min(), y.max(), z.min(), z.max()), (5, 9, 5, 7));
		// A bound the view meets already changes nothing, and one between two
		// of its values rounds in.
		assert!(!y.set_min(&mut cnf, 4).unwrap());
		assert!(y.set_min(&mut cnf, 6).unwrap());
		assert_eq!(x.domain(), RangeList::from(3..=4));
		assert_eq!(
			all_values(&cnf, &|v| vec![x.value(v), y.value(v), z.value(v)]),
			vec![vec![3, 7, 6], vec![4, 9, 5]],
			"the units fixed the literals of the values that went"
		);
		// `9 − x ≥ 7` is `x ≤ 2`, of which nothing is left.
		assert_eq!(z.set_min(&mut cnf, 7), Err(Unsatisfiable));
	}

	#[test]
	fn only_an_equal_channel_spares_the_encoding_it_reaches() {
		// One-way bounds do not replace an equality channel.
		let domain = RangeList::from(0..=2);
		let build = |already_channelled| {
			let mut cnf = Cnf::default();
			let order_lits = cnf.new_var_range(2).iter_lits().collect_vec();
			let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &order_lits).unwrap();
			let direct_lits = cnf.new_var_range(3).iter_lits().collect_vec();
			x.with_direct_encoding(&mut cnf, &direct_lits, already_channelled)
				.unwrap();
			let tied = cnf.num_clauses();
			x.constrain(&mut cnf).unwrap();
			(tied, cnf.num_clauses() - tied)
		};

		assert_eq!(
			build(Some(Comparator::Equal)),
			(0, 1),
			"nothing to tie them, and only the order encoding to constrain"
		);
		for partial in [None, Some(Comparator::LessEq), Some(Comparator::GreaterEq)] {
			let (tied, constrained) = build(partial);
			assert!(tied > 0, "{partial:?} leaves the two to be tied together");
			assert_eq!(constrained, 1, "which is what carries the constraint");
		}
	}

	#[test]
	fn steps_through_a_view_guard_on_the_values_of_the_view() {
		for domain in test_domains() {
			for (a, b, geq, direct) in
				iproduct!([-2, -1, 1, 2], [-3, 0, 4], [true, false], [false, true])
			{
				let mut cnf = Cnf::default();
				let x = IntVar::new(domain.clone()).with_label("x");
				let y = x.clone() * a + b;
				let steps = if direct {
					y.direct_steps(&mut cnf, geq).unwrap()
				} else {
					y.order_steps(&mut cnf, geq).unwrap()
				};
				let case = format!("{a}·x{b:+} geq {geq} direct {direct}");
				// The values of the view, from the end the walk starts at.
				let mut values = y.domain().iter().flatten().collect_vec();
				if !geq {
					values.reverse();
				}
				assert_eq!(
					steps.iter().map(|&(w, _)| w).collect_vec(),
					values,
					"{case}"
				);
				assert_eq!(steps[0].1, BoolVal::Const(false), "{case}");
				let _ = models(&cnf, |sol| {
					let yv = y.value(sol);
					for &(w, guard) in &steps[1..] {
						// A guard holds unless the view has reached its value:
						// taken it, or come to it from the side walked from.
						let reached = match (direct, geq) {
							(true, _) => yv == w,
							(false, true) => yv >= w,
							(false, false) => yv <= w,
						};
						assert_eq!(holds(guard, sol), !reached, "{case} at {yv} against {w}");
					}
				});
			}
		}
	}

	/// A handful of domains covering the shapes an encoding has to survive: a
	/// contiguous one, holes, negative values, a power-of-two span that fills
	/// the bits exactly, and a two-valued one.
	fn test_domains() -> Vec<RangeList<Coeff>> {
		vec![
			RangeList::from(0..=3),
			RangeList::from(0..=4),
			RangeList::from_elements([0, 1, 3]),
			RangeList::from_elements([2, 5, 6, 7, 9]),
			RangeList::from_elements([-3, -1, 0, 4]),
			RangeList::from_elements([-7, -6]),
			RangeList::from_elements([0, 5]),
		]
	}

	#[test]
	fn the_value_is_read_from_the_encoding_that_leads() {
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3);
		assert_eq!(
			x.state.borrow().lead,
			None,
			"nothing has been asked of it yet"
		);
		let _ = x.direct_encoding(&mut cnf).unwrap();
		assert_eq!(
			x.state.borrow().lead,
			Some(Lead::Direct),
			"the first encoding"
		);
		let _ = x.order_encoding(&mut cnf).unwrap();
		assert_eq!(
			x.state.borrow().lead,
			Some(Lead::Direct),
			"the order encoding is no cheaper to read, so the lead stays put"
		);
		let _ = x.binary_encoding(&mut cnf).unwrap();
		assert_eq!(
			x.state.borrow().lead,
			Some(Lead::Binary),
			"equal to the order encoding, which is equal to the direct one"
		);
		assert_eq!(
			all_values(&cnf, &|v: &dyn Valuation| vec![x.value(v)]),
			(0..=3).map(|d| vec![d]).collect_vec()
		);
	}

	#[test]
	fn what_the_encodings_cost() {
		// Size checks catch linear channelling growth and the second-view
		// cliff.
		let mut table = format!(
			"{:>6} {:>14} {:>7} {:>8} {:>9}\n",
			"card", "encodings", "vars", "clauses", "literals"
		);
		for card in [8usize, 64, 256, 1024] {
			let domain = RangeList::from(0..=(card as Coeff - 1));
			for (name, order, binary, direct) in [
				("order", true, false, false),
				("binary", false, true, false),
				("direct", false, false, true),
				("order+binary", true, true, false),
				("order+direct", true, false, true),
				("all three", true, true, true),
			] {
				// The direct encoding's exactly-one is quadratic, so it is only
				// measured where the measurement is affordable.
				if direct && card > 64 {
					continue;
				}
				let mut cnf = Cnf::default();
				let x = IntVar::new(domain.clone());
				if order {
					let _ = x.order_encoding(&mut cnf).unwrap();
				}
				if binary {
					let _ = x.binary_encoding(&mut cnf).unwrap();
				}
				if direct {
					let _ = x.direct_encoding(&mut cnf).unwrap();
				}
				x.constrain(&mut cnf).unwrap();
				table += &format!(
					"{card:>6} {name:>14} {:>7} {:>8} {:>9}\n",
					cnf.num_vars(),
					cnf.num_clauses(),
					cnf.literals()
				);
			}
		}
		expect_file!("int/encodings.size").assert_eq(&table);
	}
}
