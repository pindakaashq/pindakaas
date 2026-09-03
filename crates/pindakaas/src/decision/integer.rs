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

use std::{
	cell::RefCell,
	fmt::{self, Display},
	ops::Bound,
	rc::Rc,
};

use itertools::{Either, Itertools};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::FxHashMap;

use crate::{
	constraint::linear::{Comparator, PosCoeff},
	helpers::{as_binary, bit, new_named_var_range},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Lit, Result, Unsatisfiable, Var, VarRange,
};

/// How far a decomposition should narrow the domains of the variables it
/// makes, before the constraints between them are encoded.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Consistency {
	/// Leave the domains as they are.
	#[default]
	None,
	/// Narrow each domain to the bounds its constraints imply.
	Bounds,
	/// Narrow each domain to the values its constraints imply, holes and all.
	Domain,
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
	// A one bit of `k` needs the same bit of `x` set, or a higher bit of
	// `x` set where `k` had none.
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
	// A zero bit of `k` needs the same bit of `x` clear, or a higher bit of
	// `x` clear where `k` had one.
	for i in 0..bits {
		if !k[i] {
			db.add_clause((i..bits).filter(|&j| j == i || k[j]).map(|j| !bit(x, j)))?;
		}
	}
	Ok(())
}

/// The binary encoding of an integer variable.
///
/// The bits are those of `value - min`, least significant first. Where the
/// count starts belongs to the encoding rather than the library: the lower
/// bound, so that it costs nothing to enforce, or zero where the bits came from
/// a caller and already count from there. Both turn up within one constraint.
///
/// A bit may be fixed rather than free, which is what expresses a shifted or
/// complemented encoding without introducing literals for it.
#[derive(Clone, Debug)]
pub(crate) struct BinaryEncoding {
	x: Literals<BoolVal>,
	min: Coeff,
}

/// The literals of an encoding.
///
/// Literals created for an encoding are allocated in one block and so are
/// consecutive, which a range holds in a couple of words however wide the
/// encoding is — worth having, since an encoding is handed out by value every
/// time a constraint asks for it. Literals recovered from a constraint that
/// already mentions them, or bits fixed by a shift, are kept as given.
#[derive(Clone, Debug)]
pub(crate) enum Literals<T> {
	Explicit(Vec<T>),
	Range(VarRange),
}

/// The direct encoding of an integer variable.
///
/// There is one literal per domain value except the first, holding when the
/// variable takes exactly that value; none of them holding means it takes the
/// first. At most one may hold, which for a group of mutually exclusive
/// pseudo-Boolean terms is what the caller has already asserted.
#[derive(Clone, Debug)]
pub(crate) struct DirectEncoding {
	x: Literals<Lit>,
}

/// An integer decision variable, together with whichever Boolean encodings of
/// it have been asked for so far.
///
/// Variables are shared between the constraints that mention them: cloning a
/// handle is a new reference to the same variable, not a copy of it.
///
/// See the [module documentation](self) for how encodings are created and
/// channelled, and for what a variable built on existing literals does and does
/// not emit.
#[derive(Clone, Debug)]
pub struct IntVar(Rc<RefCell<IntVarState>>);

/// The encoding a variable's value is read from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Lead {
	Order,
	Binary,
	Direct,
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
	/// is exact by construction, so this only concerns the binary one.
	add_consistency: bool,
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

impl BinaryEncoding {
	/// The largest value `bits` bits can hold, the inverse of
	/// [`Self::required_bits`].
	pub(crate) fn largest_in(bits: u32) -> Coeff {
		// Summed rather than `(1 << bits) - 1`, which overflows at the width of
		// a coefficient where the sum lands exactly on its largest value.
		const TWO: Coeff = 2;
		(0..bits).fold(0, |sum, i| sum + TWO.pow(i))
	}

	/// The number of bits needed to represent `0..=span`.
	pub(crate) fn required_bits(span: Coeff) -> usize {
		debug_assert!(
			span >= 0,
			"a domain cannot span a negative number of values"
		);
		(Coeff::BITS - span.leading_zeros()) as usize
	}

	/// The `i`'th bit, where bits beyond the encoding's width are zero.
	pub(crate) fn lit_bit(&self, i: usize) -> BoolVal {
		self.x.get(i).unwrap_or(BoolVal::Const(false))
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
		let floor = *domain.min().unwrap() - self.min;
		if floor > 0 {
			lex_geq_const(db, &self.x.to_vec(), PosCoeff::new(floor), self.bits())?;
		}
		let span = *domain.max().unwrap() - self.min;
		lex_leq_const(db, &self.x.to_vec(), PosCoeff::new(span), self.bits())?;
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

	/// An encoding of bits already built, counting from `min`.
	pub(crate) fn from_bits(bits: Vec<BoolVal>, min: Coeff) -> Self {
		Self {
			x: Literals::Explicit(bits),
			min,
		}
	}

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

	/// The bits of the encoding, least significant first.
	pub(crate) fn to_vec(&self) -> Vec<BoolVal> {
		self.x.to_vec()
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

	/// The value represented under an assignment.
	pub(crate) fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		self.min + crate::helpers::binary_value(&self.x.to_vec(), value)
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
}

impl DirectEncoding {
	/// Restrict the encoding to holding for exactly one value.
	pub(crate) fn consistent<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		db.add_clause(self.x.iter())?;
		for (i, a) in self.x.iter().enumerate() {
			for b in self.x.iter().skip(i + 1) {
				db.add_clause([!a, !b])?;
			}
		}
		Ok(())
	}

	/// Whether the variable takes exactly `v`.
	pub(crate) fn lit_equals(&self, domain: &RangeList<Coeff>, v: Coeff) -> BoolVal {
		match domain.iter().flatten().position(|d| d == v) {
			None => BoolVal::Const(false),
			Some(pos) => BoolVal::Lit(self.x.get(pos).unwrap()),
		}
	}

	/// Create a direct encoding from the literals it is already on, one for
	/// each value of `domain` in order.
	pub(crate) fn from_literals(domain: &RangeList<Coeff>, x: Vec<Lit>) -> Self {
		debug_assert_eq!(
			x.len(),
			domain.card().unwrap(),
			"a direct encoding has a literal for every value"
		);
		Self {
			x: Literals::Explicit(x),
		}
	}

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

	/// The steps of a sequential decomposition over this variable.
	///
	/// Each step is a value paired with the clause that holds unless the
	/// variable takes it, so that what the constraint then demands can be
	/// disjoined onto it — the same shape the order encoding gives, except that
	/// a step here pins the value exactly rather than bounding it.
	///
	/// The value at the far end contributes the least of any, so what it
	/// demands holds whatever the variable turns out to be; its clause is
	/// `false` and drops out, leaving that demand unconditional.
	pub(crate) fn iter<'a>(
		&'a self,
		domain: &'a RangeList<Coeff>,
		geq: bool,
	) -> impl Iterator<Item = (Coeff, BoolVal)> + 'a {
		let vals = domain.iter().flatten();
		let step = move |(i, d): (usize, Coeff)| {
			(
				d,
				if i == 0 {
					BoolVal::Const(false)
				} else {
					!self.lit_equals(domain, d)
				},
			)
		};
		if geq {
			Either::Left(vals.enumerate().map(step))
		} else {
			Either::Right(vals.rev().enumerate().map(step))
		}
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
}

impl IntVar {
	/// The binary encoding of the variable, created if this is the first
	/// request for it.
	pub(crate) fn binary_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<BinaryEncoding> {
		if let Some(bin) = self.0.borrow().binary.as_ref() {
			return Ok(bin.clone());
		}
		// Take what is needed out of the variable before touching the database,
		// so that no borrow is held while clauses are emitted.
		let (domain, view) = {
			let state = self.0.borrow();
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
				let bin = BinaryEncoding::new(db, &domain, &self.label());
				if self.needs_constraining() {
					bin.consistent(db, &domain)?;
					self.0.borrow_mut().constrained = true;
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
			let mut state = self.0.borrow_mut();
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

	/// Tie together whatever encodings the variable now has, so that every view
	/// of it reads the same value.
	///
	/// The order encoding is the go-between: tying a new encoding to it is
	/// enough for the new one to agree with everything already tied to it. A
	/// variable holding only the other two therefore gains one, which is the
	/// price of reading it two ways at once.
	fn reconcile<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (has_order_encoding, others) = {
			let state = self.0.borrow();
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
		// The binary encoding is cheapest to read from, so it leads
		// where it can: where it and the current lead agree through the
		// order encoding.
		let mut state = self.0.borrow_mut();
		let equal = [
			state.channelled[0] == Some(Comparator::Equal),
			state.channelled[1] == Some(Comparator::Equal),
		];
		if state.binary.is_some() && equal[0] && (state.lead != Some(Lead::Direct) || equal[1]) {
			state.lead = Some(Lead::Binary);
		}
		Ok(())
	}

	/// The direct encoding of the variable, created if this is the first
	/// request for it.
	pub(crate) fn direct_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<DirectEncoding> {
		if let Some(dir) = self.0.borrow().direct.as_ref() {
			return Ok(dir.clone());
		}
		let domain = self.0.borrow().domain.clone();
		let vals = || domain.iter().flatten();
		debug_assert!(
			vals().count() > 1,
			"a variable with one value is that value, which no literal has to say"
		);
		let dir = DirectEncoding {
			x: Literals::Range(new_named_var_range!(db, vals().count(), |i| format!(
				"{}={}",
				self.label(),
				vals().nth(i).unwrap()
			))),
		};
		// One value and no more, which the chain gives the order
		// encoding for free but the direct encoding has to be told,
		// quadratically.
		if self.needs_constraining() {
			dir.consistent(db)?;
			self.0.borrow_mut().constrained = true;
		}
		self.install_direct(db, dir.clone(), None)?;
		Ok(dir)
	}

	/// Constrain the order and direct encodings to represent the same value.
	///
	/// Taking a value means reaching it, and reaching a value without reaching
	/// the next is taking it. Those two are the whole of it, and they are one
	/// clause each per value.
	fn channel_direct<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (ord, dir, domain) = {
			let mut state = self.0.borrow_mut();
			match (state.order.as_ref(), state.direct.as_ref()) {
				(Some(ord), Some(dir)) if state.channelled[1] != Some(Comparator::Equal) => {
					let all = (ord.clone(), dir.clone(), state.domain.clone());
					state.channelled[1] = Some(Comparator::Equal);
					all
				}
				_ => return Ok(()),
			}
		};
		let vals: Vec<Coeff> = domain.iter().flatten().collect();
		for (i, &v) in vals.iter().enumerate() {
			// Beyond the last value there is nothing to reach.
			let beyond = vals
				.get(i + 1)
				.map_or(BoolVal::Const(false), |&n| ord.lit_at_least(&domain, n));
			// Taking a value is reaching it and going no further, and reaching
			// it and going no further is taking it.
			db.add_clause([!dir.lit_equals(&domain, v), ord.lit_at_least(&domain, v)])?;
			db.add_clause([!dir.lit_equals(&domain, v), !beyond])?;
			db.add_clause([
				!ord.lit_at_least(&domain, v),
				beyond,
				dir.lit_equals(&domain, v),
			])?;
		}
		Ok(())
	}

	/// Constrain the encodings the variable has to say a value of its domain.
	///
	/// Emits the implication chain of an order encoding, one value and no more
	/// of a direct one, and the bounds and holes of a binary one, for whichever
	/// the variable has. This is what a variable built on literals that are not
	/// already constrained needs — see the [module documentation](self) — and
	/// it is how a declared bound becomes a restriction rather than a claim.
	///
	/// Only the encoding the value is read from is constrained; the rest are
	/// worth what their channels to it make them worth. An encoding tied
	/// one-directionally is a bound rather than the value, and so has no value
	/// to constrain.
	pub fn constrain<Db: ClauseDatabase + ?Sized>(&self, db: &mut Db) -> Result {
		let (lead, order, direct, binary, domain) = {
			let mut state = self.0.borrow_mut();
			// An encoding made for this variable was held to the
			// domain as it was made, and everything else is tied to
			// that one.
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
			// Nothing was ever asked of it, so it is its one value already.
			None => Ok(()),
		}
	}

	/// The bits of `c·(x − min)`, where they have already been built.
	pub(crate) fn product(&self, c: Coeff) -> Option<Vec<BoolVal>> {
		// The bits of `1·x` are the binary encoding itself, so there is nothing
		// to remember separately.
		if c == 1 {
			return self.0.borrow().binary.as_ref().map(BinaryEncoding::to_vec);
		}
		self.0.borrow().products.get(&c).cloned()
	}

	/// Remember the bits of `c·(x − min)`, so that the next constraint to scale
	/// the variable by `c` finds them.
	pub(crate) fn set_product(&self, c: Coeff, bits: Vec<BoolVal>) {
		debug_assert_ne!(c, 1);
		let _ = self.0.borrow_mut().products.insert(c, bits);
	}

	/// The domain of the variable.
	pub fn domain(&self) -> RangeList<Coeff> {
		self.0.borrow().domain.clone()
	}

	/// Whether the variable is held in a direct encoding, which is the view a
	/// constraint reads it through when it has one.
	pub fn has_direct_encoding(&self) -> bool {
		self.0.borrow().direct.is_some()
	}

	/// Whether the variable is held in a binary encoding.
	pub fn has_binary_encoding(&self) -> bool {
		self.0.borrow().binary.is_some()
	}

	/// Whether the variable is at least `v`.
	///
	/// The answer is a constant where the domain settles it, and otherwise one
	/// literal of the order encoding, which is created if the variable has not
	/// been asked for one before.
	pub fn lit_at_least<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<BoolVal, Unsatisfiable> {
		{
			let state = self.0.borrow();
			if v <= *state.domain.min().unwrap() {
				return Ok(BoolVal::Const(true));
			} else if v > *state.domain.max().unwrap() {
				return Ok(BoolVal::Const(false));
			} else if let Some(order) = state.order.as_ref() {
				return Ok(order.lit_at_least(&state.domain, v));
			}
		}
		let order = self.order_encoding(db)?;
		let state = self.0.borrow();
		Ok(order.lit_at_least(&state.domain, v))
	}

	/// Whether the variable is at most `v`, which is whether it fails to reach
	/// the value after it.
	pub fn lit_at_most<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<BoolVal, Unsatisfiable> {
		Ok(!self.lit_at_least(db, v + 1)?)
	}

	/// Whether the variable takes exactly `v`.
	///
	/// The answer is a constant where the domain settles it, and one literal of
	/// the order encoding where `v` is at either end of the domain, since
	/// reaching the last value or failing to reach the second is the same as
	/// taking it. Anywhere else it takes the direct encoding, which is created
	/// if the variable has none — and tying that to an encoding it already has
	/// costs clauses in proportion to the size of the domain, so it is worth
	/// giving a variable its direct encoding up front where every value will be
	/// asked about.
	pub fn lit_equals<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		v: Coeff,
	) -> Result<BoolVal, Unsatisfiable> {
		{
			let state = self.0.borrow();
			if !state.domain.contains(&v) {
				return Ok(BoolVal::Const(false));
			} else if state.domain.card().unwrap() == 1 {
				return Ok(BoolVal::Const(true));
			} else if let Some(direct) = state.direct.as_ref() {
				return Ok(direct.lit_equals(&state.domain, v));
			}
			// Only where the order encoding is the one already there, since
			// otherwise the direct encoding answers in one literal anyway.
			if state.order.is_some() {
				if v == *state.domain.max().unwrap() {
					drop(state);
					return self.lit_at_least(db, v);
				} else if v == *state.domain.min().unwrap() {
					drop(state);
					return self.lit_at_most(db, v);
				}
			}
		}
		let direct = self.direct_encoding(db)?;
		let state = self.0.borrow();
		Ok(direct.lit_equals(&state.domain, v))
	}

	/// The order encoding walked: every value of the domain, paired with
	/// whether the variable is at least it.
	///
	/// This is [`IntVar::lit_at_least`] over the whole domain, and creates the
	/// order encoding for the same reason.
	pub fn lit_order_walk<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<impl Iterator<Item = (Coeff, BoolVal)>, Unsatisfiable> {
		let order = self.order_encoding(db)?;
		let state = self.0.borrow();
		Ok(state
			.domain
			.iter()
			.flatten()
			.map(|v| (v, order.lit_at_least(&state.domain, v)))
			.collect_vec()
			.into_iter())
	}

	/// Every value of the domain, paired with whether the variable takes it —
	/// what [`IntVar::lit_equals`] gives, without asking value by value.
	pub fn lit_direct_walk<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<impl Iterator<Item = (Coeff, BoolVal)>, Unsatisfiable> {
		if self.card() == 1 {
			return Ok(vec![(self.min(), BoolVal::Const(true))].into_iter());
		}
		let direct = self.direct_encoding(db)?;
		let state = self.0.borrow();
		Ok(state
			.domain
			.iter()
			.flatten()
			.map(|v| (v, direct.lit_equals(&state.domain, v)))
			.collect_vec()
			.into_iter())
	}

	/// The bits of the variable, least significant first, together with the
	/// value all of them being zero stands for.
	///
	/// A bit is a constant where the domain leaves it no choice. The binary
	/// encoding is created if the variable has not been asked for one before.
	pub fn lit_binary_bits<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<(Vec<BoolVal>, Coeff), Unsatisfiable> {
		let binary = self.binary_encoding(db)?;
		Ok((binary.to_vec(), binary.min()))
	}

	/// The steps of a sequential decomposition over the order encoding.
	///
	/// Each step is a domain value paired with the clause that holds unless the
	/// variable has reached it, so that whatever the constraint then demands
	/// can be disjoined onto that clause.
	pub(crate) fn lit_order_steps<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		geq: bool,
	) -> Result<Vec<(Coeff, BoolVal)>, Unsatisfiable> {
		let order = self.order_encoding(db)?;
		let state = self.0.borrow();
		// Collected rather than lazy: holding the borrow across the
		// caller's work fails as soon as a constraint mentions the
		// variable twice.
		Ok(order.iter(&state.domain, geq).collect())
	}

	/// The steps of a sequential decomposition over the direct encoding, which
	/// pin a value where [`IntVar::lit_order_steps`] bounds it.
	pub(crate) fn lit_direct_steps<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		geq: bool,
	) -> Result<Vec<(Coeff, BoolVal)>, Unsatisfiable> {
		let direct = self.direct_encoding(db)?;
		let state = self.0.borrow();
		// Collected, for the reason given on [`IntVar::lit_order_steps`].
		Ok(direct.iter(&state.domain, geq).collect())
	}

	/// The variable as a weighted sum of literals, plus what it is worth when
	/// none of them hold.
	///
	/// Read through whichever encoding it has, so that a constraint wanting
	/// literals rather than integers gets the ones already standing for it.
	pub(crate) fn as_weighted<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<(Vec<(Lit, Coeff)>, Coeff), Unsatisfiable> {
		{
			let state = self.0.borrow();
			match (
				state.direct.as_ref(),
				state.order.as_ref(),
				state.binary.as_ref(),
			) {
				(.., Some(bin)) => return Ok(bin.as_weighted()),
				(Some(dir), ..) => return Ok(dir.as_weighted(&state.domain)),
				(_, Some(ord), _) => return Ok(ord.as_weighted(&state.domain)),
				_ => {}
			}
		}
		// Nothing has been asked of it yet. The binary encoding is the one that
		// costs least to make.
		let bin = self.binary_encoding(db)?;
		Ok(bin.as_weighted())
	}

	/// Whether the variable's literals are settled, so that its domain can no
	/// longer move.
	///
	/// A variable holding any encoding is settled: its literals are out in the
	/// world, and dropping a value would leave nothing to say it cannot hold.
	pub(crate) fn is_committed(&self) -> bool {
		let state = self.0.borrow();
		state.order.is_some() || state.binary.is_some() || state.direct.is_some()
	}

	/// Drop the values below `v` from the domain, reporting whether any went.
	pub(crate) fn set_min(&self, v: Coeff) -> bool {
		debug_assert!(
			!self.is_committed(),
			"the domain of {} cannot move once it is encoded",
			self.label()
		);
		let mut state = self.0.borrow_mut();
		if v <= *state.domain.min().unwrap() {
			return false;
		}
		state.domain.tighten_min(v);
		true
	}

	/// Drop the values above `v` from the domain, reporting whether any went.
	pub(crate) fn set_max(&self, v: Coeff) -> bool {
		debug_assert!(
			!self.is_committed(),
			"the domain of {} cannot move once it is encoded",
			self.label()
		);
		let mut state = self.0.borrow_mut();
		if v >= *state.domain.max().unwrap() {
			return false;
		}
		state.domain.tighten_max(v);
		true
	}

	/// The greatest value the variable can take.
	pub fn max(&self) -> Coeff {
		*self.0.borrow().domain.max().unwrap()
	}

	/// The least value the variable can take.
	pub fn min(&self) -> Coeff {
		*self.0.borrow().domain.min().unwrap()
	}

	/// The label of the variable, which is empty unless tracing is enabled —
	/// nothing else has a use for one, so nothing else pays to store it. Use
	/// the [`Display`] implementation to name a variable in a message, which
	/// falls back to its domain.
	pub fn label(&self) -> String {
		#[cfg(any(feature = "tracing", test))]
		return self.0.borrow().label.clone();
		#[cfg(not(any(feature = "tracing", test)))]
		return String::new();
	}

	/// Give the variable an order encoding it does not have yet.
	///
	/// `already_channelled` says how this encoding is known to stand to the
	/// others already, so that this does not tie again what is tied.
	fn install_order<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		order: OrderEncoding,
		already_channelled: Option<Comparator>,
	) -> Result {
		{
			let mut state = self.0.borrow_mut();
			debug_assert!(
				state.order.is_none(),
				"{} is already order encoded",
				self.label()
			);
			state.order = Some(order);
			// The order encoding is the go-between, so what is said of it is
			// said of both pairs.
			state.channelled = [already_channelled; 2];
			state.lead = state.lead.or(Some(Lead::Order));
		}
		self.reconcile(db)
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
		{
			let mut state = self.0.borrow_mut();
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
		{
			let mut state = self.0.borrow_mut();
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

	/// Create a variable held in an order encoding on literals that already
	/// exist.
	///
	/// There is one literal per value of `domain` beyond the first, in order,
	/// and `literals[i]` must hold exactly when the variable has reached the
	/// `i + 1`'th of them — which means each of them implying the one before.
	/// That chain is taken on trust and not emitted; see [`IntVar::constrain`]
	/// where it needs saying.
	pub fn from_order_encoding<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: impl Into<RangeList<Coeff>>,
		literals: &[Lit],
	) -> Result<Self, Unsatisfiable> {
		let x = Self::new(domain).enforce_consistency(false);
		let order = {
			let state = x.0.borrow();
			OrderEncoding::from_literals(&state.domain, literals.to_vec())
		};
		x.install_order(db, order, None)?;
		Ok(x)
	}

	/// Create a variable from what its order encoding says value by value,
	/// which is what [`IntVar::lit_order_walk`] gives.
	///
	/// Each pair is a value and whether the variable reaches it, least value
	/// first. A settled pair is domain rather than encoding: one that always
	/// holds puts every value below it out of reach, one that never holds does
	/// the same for it and everything above. A view onto another variable's
	/// literals can therefore be taken as it comes, untrimmed.
	pub fn from_order_walk<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		walk: impl IntoIterator<Item = (Coeff, BoolVal)>,
	) -> Result<Self, Unsatisfiable> {
		let (mut values, mut literals) = (Vec::new(), Vec::new());
		for (v, reaches) in walk {
			match reaches {
				// Reached whatever happens, so nothing below it is in reach.
				BoolVal::Const(true) => {
					values.clear();
					literals.clear();
					values.push(v);
				}
				// Never reached, so neither is anything above it.
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

	/// The variable `min + max − x`, which counts the same domain from the
	/// other end.
	///
	/// Its literals are `x`'s: reaching a value from below is `x` failing to
	/// reach past the value that mirrors it. A term with a negative coefficient
	/// is turned around this way, since `c·x` is `c·(min + max) − c·x'`.
	pub fn mirrored<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		x: &IntVar,
	) -> Result<Self, Unsatisfiable> {
		let (min, max) = (x.min(), x.max());
		let walk = x
			.domain()
			.iter()
			.flatten()
			.rev()
			.map(|v| Ok((min + max - v, x.lit_at_most(db, v)?)))
			.collect::<Result<Vec<_>, Unsatisfiable>>()?;
		Self::from_order_walk(db, walk)
	}

	/// Create a variable from what its direct encoding says value by value,
	/// which is what [`IntVar::lit_direct_walk`] gives.
	///
	/// Each pair is a value and whether the variable takes it. A pair that is
	/// already settled is domain rather than encoding: one that always holds
	/// leaves the variable that value and no other, and one that never holds
	/// drops it from the domain.
	///
	/// The literals are taken on trust, as they are by
	/// [`IntVar::from_direct_encoding`], which this builds on.
	pub fn from_direct_walk<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		walk: impl IntoIterator<Item = (Coeff, BoolVal)>,
	) -> Result<Self, Unsatisfiable> {
		let (mut values, mut literals) = (Vec::new(), Vec::new());
		for (v, takes) in walk {
			match takes {
				// Taken whatever happens, so there is nothing else it can be
				// and no literal has to say so.
				BoolVal::Const(true) => return Ok(Self::new(v..=v)),
				// Never taken, so not a value of the variable at all.
				BoolVal::Const(false) => {}
				BoolVal::Lit(l) => {
					values.push(v);
					literals.push(l);
				}
			}
		}
		if values.is_empty() {
			db.contradiction()?;
		}
		let domain = RangeList::from_elements(values);
		Self::from_direct_encoding(db, domain, &literals)
	}

	/// Create a variable held in a direct encoding on literals that already
	/// exist.
	///
	/// There is one literal per value of `domain`, in order, and `literals[i]`
	/// must hold exactly when the variable takes the `i`'th of them — which
	/// means exactly one of them holding. That is taken on trust and not
	/// emitted; see [`IntVar::constrain`] where it needs saying, though it is
	/// worth avoiding, the clauses for it being quadratic in the domain.
	pub fn from_direct_encoding<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: impl Into<RangeList<Coeff>>,
		literals: &[Lit],
	) -> Result<Self, Unsatisfiable> {
		let x = Self::new(domain).enforce_consistency(false);
		let direct = DirectEncoding::from_literals(&x.0.borrow().domain, literals.to_vec());
		x.install_direct(db, direct, None)?;
		Ok(x)
	}

	/// Create a variable held in a binary encoding on bits that already exist.
	///
	/// The bits are those of `value - min`, least significant first, so `min`
	/// is what all of them being zero stands for: the lower bound of `domain`
	/// where the bits were made for it, or zero where they count from there. A
	/// bit may be a constant rather than a literal.
	///
	/// The bits must already stay within `domain`, bounds and holes both, so a
	/// `domain` narrower than they can reach is a claim rather than a
	/// restriction; see [`IntVar::constrain`] to make it one.
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

	/// Give the variable an order encoding on literals that already exist.
	///
	/// The literals mean what they do for [`IntVar::from_order_encoding`], and
	/// are taken on trust in the same way. Where the variable has another
	/// encoding, the channel between the two carries what that one says over to
	/// these; where it has none, see [`IntVar::constrain`].
	///
	/// See [`IntVar::with_binary_encoding`] for `already_channelled`.
	pub fn with_order_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		literals: &[Lit],
		already_channelled: Option<Comparator>,
	) -> Result {
		let order = {
			let state = self.0.borrow();
			OrderEncoding::from_literals(&state.domain, literals.to_vec())
		};
		self.install_order(db, order, already_channelled)
	}

	/// Give the variable a direct encoding on literals that already exist.
	///
	/// The literals mean what they do for [`IntVar::from_direct_encoding`], and
	/// are taken on trust in the same way — a group of at-most-one
	/// pseudo-Boolean terms is the case this is for, its exclusivity being what
	/// the group is. Where the variable has another encoding, the channel
	/// between the two carries what that one says over to these; where it has
	/// none, see [`IntVar::constrain`].
	///
	/// See [`IntVar::with_binary_encoding`] for `already_channelled`.
	pub fn with_direct_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		literals: &[Lit],
		already_channelled: Option<Comparator>,
	) -> Result {
		let direct = DirectEncoding::from_literals(&self.0.borrow().domain, literals.to_vec());
		self.install_direct(db, direct, already_channelled)
	}

	/// Give the variable a binary encoding on bits that already exist.
	///
	/// The bits mean what they do for [`IntVar::from_binary_encoding`], and are
	/// taken on trust in the same way. Another encoding channels what it says
	/// over to these; where there is none, see [`IntVar::constrain`].
	///
	/// `already_channelled` says how these literals already stand to the other
	/// encodings — sharing literals, say, or tied by the caller's own clauses.
	/// [`Comparator::Equal`] says they hold the same value; the other two say
	/// only that this encoding bounds the rest, which is less, so it is still
	/// constrained in its own right. `None` ties whatever is missing, here and
	/// for encodings added later.
	pub fn with_binary_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		bits: &[BoolVal],
		min: Coeff,
		already_channelled: Option<Comparator>,
	) -> Result {
		self.check_bits(bits, min);
		let binary = BinaryEncoding::from_bits(bits.to_vec(), min);
		self.install_binary(db, binary, already_channelled)
	}

	/// Check that bits given for this variable can hold its domain and no more.
	fn check_bits(&self, bits: &[BoolVal], min: Coeff) {
		let domain = &self.0.borrow().domain;
		debug_assert!(
			min <= *domain.min().unwrap(),
			"a binary encoding counts up from {min}, which is past the domain it is for"
		);
		debug_assert_eq!(
			bits.len(),
			BinaryEncoding::required_bits(*domain.max().unwrap() - min),
			"a binary encoding has the bits its domain needs and no more"
		);
	}

	/// Name the variable, so that the literals its encodings create are called
	/// after it.
	///
	/// Nothing is kept and the name is never read unless tracing is enabled,
	/// so this costs no more than building the name did.
	pub fn with_label(self, label: impl Into<String>) -> Self {
		#[cfg(any(feature = "tracing", test))]
		{
			self.0.borrow_mut().label = label.into();
		}
		#[cfg(not(any(feature = "tracing", test)))]
		let _ = label;
		self
	}

	/// Restrict the variable's encodings to its domain.
	///
	/// The order encoding is exact by construction, so this only concerns a
	/// binary one: set it when the variable has to be within its domain in
	/// every model, and leave it unset when the constraints it appears in
	/// already say so and the extra clauses would only repeat them.
	pub fn enforce_consistency(self, enforce: bool) -> Self {
		debug_assert!(
			!self.has_binary_encoding(),
			"the binary encoding of {} is already made, so this would say nothing",
			self.label()
		);
		self.0.borrow_mut().add_consistency = enforce;
		self
	}

	/// Create a variable over `domain`.
	///
	/// Give it a name with [`IntVar::label`] and restrict its encodings to
	/// `domain` with [`IntVar::enforce_consistency`].
	pub fn new(domain: impl Into<RangeList<Coeff>>) -> Self {
		let domain = domain.into();
		debug_assert!(!domain.is_empty(), "an integer variable needs a domain");
		Self(Rc::new(RefCell::new(IntVarState {
			domain,
			#[cfg(any(feature = "tracing", test))]
			label: String::new(),
			// A variable a caller made holds a value of its domain
			// in every model; ones derived here set this as their
			// construction requires.
			add_consistency: true,
			order: None,
			binary: None,
			direct: None,
			channelled: [None; 2],
			constrained: false,
			products: FxHashMap::default(),
			lead: None,
		})))
	}

	/// Whether an encoding being created has to be held to the domain itself.
	///
	/// It does when it is the variable's first, and does not when it is not:
	/// the channel [`Self::reconcile`] is about to build ties it to an encoding
	/// that already holds a value of the domain, whether by clauses here or by
	/// the promise a caller made about its literals.
	fn needs_constraining(&self) -> bool {
		let state = self.0.borrow();
		state.add_consistency
			&& !state.constrained
			&& state.order.is_none()
			&& state.binary.is_none()
			&& state.direct.is_none()
	}

	/// Whether the variable is better held in binary than in order form.
	///
	/// An encoding it already has settles the question: reaching for the other
	/// one would mean paying to channel between them. Otherwise a variable is
	/// held in binary once its domain grows past `cutoff`, and always in order
	/// form when there is no cutoff.
	pub(crate) fn prefers_binary(&self, cutoff: Option<Coeff>) -> bool {
		let state = self.0.borrow();
		match (state.binary.is_some(), state.order.is_some(), cutoff) {
			(true, _, _) => true,
			(_, true, _) => false,
			(_, _, None) => false,
			// Heuristic: past the cutoff the order literals outnumber the bits.
			(_, _, Some(cutoff)) => state.domain.card().unwrap() as Coeff >= cutoff,
		}
	}

	/// The order encoding of the variable, created if this is the first request
	/// for it.
	pub(crate) fn order_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
	) -> Result<OrderEncoding> {
		if let Some(ord) = self.0.borrow().order.as_ref() {
			return Ok(ord.clone());
		}
		let domain = self.0.borrow().domain.clone();
		let ord = OrderEncoding::new(db, &domain, &self.label());
		// Not optional like the other two: without the chain the
		// literals describe no value, so there is nothing to channel.
		ord.consistent(db)?;
		self.0.borrow_mut().constrained = true;

		self.install_order(db, ord.clone(), None)?;
		Ok(ord)
	}

	/// Whether the variable is held in an order encoding.
	pub fn has_order_encoding(&self) -> bool {
		self.0.borrow().order.is_some()
	}

	/// The value the variable takes under an assignment, read through whichever
	/// encoding it was given.
	pub fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		let state = self.0.borrow();
		// Only the leading encoding is known to say what the variable is worth.
		// Another may merely bound it, if what ties them is one-directional.
		match state.lead {
			Some(Lead::Binary) => state.binary.as_ref().unwrap().value(value),
			Some(Lead::Order) => state.order.as_ref().unwrap().value(&state.domain, value),
			Some(Lead::Direct) => state.direct.as_ref().unwrap().value(&state.domain, value),
			// Nothing was ever asked of it, so it can only be its one value.
			None => *state.domain.min().unwrap(),
		}
	}

	/// The number of values in the domain.
	pub fn card(&self) -> usize {
		self.0.borrow().domain.card().unwrap()
	}
}

impl Display for IntVar {
	/// The label of the variable, or where it is held where it has none — which
	/// is every variable at all, unless tracing is enabled to store labels.
	///
	/// The address is what tells one variable from another, which its domain
	/// would not: two variables over the same values are still two variables.
	/// It says nothing across runs, so nothing should be read into it beyond
	/// which occurrences are the same variable.
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.label() {
			label if label.is_empty() => write!(f, "y@{:p}", Rc::as_ptr(&self.0)),
			label => write!(f, "{label}"),
		}
	}
}

impl OrderEncoding {
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

	/// An encoding on literals already created, one for each value of `domain`
	/// beyond the first, in order.
	pub(crate) fn from_literals(domain: &RangeList<Coeff>, x: Vec<Lit>) -> Self {
		debug_assert_eq!(
			x.len() + 1,
			domain.card().unwrap(),
			"an order encoding has a literal for every value but the first"
		);
		Self {
			x: Literals::Explicit(x),
		}
	}

	/// Whether the variable is at least `v`.
	pub(crate) fn lit_at_least(&self, domain: &RangeList<Coeff>, v: Coeff) -> BoolVal {
		if v <= *domain.min().unwrap() {
			BoolVal::Const(true)
		} else if v > *domain.max().unwrap() {
			BoolVal::Const(false)
		} else {
			// The first domain value at or above `v`; the variable reaches `v`
			// exactly when it reaches that value.
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

	/// The steps of a sequential decomposition over this variable.
	///
	/// Each step is a domain value `d` paired with the clause that holds unless
	/// the variable reaches `d` — from below when `geq`, from above otherwise.
	/// Whatever the constraint demands once `d` is reached can therefore just
	/// be disjoined onto that clause.
	///
	/// The step at the far end of the domain guards nothing, since the variable
	/// always reaches it; its clause is `false` and drops out, leaving the
	/// demand unconditional.
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

	/// The single literal of a two-valued variable, which on its own already
	/// distinguishes both of its values.
	pub(crate) fn lit_single(&self) -> Option<Lit> {
		(self.x.len() == 1).then(|| self.x.get(0).unwrap())
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

#[cfg(test)]
pub(crate) mod tests {
	use itertools::Itertools;
	use rangelist::RangeList;
	use traced_test::test;

	use crate::{
		constraint::linear::{Comparator, PosCoeff},
		decision::integer::{lex_geq_const, lex_leq_const, BinaryEncoding, IntVar, Lead},
		helpers::{
			binary_value,
			tests::{all_binary_solutions, binary_literals, expect_file},
		},
		solver::{cadical::Cadical, SolveResult, Solver},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Lit, Valuation,
	};

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

	/// Every model of `cnf`, as the values each of `read` extracts from it.
	fn all_values(cnf: &Cnf, read: &dyn Fn(&dyn Valuation) -> Vec<Coeff>) -> Vec<Vec<Coeff>> {
		let mut slv = Cadical::from(cnf);
		let vars = cnf.get_variables();
		let mut solutions = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			solutions.push(read(&value));
			let no_good: Vec<_> = vars
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
		solutions.sort();
		solutions
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
	fn channelled_encodings_agree_on_every_value() {
		for domain in test_domains() {
			for bin_first in [false, true] {
				let mut cnf = Cnf::default();
				let x = IntVar::new(domain.clone())
					.enforce_consistency(true)
					.with_label("x");
				// Whichever encoding is asked for second is the
				// one that channels, so the order they are
				// asked in must not matter.
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
				// Exactly the domain, once each and read alike:
				// a disagreement shows up as an extra row, a
				// missing one, or one whose entries differ.
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
	fn encodings_are_created_once() {
		let domain = RangeList::from_elements([0, 1, 3]);
		let mut cnf = Cnf::default();
		let x = IntVar::new(domain)
			.enforce_consistency(true)
			.with_label("x");

		let _ = x.order_encoding(&mut cnf).unwrap();
		let _ = x.binary_encoding(&mut cnf).unwrap();
		let (vars, clauses) = (cnf.num_vars(), cnf.num_clauses());

		// Asking again hands back what is already there: no new literals, and
		// in particular no second round of channelling clauses.
		let _ = x.order_encoding(&mut cnf).unwrap();
		let _ = x.binary_encoding(&mut cnf).unwrap();
		assert_eq!((cnf.num_vars(), cnf.num_clauses()), (vars, clauses));
	}

	#[test]
	fn a_detected_variable_encodes_onto_the_literals_it_was_found_on() {
		// An integer recovered from a constraint encodes onto the
		// literals already there, and still channels like any other.
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
	fn a_variable_built_on_given_literals_takes_exactly_its_domain() {
		// Each constructor must make its literals stand for a value:
		// one order literal per step, one direct per value, bits enough
		// to reach the top.
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
					let state = x.0.borrow();
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
					let state = x.0.borrow();
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
	fn a_question_the_domain_settles_costs_nothing() {
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();
			let (min, max) = (values[0], values[values.len() - 1]);
			let mut cnf = Cnf::default();
			let x = IntVar::new(domain.clone());

			assert_eq!(x.lit_at_least(&mut cnf, min).unwrap(), BoolVal::Const(true));
			assert_eq!(
				x.lit_at_least(&mut cnf, max + 1).unwrap(),
				BoolVal::Const(false)
			);
			assert_eq!(x.lit_at_most(&mut cnf, max).unwrap(), BoolVal::Const(true));
			assert_eq!(
				x.lit_at_most(&mut cnf, min - 1).unwrap(),
				BoolVal::Const(false)
			);
			assert_eq!(
				x.lit_equals(&mut cnf, max + 1).unwrap(),
				BoolVal::Const(false)
			);
			assert_eq!(
				cnf.num_vars(),
				0,
				"nothing had to be encoded to answer over {domain:?}"
			);
		}
	}

	#[test]
	fn every_way_of_reading_a_variable_agrees() {
		let holds = |b: &BoolVal, v: &dyn Valuation| match b {
			BoolVal::Const(c) => *c,
			BoolVal::Lit(l) => v.value(*l),
		};
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();
			let mut cnf = Cnf::default();
			let x = IntVar::new(domain.clone());

			// Asking all three ways ties them together, which is what makes
			// them agree in the first place.
			let reaches = x.lit_order_walk(&mut cnf).unwrap().collect_vec();
			let takes = x.lit_direct_walk(&mut cnf).unwrap().collect_vec();
			let (bits, min) = x.lit_binary_bits(&mut cnf).unwrap();
			assert_eq!(reaches.len(), values.len());
			assert_eq!(takes.len(), values.len());

			let solutions = all_values(&cnf, &|v| {
				vec![
					reaches
						.iter()
						.filter(|(_, b)| holds(b, v))
						.map(|&(d, _)| d)
						.max()
						.expect("the variable reaches its lowest value"),
					takes
						.iter()
						.find(|(_, b)| holds(b, v))
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

	#[test]
	fn an_end_of_the_domain_is_taken_by_reaching_it() {
		// Taking the highest value is reaching it and taking the lowest
		// is failing to reach the next, so an order encoding answers
		// both alone.
		let holds = |b: BoolVal, v: &dyn Valuation| match b {
			BoolVal::Const(c) => c,
			BoolVal::Lit(l) => v.value(l),
		};
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();
			let (min, max) = (values[0], values[values.len() - 1]);
			let mut cnf = Cnf::default();
			let x = IntVar::new(domain.clone());
			let _ = x.lit_at_least(&mut cnf, values[1]).unwrap();

			let vars_before = cnf.num_vars();
			let is_min = x.lit_equals(&mut cnf, min).unwrap();
			let is_max = x.lit_equals(&mut cnf, max).unwrap();
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
	fn a_variable_with_one_value_costs_nothing() {
		// A constant reaches its one value, takes it, and has no bits to say
		// so with — none of which any literal has to stand for.
		for k in [-3, 0, 7] {
			let mut cnf = Cnf::default();
			let x = IntVar::new(k..=k).enforce_consistency(true);

			assert_eq!(x.lit_at_least(&mut cnf, k).unwrap(), BoolVal::Const(true));
			assert_eq!(x.lit_at_most(&mut cnf, k).unwrap(), BoolVal::Const(true));
			assert_eq!(x.lit_equals(&mut cnf, k).unwrap(), BoolVal::Const(true));
			assert_eq!(
				x.lit_order_walk(&mut cnf).unwrap().collect_vec(),
				vec![(k, BoolVal::Const(true))]
			);
			assert_eq!(
				x.lit_direct_walk(&mut cnf).unwrap().collect_vec(),
				vec![(k, BoolVal::Const(true))]
			);
			assert_eq!(x.lit_binary_bits(&mut cnf).unwrap(), (Vec::new(), k));
			assert_eq!(x.value(&|_: Lit| false), k);

			assert_eq!(
				(cnf.num_vars(), cnf.num_clauses()),
				(0, 0),
				"the constant {k} cost literals or clauses"
			);
		}
	}

	#[test]
	fn a_walk_wider_than_the_variable_is_trimmed_to_it() {
		// Values outside the domain give settled answers, and a walk
		// built from them has to come back to the domain rather than
		// keep them.
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3).with_label("x");
		let walk = (-2..=6)
			.map(|v| (v, x.lit_at_least(&mut cnf, v).unwrap()))
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
	fn a_direct_walk_settles_into_the_domain_too() {
		// A value never taken is not a value, and one always taken leaves no
		// others — so a walk over them says what the variable is.
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3).with_label("x");
		let walk = (-2..=6)
			.map(|v| (v, x.lit_equals(&mut cnf, v).unwrap()))
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

		// A value that always holds is the whole of the variable.
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
	fn a_tied_encoding_is_constrained_through_its_channel() {
		// A channel is a biconditional, so constraining the lead says
		// it of everything tied to it; saying it again would be
		// quadratic.
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

		// And it really is enough: both views read the same value, and only
		// values of the domain.
		let read = {
			let (d, state) = (domain.clone(), x.0.borrow());
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
	fn only_an_equal_channel_spares_the_encoding_it_reaches() {
		// Clauses making two encodings equal stand in for the channel;
		// ones that only bound one by the other do not, so it is built
		// anyway.
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
	fn an_encoding_made_beside_another_is_told_nothing() {
		// A created encoding is held to the domain only where it is the
		// first; beside an existing one the channel carries that, at
		// the same cost.
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
	fn what_the_encodings_cost() {
		// Sizes over every combination of encodings, to catch
		// channelling growing past a clause per value and the binary
		// cliff at the second view.
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

	#[test]
	fn constraining_the_lead_holds_the_variable_to_its_domain() {
		// The lead is what the value is read from, so it is what gets
		// constrained: past the bounds and the holes both, whichever of
		// the three leads.
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
			x.0.borrow().lead,
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
			let (d, state) = (domain.clone(), x.0.borrow());
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
	fn the_value_is_read_from_the_encoding_that_leads() {
		// Every encoding but the lead is somewhere between a bound and
		// an equal, and the binary one leads where it can, being
		// cheapest to read.
		let mut cnf = Cnf::default();
		let x = IntVar::new(0..=3);
		assert_eq!(x.0.borrow().lead, None, "nothing has been asked of it yet");
		let _ = x.direct_encoding(&mut cnf).unwrap();
		assert_eq!(x.0.borrow().lead, Some(Lead::Direct), "the first encoding");
		let _ = x.order_encoding(&mut cnf).unwrap();
		assert_eq!(
			x.0.borrow().lead,
			Some(Lead::Direct),
			"the order encoding is no cheaper to read, so the lead stays put"
		);
		let _ = x.binary_encoding(&mut cnf).unwrap();
		assert_eq!(
			x.0.borrow().lead,
			Some(Lead::Binary),
			"equal to the order encoding, which is equal to the direct one"
		);
		assert_eq!(
			all_values(&cnf, &|v: &dyn Valuation| vec![x.value(v)]),
			(0..=3).map(|d| vec![d]).collect_vec()
		);
	}
}
