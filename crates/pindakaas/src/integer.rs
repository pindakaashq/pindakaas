//! Integer decision variables, their Boolean encodings, and the bit-level
//! constraints shared between them.

use std::{
	cell::RefCell,
	hash::{Hash, Hasher},
	ops::Bound,
	rc::{Rc, Weak},
};

use itertools::{Either, Itertools};
use rangelist::{IntervalIterator, RangeList};
use rustc_hash::FxHashMap;

use crate::{
	bool_linear::{Comparator, PosCoeff},
	helpers::{as_binary, bit, new_named_lit, new_named_var_range},
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

/// The binary encoding of an integer variable.
///
/// The bits are those of `value - min`, least significant first. Where that
/// count starts belongs to the encoding rather than to the library: at the
/// variable's lower bound, so that the bound costs nothing to enforce, or at
/// zero where the bits were found on a caller's own literals and already count
/// from there. Both turn up within a single constraint, so it cannot be settled
/// once for everything.
///
/// A bit may be fixed rather than free, which is what lets a shifted,
/// complemented or otherwise derived encoding be expressed without introducing
/// literals for it.
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
/// A variable may hold several encodings at once. They are created on first
/// request rather than up front, and the moment a second one appears it is
/// channelled against the first, so that every view of the variable agrees on
/// its value. A constraint can therefore ask for whichever view suits it — the
/// order literals for a sequential decomposition, the bits for an adder —
/// without having to commit to one in advance or introduce a second variable
/// to hold the other.
///
/// Variables are shared between the constraints that mention them, as
/// `IntVar`.
#[derive(Clone, Debug)]
pub struct IntVar(Rc<RefCell<IntVarState>>);

/// A variable by identity rather than by hold, for keying what has been built
/// for it.
///
/// A `Weak` keeps the allocation alive after the last handle is dropped, so its
/// address cannot be handed to a later variable while a key to it still exists
/// — which a raw pointer could not promise.
#[derive(Clone, Debug)]
pub(crate) struct IntVarKey(Weak<RefCell<IntVarState>>);

impl Eq for IntVarKey {}

impl Hash for IntVarKey {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.0.as_ptr().hash(state);
	}
}

impl PartialEq for IntVarKey {
	fn eq(&self, other: &Self) -> bool {
		Weak::ptr_eq(&self.0, &other.0)
	}
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
	/// Which pairs of encodings have been tied together already. With three of
	/// them, "the channel fires when the second appears" no longer says enough.
	channelled: [bool; 2],
	/// Literals to reuse as `x ≥ v` when the order encoding is created, rather
	/// than introducing a fresh one.
	order_views: FxHashMap<Coeff, Lit>,
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

	/// Restrict the encoding to the values on one side of `v`.
	pub(crate) fn encode_bound<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		cmp: Comparator,
		v: Coeff,
		domain: &RangeList<Coeff>,
	) -> Result {
		let (lb, ub) = (*domain.min().unwrap(), *domain.max().unwrap());
		match cmp {
			Comparator::LessEq if v >= ub => Ok(()),
			Comparator::LessEq if v < lb => db.contradiction(),
			Comparator::LessEq => lex_leq_const(
				db,
				&self.x.to_vec(),
				PosCoeff::new(v - self.min),
				self.bits(),
			),
			Comparator::GreaterEq if v <= lb => Ok(()),
			Comparator::GreaterEq if v > ub => db.contradiction(),
			Comparator::GreaterEq => lex_geq_const(
				db,
				&self.x.to_vec(),
				PosCoeff::new(v - self.min),
				self.bits(),
			),
			Comparator::Equal => unreachable!("an equality is split before it is encoded"),
		}
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
				if self.0.borrow().add_consistency {
					bin.consistent(db, &domain)?;
				}
				bin
			}
		};

		// A two-valued variable needs no tying: its order literal is already
		// the whole of its binary encoding.
		self.install_binary(db, bin.clone(), !derived)?;
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
				(Some(ord), Some(bin)) if !state.channelled[0] => {
					let all = (state.domain.clone(), ord.clone(), bin.clone());
					state.channelled[0] = true;
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
		self.channel_direct(db)
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
		// One value and no more, which the order encoding gets from its chain
		// but the direct encoding has to be told.
		dir.consistent(db)?;
		self.install_direct(db, dir.clone(), true)?;
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
				(Some(ord), Some(dir)) if !state.channelled[1] => {
					let all = (ord.clone(), dir.clone(), state.domain.clone());
					state.channelled[1] = true;
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

	/// The variable's identity, for keying what has been built for it.
	pub(crate) fn key(&self) -> IntVarKey {
		IntVarKey(Rc::downgrade(&self.0))
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
		// Collected rather than handed back lazily: the borrow cannot outlive
		// this call, and holding one while the caller works through the steps
		// is what would fail the moment a constraint mentioned this variable
		// twice.
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
				(Some(dir), ..) => return Ok(dir.as_weighted(&state.domain)),
				(_, Some(ord), _) => return Ok(ord.as_weighted(&state.domain)),
				(.., Some(bin)) => return Ok(bin.as_weighted()),
				_ => {}
			}
		}
		// Nothing has been asked of it yet. The order encoding is the one that
		// costs least to make, and nothing at all where the literals for it are
		// already there.
		let ord = self.order_encoding(db)?;
		Ok(ord.as_weighted(&self.0.borrow().domain))
	}

	/// Whether the variable's literals are settled, so that its domain can no
	/// longer move.
	///
	/// An encoding that exists is settled for the obvious reason. So is one
	/// that does not exist yet but is spoken for: a variable found on literals
	/// that were already there cannot drop a value, because the literal
	/// standing for it is out in the world regardless, and dropping the value
	/// would leave nothing to say it cannot hold.
	pub(crate) fn is_committed(&self) -> bool {
		let state = self.0.borrow();
		state.order.is_some()
			|| state.binary.is_some()
			|| state.direct.is_some()
			|| !state.order_views.is_empty()
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

	/// The label of the variable, which is empty unless tracing is enabled.
	pub fn label(&self) -> String {
		#[cfg(any(feature = "tracing", test))]
		return self.0.borrow().label.clone();
		#[cfg(not(any(feature = "tracing", test)))]
		return String::new();
	}

	/// Give the variable an order encoding it does not have yet.
	///
	/// `channel` says whether this encoding should ever be tied to the others
	/// by clauses — not only to those already there, but to any added later.
	/// It should be, unless something else already keeps them in step: the
	/// encodings sharing their literals, say, or a caller that has constrained
	/// them itself.
	fn install_order<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		order: OrderEncoding,
		channel: bool,
	) -> Result {
		{
			let mut state = self.0.borrow_mut();
			debug_assert!(
				state.order.is_none(),
				"{} is already order encoded",
				self.label()
			);
			state.order = Some(order);
			// The order encoding is the go-between, so declining to channel it
			// settles both pairs.
			if !channel {
				state.channelled = [true; 2];
			}
		}
		self.reconcile(db)
	}

	/// Give the variable a binary encoding it does not have yet.
	///
	/// See [`IntVar::with_order_encoding`] for what `channel` decides.
	fn install_binary<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		binary: BinaryEncoding,
		channel: bool,
	) -> Result {
		{
			let mut state = self.0.borrow_mut();
			debug_assert!(
				state.binary.is_none(),
				"{} is already binary encoded",
				self.label()
			);
			state.binary = Some(binary);
			state.channelled[0] |= !channel;
		}
		self.reconcile(db)
	}

	/// Give the variable a direct encoding it does not have yet.
	///
	/// See [`IntVar::with_order_encoding`] for what `channel` decides.
	fn install_direct<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		direct: DirectEncoding,
		channel: bool,
	) -> Result {
		{
			let mut state = self.0.borrow_mut();
			debug_assert!(
				state.direct.is_none(),
				"{} is already directly encoded",
				self.label()
			);
			state.direct = Some(direct);
			state.channelled[1] |= !channel;
		}
		self.reconcile(db)
	}

	/// Create a variable held in an order encoding on literals that already
	/// exist.
	///
	/// There is one literal per value of `domain` beyond the first, in order,
	/// and `literals[i]` holds exactly when the variable has reached the
	/// `i + 1`'th of them. The implication chain between them is emitted here,
	/// since without it the literals do not stand for a value at all; give them
	/// to [`IntVar::with_order_encoding`] instead when your own constraints
	/// already provide it.
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
		order.consistent(db)?;
		x.install_order(db, order, true)?;
		Ok(x)
	}

	/// Create a variable from what its order encoding says value by value,
	/// which is what [`IntVar::lit_order_walk`] gives.
	///
	/// Each pair is a value and whether the variable reaches it, least value
	/// first. A pair that is already settled is domain rather than encoding:
	/// one that always holds puts every value below it out of reach, and one
	/// that never holds does the same for it and everything above. So a view
	/// onto another variable's literals can be taken as it comes, without the
	/// ends that fall outside this variable's domain having to be trimmed
	/// first.
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
	/// holds exactly when the variable takes the `i`'th of them. That exactly
	/// one of them holds is emitted here, since without it the literals do not
	/// stand for a value at all; give them to [`IntVar::with_direct_encoding`]
	/// instead when your own constraints already provide it, which is worth
	/// doing — the clauses for it are quadratic in the size of the domain.
	pub fn from_direct_encoding<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: impl Into<RangeList<Coeff>>,
		literals: &[Lit],
	) -> Result<Self, Unsatisfiable> {
		let x = Self::new(domain).enforce_consistency(false);
		let direct = DirectEncoding::from_literals(&x.0.borrow().domain, literals.to_vec());
		direct.consistent(db)?;
		x.install_direct(db, direct, true)?;
		Ok(x)
	}

	/// Create a variable held in a binary encoding on bits that already exist.
	///
	/// The bits are those of `value - min`, least significant first, so `min`
	/// is what all of them being zero stands for: the lower bound of `domain`
	/// where the bits were made for it, or zero where they count from there. A
	/// bit may be a constant rather than a literal.
	///
	/// The bits are restricted to `domain` here, bounds and holes both, since
	/// nothing else says they hold a value of it; give them to
	/// [`IntVar::with_binary_encoding`] instead when your own constraints
	/// already do.
	pub fn from_binary_encoding<Db: ClauseDatabase + ?Sized>(
		db: &mut Db,
		domain: impl Into<RangeList<Coeff>>,
		bits: &[BoolVal],
		min: Coeff,
	) -> Result<Self, Unsatisfiable> {
		let x = Self::new(domain).enforce_consistency(false);
		let binary = BinaryEncoding::from_bits(bits.to_vec(), min);
		binary.consistent(db, &x.0.borrow().domain.clone())?;
		x.install_binary(db, binary, true)?;
		Ok(x)
	}

	/// Give the variable an order encoding on literals that already exist.
	///
	/// The literals mean what they do for [`IntVar::from_order_encoding`], but
	/// nothing is emitted to make them mean it: the caller's own constraints
	/// must, or the channel to an encoding the variable already has must.
	///
	/// See [`IntVar::with_binary_encoding`] for what `channel` decides.
	pub fn with_order_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		literals: &[Lit],
		channel: bool,
	) -> Result {
		let order = {
			let state = self.0.borrow();
			OrderEncoding::from_literals(&state.domain, literals.to_vec())
		};
		self.install_order(db, order, channel)
	}

	/// Give the variable a direct encoding on literals that already exist.
	///
	/// The literals mean what they do for [`IntVar::from_direct_encoding`], but
	/// nothing is emitted to make them mean it: the caller's own constraints
	/// must, or the channel to an encoding the variable already has must. A
	/// group of at-most-one pseudo-Boolean terms is the case this is for, its
	/// exclusivity being what the group is.
	///
	/// See [`IntVar::with_binary_encoding`] for what `channel` decides.
	pub fn with_direct_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		literals: &[Lit],
		channel: bool,
	) -> Result {
		let direct = DirectEncoding::from_literals(&self.0.borrow().domain, literals.to_vec());
		self.install_direct(db, direct, channel)
	}

	/// Give the variable a binary encoding on bits that already exist.
	///
	/// The bits mean what they do for [`IntVar::from_binary_encoding`], but
	/// nothing is emitted to make them mean it: the caller's own constraints
	/// must, or the channel to an encoding the variable already has must.
	///
	/// `channel` says whether this encoding should ever be tied to the others
	/// by clauses — not only to those the variable has now, but to any it is
	/// given later. It should be, unless something already keeps them in step:
	/// the encodings sharing their literals, say. Note that tying two encodings
	/// costs clauses in proportion to the size of the domain, so a variable
	/// large enough to want a binary encoding is one to keep from acquiring a
	/// second view at all.
	pub fn with_binary_encoding<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		bits: &[BoolVal],
		min: Coeff,
		channel: bool,
	) -> Result {
		self.install_binary(db, BinaryEncoding::from_bits(bits.to_vec(), min), channel)
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
			// A variable a caller made is expected to hold a value of its
			// domain in every model, without anything else having to say so.
			// Ones derived here set it as their construction requires.
			add_consistency: true,
			order: None,
			binary: None,
			direct: None,
			channelled: [false; 2],
			order_views: FxHashMap::default(),
		})))
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
		let (domain, views) = {
			let state = self.0.borrow();
			(state.domain.clone(), state.order_views.clone())
		};

		let ord = OrderEncoding::new(db, &domain, &views, &self.label());
		ord.consistent(db)?;

		self.install_order(db, ord.clone(), true)?;
		Ok(ord)
	}

	/// Whether the variable has been given an order encoding.
	#[cfg(test)]
	pub fn has_order_encoding(&self) -> bool {
		self.0.borrow().order.is_some()
	}

	/// The value the variable takes under an assignment, read through whichever
	/// encoding it was given.
	pub fn value<F: crate::Valuation + ?Sized>(&self, value: &F) -> Coeff {
		let state = self.0.borrow();
		match (
			state.order.as_ref(),
			state.binary.as_ref(),
			state.direct.as_ref(),
		) {
			(_, Some(bin), _) => bin.value(value),
			(Some(ord), _, _) => ord.value(&state.domain, value),
			(_, _, Some(dir)) => dir.value(&state.domain, value),
			// Nothing was ever asked of it, so it can only be its one value.
			_ => *state.domain.min().unwrap(),
		}
	}

	/// The number of values in the domain.
	pub fn card(&self) -> usize {
		self.0.borrow().domain.card().unwrap()
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
		views: &FxHashMap<Coeff, Lit>,
		_label: &str,
	) -> Self {
		let vals = || domain.iter().flatten().skip(1);
		let x = if views.is_empty() {
			// Nothing to reuse, so the literals can be taken in one block.
			Literals::Range(new_named_var_range!(db, vals().count(), |i| {
				format!("{_label}≥{}", vals().nth(i).unwrap())
			}))
		} else {
			Literals::Explicit(
				vals()
					.map(|v| {
						views
							.get(&v)
							.copied()
							.unwrap_or_else(|| new_named_lit!(db, format!("{_label}≥{v}")))
					})
					.collect(),
			)
		};
		Self { x }
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
		bool_linear::PosCoeff,
		helpers::{
			binary_value,
			tests::{all_binary_solutions, binary_literals},
		},
		integer::{lex_geq_const, lex_leq_const, BinaryEncoding, IntVar},
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
				// The order the encodings are asked for must not matter: whichever
				// arrives second is the one that triggers the channelling.
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
				// Exactly the domain, once each, with both views reading alike. A
				// disagreement or a value outside the domain would show up as an
				// extra row, a missing one, or a row whose two entries differ.
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

		// Asking again hands back what is already there: no new literals, and in
		// particular no second round of channelling clauses.
		let _ = x.order_encoding(&mut cnf).unwrap();
		let _ = x.binary_encoding(&mut cnf).unwrap();
		assert_eq!((cnf.num_vars(), cnf.num_clauses()), (vars, clauses));
	}

	#[test]
	fn a_detected_variable_encodes_onto_the_literals_it_was_found_on() {
		// An integer recovered from a constraint that already mentions its
		// literals has to encode onto those rather than introduce its own, and
		// must still channel like any other variable.
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
		// Each constructor is handed literals of its own and must make them
		// stand for a value: one order literal per step, one direct literal per
		// value, enough bits to reach the top.
		for domain in test_domains() {
			let values: Vec<Coeff> = domain.iter().flatten().collect();

			let mut cnf = Cnf::default();
			let lits = cnf
				.new_var_range(values.len() - 1)
				.iter_lits()
				.collect_vec();
			let x = IntVar::from_order_encoding(&mut cnf, domain.clone(), &lits).unwrap();
			assert_eq!(
				all_values(&cnf, &|v| vec![x.value(v)]),
				values.iter().map(|&d| vec![d]).collect_vec(),
				"an order encoding on given literals over {domain:?}"
			);

			let mut cnf = Cnf::default();
			let lits = cnf.new_var_range(values.len()).iter_lits().collect_vec();
			let x = IntVar::from_direct_encoding(&mut cnf, domain.clone(), &lits).unwrap();
			assert_eq!(
				all_values(&cnf, &|v| vec![x.value(v)]),
				values.iter().map(|&d| vec![d]).collect_vec(),
				"a direct encoding on given literals over {domain:?}"
			);

			let mut cnf = Cnf::default();
			let (min, max) = (values[0], values[values.len() - 1]);
			let bits = binary_literals(&mut cnf, BinaryEncoding::required_bits(max - min));
			let x = IntVar::from_binary_encoding(&mut cnf, domain.clone(), &bits, min).unwrap();
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
			let bits = binary_literals(&mut cnf, BinaryEncoding::required_bits(max - min));
			x.with_binary_encoding(&mut cnf, &bits, min, true).unwrap();
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
			let ord_lits = cnf
				.new_var_range(values.len() - 1)
				.iter_lits()
				.collect_vec();
			x.with_order_encoding(&mut cnf, &ord_lits, true).unwrap();
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
		// Taking the highest value is reaching it, and taking the lowest is
		// failing to reach the next — so an order encoding answers both without
		// a direct encoding having to be built and tied to it.
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
		// Asking about values outside the domain gives settled answers, and a
		// walk built from them has to come back to the domain they settle to
		// rather than keeping them as values.
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
}
