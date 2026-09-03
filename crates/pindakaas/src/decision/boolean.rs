//! Boolean decision variables: the literals a formula is written over.

use std::{
	cmp::Ordering,
	fmt::{self, Display},
	iter::FusedIterator,
	num::NonZeroI32,
	ops::{Add, BitAnd, BitOr, BitXor, Bound, Mul, Not, RangeBounds, RangeInclusive},
};

use itertools::Itertools;

use crate::{
	constraint::{linear::LinExp, propositional_logic::Formula},
	helpers::subscript_number,
	Coeff,
};

/// A helper type used to represent a Boolean value that can be either a literal
/// for a Boolean decision variable, or a constant Boolean value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[expect(
	variant_size_differences,
	reason = "bool is 1 byte, but Lit will always require more"
)]
pub enum BoolVal {
	/// A constant Boolean value.
	Const(bool),
	/// A literal for a Boolean decision variable.
	Lit(Lit),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
/// Literal is type that can be use to represent Boolean decision variables and
/// their negations
pub struct Lit(pub(crate) NonZeroI32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// A canonical implementation of a Boolean decision variable, independent of
/// negation.
pub struct Var(pub(crate) NonZeroI32);

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
/// A continuous range of Boolean variables.
///
/// This is a representation that is used to represent a range of variables in a
/// more compact way.
pub struct VarRange {
	pub(crate) start: Var,
	pub(crate) end: Var,
}

impl BitAnd<BoolVal> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitand(self, rhs: BoolVal) -> Self::Output {
		match (self, rhs) {
			(BoolVal::Const(a), BoolVal::Const(b)) => Formula::Atom((a & b).into()),
			(BoolVal::Lit(a), BoolVal::Lit(b)) => (a & b).into(),
			(BoolVal::Lit(a), BoolVal::Const(b)) | (BoolVal::Const(b), BoolVal::Lit(a)) => {
				Formula::Atom(a & b)
			}
		}
	}
}

impl BitAnd<Lit> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitand(self, rhs: Lit) -> Self::Output {
		self & BoolVal::Lit(rhs)
	}
}

impl BitAnd<bool> for BoolVal {
	type Output = BoolVal;

	fn bitand(self, rhs: bool) -> Self::Output {
		match self {
			BoolVal::Const(b) => (b & rhs).into(),
			BoolVal::Lit(l) if rhs => (l).into(),
			BoolVal::Lit(_) => false.into(),
		}
	}
}

impl BitOr<BoolVal> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitor(self, rhs: BoolVal) -> Self::Output {
		match (self, rhs) {
			(BoolVal::Const(a), BoolVal::Const(b)) => Formula::Atom((a | b).into()),
			(BoolVal::Lit(a), BoolVal::Lit(b)) => (a | b).into(),
			(BoolVal::Lit(a), BoolVal::Const(b)) | (BoolVal::Const(b), BoolVal::Lit(a)) => {
				Formula::Atom(a | b)
			}
		}
	}
}

impl BitOr<Lit> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitor(self, rhs: Lit) -> Self::Output {
		self | BoolVal::Lit(rhs)
	}
}

impl BitOr<bool> for BoolVal {
	type Output = BoolVal;

	fn bitor(self, rhs: bool) -> Self::Output {
		match self {
			BoolVal::Const(b) => (b | rhs).into(),
			BoolVal::Lit(_) if rhs => true.into(),
			BoolVal::Lit(_) => self,
		}
	}
}

impl BitXor<BoolVal> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitxor(self, rhs: BoolVal) -> Self::Output {
		match (self, rhs) {
			(BoolVal::Const(a), BoolVal::Const(b)) => Formula::Atom((a ^ b).into()),
			(BoolVal::Lit(a), BoolVal::Lit(b)) => {
				Formula::Xor(vec![Formula::Atom(a.into()), Formula::Atom(b.into())])
			}
			(BoolVal::Lit(a), BoolVal::Const(b)) | (BoolVal::Const(b), BoolVal::Lit(a)) => {
				Formula::Atom((a ^ b).into())
			}
		}
	}
}

impl BitXor<Lit> for BoolVal {
	type Output = Formula<BoolVal>;

	fn bitxor(self, rhs: Lit) -> Self::Output {
		self ^ BoolVal::Lit(rhs)
	}
}

impl BitXor<bool> for BoolVal {
	type Output = BoolVal;

	fn bitxor(self, rhs: bool) -> Self::Output {
		if rhs {
			!self
		} else {
			self
		}
	}
}

impl Display for BoolVal {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			BoolVal::Const(b) => write!(f, "{b}"),
			BoolVal::Lit(l) => write!(f, "{l}"),
		}
	}
}

impl From<Lit> for BoolVal {
	fn from(value: Lit) -> Self {
		BoolVal::Lit(value)
	}
}

impl From<Var> for BoolVal {
	fn from(value: Var) -> Self {
		BoolVal::Lit(value.into())
	}
}

impl From<bool> for BoolVal {
	fn from(value: bool) -> Self {
		BoolVal::Const(value)
	}
}

impl Not for BoolVal {
	type Output = BoolVal;

	fn not(self) -> Self::Output {
		match self {
			BoolVal::Lit(l) => (!l).into(),
			BoolVal::Const(b) => (!b).into(),
		}
	}
}

impl Add<Lit> for Coeff {
	type Output = LinExp;

	fn add(self, rhs: Lit) -> Self::Output {
		rhs + self
	}
}

impl Mul<Lit> for Coeff {
	type Output = LinExp;

	fn mul(self, rhs: Lit) -> Self::Output {
		rhs * self
	}
}

impl Lit {
	/// Coerce a non-zero integer into a literal.
	///
	/// ### Warning
	/// This method is only safe to use if the input integer is known to be a
	/// integer coerced from a literal part of the same formula. Otherwise, the
	/// usage of the literal may lead to undefined behavior.
	pub fn from_raw(value: NonZeroI32) -> Lit {
		Lit(value)
	}

	/// Returns whether the literal is a negation of the underlying variable.
	pub fn is_negated(&self) -> bool {
		self.0.is_negative()
	}

	/// Returns the underlying variable of the literal, whether negated or not.
	pub fn var(&self) -> Var {
		Var(self.0.abs())
	}
}

impl Add for Lit {
	type Output = LinExp;

	fn add(self, rhs: Self) -> Self::Output {
		LinExp::from_terms(&[(self, 1), (rhs, 1)])
	}
}

impl Add<Coeff> for Lit {
	type Output = LinExp;

	fn add(self, rhs: Coeff) -> Self::Output {
		LinExp::from_terms(&[(self, 1)]) + rhs
	}
}

impl BitAnd<BoolVal> for Lit {
	type Output = Formula<BoolVal>;

	fn bitand(self, rhs: BoolVal) -> Self::Output {
		rhs & self
	}
}

impl BitAnd<Lit> for Lit {
	type Output = Formula<Lit>;

	fn bitand(self, rhs: Lit) -> Self::Output {
		Formula::And(vec![Formula::Atom(self), Formula::Atom(rhs)])
	}
}

impl BitAnd<bool> for Lit {
	type Output = BoolVal;

	fn bitand(self, rhs: bool) -> Self::Output {
		if rhs {
			self.into()
		} else {
			false.into()
		}
	}
}

impl BitOr<BoolVal> for Lit {
	type Output = Formula<BoolVal>;

	fn bitor(self, rhs: BoolVal) -> Self::Output {
		rhs | self
	}
}

impl BitOr<Lit> for Lit {
	type Output = Formula<Lit>;

	fn bitor(self, rhs: Lit) -> Self::Output {
		Formula::Or(vec![Formula::Atom(self), Formula::Atom(rhs)])
	}
}

impl BitOr<bool> for Lit {
	type Output = BoolVal;

	fn bitor(self, rhs: bool) -> Self::Output {
		if rhs {
			true.into()
		} else {
			self.into()
		}
	}
}

impl BitXor<BoolVal> for Lit {
	type Output = Formula<BoolVal>;

	fn bitxor(self, rhs: BoolVal) -> Self::Output {
		rhs ^ self
	}
}

impl BitXor<Lit> for Lit {
	type Output = Formula<Lit>;

	fn bitxor(self, rhs: Lit) -> Self::Output {
		Formula::Xor(vec![Formula::Atom(self), Formula::Atom(rhs)])
	}
}

impl BitXor<bool> for Lit {
	type Output = Lit;

	fn bitxor(self, rhs: bool) -> Self::Output {
		if rhs {
			!self
		} else {
			self
		}
	}
}

impl Display for Lit {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}{}",
			if self.is_negated() { "¬" } else { "" },
			self.var()
		)
	}
}

impl From<Var> for Lit {
	fn from(value: Var) -> Self {
		Lit(value.0)
	}
}

impl Mul<Coeff> for Lit {
	type Output = LinExp;

	fn mul(self, rhs: Coeff) -> Self::Output {
		LinExp::from_terms(&[(self, rhs)])
	}
}

impl Not for Lit {
	type Output = Lit;

	fn not(self) -> Self::Output {
		Lit(-self.0)
	}
}

impl Ord for Lit {
	fn cmp(&self, other: &Self) -> Ordering {
		match self.var().cmp(&other.var()) {
			Ordering::Equal => (self.is_negated()).cmp(&other.is_negated()),
			r => r,
		}
	}
}

impl PartialOrd for Lit {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl From<Lit> for NonZeroI32 {
	fn from(val: Lit) -> Self {
		val.0
	}
}

impl From<Var> for NonZeroI32 {
	fn from(val: Var) -> Self {
		val.0
	}
}

impl Var {
	pub(crate) const MAX_VARS: usize = NonZeroI32::MAX.get() as usize;

	pub(crate) fn checked_add(&self, b: NonZeroI32) -> Option<Var> {
		self.0
			.get()
			.checked_add(b.get())
			.map(|v| Var(NonZeroI32::new(v).unwrap()))
	}

	pub(crate) fn next_var(&self) -> Option<Var> {
		const ONE: NonZeroI32 = NonZeroI32::new(1).unwrap();
		self.checked_add(ONE)
	}

	pub(crate) fn prev_var(&self) -> Option<Var> {
		let prev = self.0.get() - 1;
		if prev > 0 {
			Some(Var(NonZeroI32::new(prev).unwrap()))
		} else {
			None
		}
	}
}

impl Display for Var {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "x{}", subscript_number(self.0.get() as usize).format(""))
	}
}

impl Not for Var {
	type Output = Lit;

	fn not(self) -> Self::Output {
		!Lit::from(self)
	}
}

impl VarRange {
	/// Create an empty variable range
	pub fn empty() -> Self {
		Self {
			start: Var(NonZeroI32::new(2).unwrap()),
			end: Var(NonZeroI32::new(1).unwrap()),
		}
	}

	/// Returns the upper bound of the variable range (inclusive).
	///
	/// Note: the value returned by this method is unspecified after the range
	/// has been iterated to exhaustion.
	pub fn end(&self) -> Var {
		self.end
	}

	/// Find the index of a variable within the range
	pub fn find(&self, var: Var) -> Option<usize> {
		if !self.contains(&var) {
			None
		} else {
			let offset = (var.0.get() - self.start.0.get()) as usize;
			debug_assert!(offset <= self.len());
			Some(offset)
		}
	}

	/// Performs the indexing operation into the variable range
	pub fn index(&self, index: usize) -> Var {
		if index >= self.len() {
			panic!("out of bounds access");
		}
		if index == 0 {
			self.start
		} else {
			let index = NonZeroI32::new(index as i32).unwrap();
			self.start.checked_add(index).unwrap()
		}
	}

	/// Returns `true` if the range contains no items.
	///
	/// # Examples
	///
	/// ```
	/// # use pindakaas::VarRange;
	/// assert!(VarRange::empty().is_empty());
	/// ```
	pub const fn is_empty(&self) -> bool {
		self.len() == 0
	}

	/// Returns an iterator of the Boolean variables in the range represented as
	/// [`Lit`]s.
	pub fn iter_lits(&mut self) -> impl Iterator<Item = Lit> + '_ {
		self.map(Lit::from)
	}

	/// Returns the number of variables in the range.
	pub const fn len(&self) -> usize {
		let len = self.end.0.get() - self.start.0.get() + 1;
		if len < 0 {
			return 0;
		}
		len as usize
	}

	/// Create a range starting from `start` and ending at `end` (inclusive)
	pub fn new(start: Var, end: Var) -> Self {
		Self { start, end }
	}

	/// Returns the lower bound of the variable range (inclusive).
	///
	/// Note: the value returned by this method is unspecified after the range
	/// has been iterated to exhaustion.
	pub fn start(&self) -> Var {
		self.start
	}
}

impl DoubleEndedIterator for VarRange {
	fn next_back(&mut self) -> Option<Self::Item> {
		if self.start <= self.end {
			let item = self.end;
			if let Some(prev) = self.end.prev_var() {
				self.end = prev;
			} else {
				*self = VarRange::empty();
			}
			Some(item)
		} else {
			None
		}
	}
}

impl ExactSizeIterator for VarRange {
	fn len(&self) -> usize {
		self.len()
	}
}

impl From<RangeInclusive<Var>> for VarRange {
	fn from(value: RangeInclusive<Var>) -> Self {
		VarRange::new(*value.start(), *value.end())
	}
}

impl FusedIterator for VarRange {}

impl Iterator for VarRange {
	type Item = Var;

	fn count(self) -> usize {
		let (lower, upper) = self.size_hint();
		debug_assert_eq!(upper, Some(lower));
		lower
	}

	fn next(&mut self) -> Option<Self::Item> {
		if self.start <= self.end {
			let item = self.start;
			self.start = self.start.next_var().unwrap();
			Some(item)
		} else {
			None
		}
	}

	fn size_hint(&self) -> (usize, Option<usize>) {
		let len = self.len();
		(len, Some(len))
	}
}

impl RangeBounds<Var> for VarRange {
	fn end_bound(&self) -> Bound<&Var> {
		Bound::Included(&self.end)
	}
	fn start_bound(&self) -> Bound<&Var> {
		Bound::Included(&self.start)
	}
}

impl From<Lit> for i32 {
	fn from(val: Lit) -> Self {
		val.0.get()
	}
}

impl From<Var> for i32 {
	fn from(val: Var) -> Self {
		val.0.get()
	}
}
