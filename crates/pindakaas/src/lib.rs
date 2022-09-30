//! `pindakaas` is a collection of encoders to transform integer and
//! pseudo-Boolean (PB) constraints into conjunctive normal form (CNF). It
//! currently considers mostly linear constraints, which are in the form ∑
//! aᵢ·xᵢ ≷ k, where the aᵢ's and k are constant, xᵢ's are integer variables
//! or boolean literals, and ≷ can be the relationship ≤, =, or ≥. Two forms
//! of PB constraints are seen as special forms of PB constraints: ensuring a
//! set of booleans is *At Most One (AMO)* or *At Most K (AMK)*. Specialised
//! encodings are used when these cases are detected.

use std::clone::Clone;
use std::cmp::Eq;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;

use itertools::{Itertools, Position};
use num::traits::{NumAssignOps, NumOps};
use num::{PrimInt, Signed, Unsigned};

mod at_most_one;
mod cardinality;
pub(crate) mod helpers;
mod linear;

pub use at_most_one::{AtMostOne, LadderEncoder, PairwiseEncoder};
pub use cardinality::Cardinality;
pub use linear::{
	AdderEncoder, BddEncoder, Comparator, LinExp, LinVariant, Linear, LinearEncoder, SwcEncoder,
	TotalizerEncoder,
};

/// Literal is the super-trait for types that can be used to represent boolean
/// literals in this library.
///
/// Literals need to implement the following trait to be used as literals:
///
///  - [`std::clone::Clone`] to allow creating a new copy of the literal to
///    create clauses.
///
///  - [`std::ops::Neg`] to allow the negation literals.
///
///  - [`std::cmp::Eq`] and [`std::hash::Hash`] to allow PB constraints to be
///    simplified
pub trait Literal: fmt::Debug + fmt::Display + Clone + Eq + Hash {
	/// Returns the negation of the literal in its current form
	fn negate(&self) -> Self;
	/// Returns `true` when the literal a negated boolean variable.
	fn is_negated(&self) -> bool;
	/// Returns a non-negated version of the literal
	fn var(&self) -> Self {
		if self.is_negated() {
			self.negate()
		} else {
			self.clone()
		}
	}
}
impl<T: Signed + fmt::Debug + fmt::Display + Clone + Eq + Hash + Neg<Output = Self>> Literal for T {
	fn is_negated(&self) -> bool {
		self.is_negative()
	}
	fn negate(&self) -> Self {
		-(self.clone())
	}
	fn var(&self) -> Self {
		self.abs()
	}
}

/// Unsatisfiable is an error type returned when the problem being encoded is
/// found to be inconsistent.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub struct Unsatisfiable;
impl Error for Unsatisfiable {}
impl fmt::Display for Unsatisfiable {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Problem inconsistency detected")
	}
}

/// Result is a type alias for [`std::result::Result`] that by default returns
/// an empty value, or the [`Unsatisfiable`] error type.
pub type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;
/// NewVarFn is a type alias for the type of function used by
/// [`Encoder`] objects to request new (unused) variables when required to
/// encode the constraint.
pub type NewVarFn<Lit> = fn() -> Lit;
/// EmitClauseFn is a type alias for the type of function used by
/// [`Encoder`] objects to emit the clauses to encode the given constraint.
pub type EmitClauseFn<Lit> = fn(&[Lit]) -> Result;

/// Encoder is the central trait implemented for all the encoding algorithms
pub trait Encoder {
	type Lit: Literal;
	type Ret;

	fn encode<DB: ClauseDatabase<Lit = Self::Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret>;
}

/// Checker is a trait implemented by types that represent constraints. The
/// [`Checker::check`] methods checks whether an assignment (often referred to
/// as a model) satisfies the constraint.
pub trait Checker {
	type Lit: Literal;

	/// Check whether the constraint represented by the object is violated.
	///
	/// - The method returns [`Result::Ok`] when the assignment satisfies
	///   the constraint,
	/// - it returns [`Unsatisfiable`] when the assignment violates the
	///   constraint,
	/// - and it return [`Incomplete`] when not all the literals used in the
	///   constraint have been assigned.
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>>;
}

/// Incomplete is a error type returned by a [`Checker`] type when the
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub struct Incomplete<Lit: Literal> {
	missing: Box<[Lit]>,
}
impl<Lit: Literal> Error for Incomplete<Lit> {}
impl<Lit: Literal> fmt::Display for Incomplete<Lit> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self.missing.len() {
			0 => write!(f, "Unknown literal is unasssigned"),
			1 => write!(f, "Literal {} is unasssigned", self.missing[0]),
			_ => {
				write!(f, "Literals")?;
				for pos in self.missing.iter().with_position() {
					match pos {
						Position::First(lit) => write!(f, " {}", lit)?,
						Position::Middle(lit) => write!(f, ", {}", lit)?,
						Position::Last(lit) => write!(f, ", and {}", lit)?,
						_ => unreachable!(),
					}
				}
				write!(f, " are unasssigned")
			}
		}
	}
}

/// Enumerated type of
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub enum CheckError<Lit: Literal> {
	Unsatisfiable(Unsatisfiable),
	Incomplete(Incomplete<Lit>),
}
impl<Lit: Literal> Error for CheckError<Lit> {}
impl<Lit: Literal> fmt::Display for CheckError<Lit> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			CheckError::Unsatisfiable(err) => err.fmt(f),
			CheckError::Incomplete(err) => err.fmt(f),
		}
	}
}

/// Coefficient in PB constraints are represented by types that implement the
/// `Coefficient` constraint.
pub trait Coefficient: Signed + PrimInt + NumAssignOps + NumOps + fmt::Debug {}
impl<T: Signed + PrimInt + NumAssignOps + NumOps + fmt::Debug> Coefficient for T {}
/// PositiveCoefficient is a trait used for types used for coefficients that
/// have been simplified.
pub trait PositiveCoefficient:
	Unsigned + PrimInt + NumAssignOps + NumOps + Hash + fmt::Debug
{
}
impl<T: Unsigned + PrimInt + NumAssignOps + NumOps + Hash + fmt::Debug> PositiveCoefficient for T {}

/// IntEncoding is a enumerated type use to represent Boolean encodings of
/// integer variables within this library
pub enum IntEncoding<'a, Lit: Literal, C: Coefficient> {
	/// The Direct variant represents a integer variable encoded using domain
	/// or direct encoding of an integer variable. Each given Boolean literal
	/// represents whether the integer takes the associated value (i.e., X =
	/// (first+i) ↔ vals\[i\]).
	Direct { first: C, vals: &'a [Lit] },
	/// The Order variant represents a integer variable using an order
	/// encoding. Each given Boolean literal represents whether the integer
	/// is bigger than the associated value(i.e., X > (first+i) ↔ vals\[i\]).
	Order { first: C, vals: &'a [Lit] },
	/// The Log variant represents a integer variable using a two's complement
	/// encoding. The sum of the Boolean literals multiplied by their
	/// associated power of two represents value of the integer (i.e., X = ∑
	/// 2ⁱ·bits\[i\]).
	Log { signed: bool, bits: &'a [Lit] },
}

/// The `ClauseDatabase` trait is the common trait implemented by types that are
/// used to manage the encoding of PB constraints and contain their output. This
/// trait can be used for all encoding methods in this library.
///
/// To satisfy the trait, the type must implement a [`Self::add_clause`] method
/// and a [`Self::new_var`] method.
pub trait ClauseDatabase {
	/// Type used to represent a Boolean literal in the constraint input and
	/// generated clauses.
	type Lit: Literal;
	/// Method to be used to receive a new Boolean variable that can be used in
	/// the encoding of a constraint.
	fn new_var(&mut self) -> Self::Lit;

	/// Add a clause to the `ClauseDatabase`. The sink is allowed to return
	/// [`Unsatisfiable`] when the collection of clauses has been *proven* to
	/// be unsatisfiable. This is used as a signal to the encoder that any
	/// subsequent encoding effort can be abandoned.
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result;
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_int_literals() {
		assert!(is_lit(1i8));
		assert!(is_lit(1i16));
		assert!(is_lit(1i32));
		assert!(is_lit(1i64));
		assert!(is_lit(1i128));
	}
	fn is_lit<T: Literal>(_: T) -> bool {
		true
	}

	#[test]
	fn test_coefficients() {
		assert!(is_coeff(1i8));
		assert!(is_coeff(1i16));
		assert!(is_coeff(1i32));
		assert!(is_coeff(1i64));
		assert!(is_coeff(1i128));
	}
	fn is_coeff<T: Coefficient>(_: T) -> bool {
		true
	}

	#[test]
	fn test_positive_coefficients() {
		assert!(is_poscoeff(1u8));
		assert!(is_poscoeff(1u16));
		assert!(is_poscoeff(1u32));
		assert!(is_poscoeff(1u64));
		assert!(is_poscoeff(1u128));
	}
	fn is_poscoeff<T: PositiveCoefficient>(_: T) -> bool {
		true
	}
}
