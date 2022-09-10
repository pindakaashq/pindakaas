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
	AdderEncoder, Comparator, Constraint, LinVariant, Linear, LinearEncoder, TotalizerEncoder,
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
	/// Returns `true` when the literal a negated boolean variable.
	fn is_negated(&self) -> bool;
	fn negate(&self) -> Self;
}
impl<T: Signed + fmt::Debug + fmt::Display + Clone + Eq + Hash + Neg<Output = Self>> Literal for T {
	fn is_negated(&self) -> bool {
		self.is_negative()
	}
	fn negate(&self) -> Self {
		-(self.clone())
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

	/// Add a clause to the `ClauseDatabase`. The sink is allowed to return
	/// [`Unsatisfiable`] when the collection of clauses has been *proven* to
	/// be unsatisfiable. This is used as a signal to the encoder that any
	/// Encode an integer linear constraint
	fn encode_int_lin<C: Coefficient + TryInto<PC>, PC: PositiveCoefficient>(
		&mut self,
		coeff: &[C],
		vars: &[IntEncoding<Self::Lit, C>],
		cmp: Comparator,
		k: C,
	) -> Result {
		assert_eq!(coeff.len(), vars.len());

		// TODO: Actually deal with the fact that these constraints are integers
		let mut bool_coeff = Vec::new();
		let mut bool_vars = Vec::new();
		let mut k = k;

		for i in 0..coeff.len() {
			match &vars[i] {
				IntEncoding::Direct { first, vals } => {
					let mut counter = *first;
					for j in 0..vals.len() {
						bool_coeff.push(coeff[i] * counter);
						bool_vars.push(vals[j].clone());
						counter += C::one();
					}
				}
				IntEncoding::Order { first, vals } => {
					k -= *first * coeff[i];
					for i in 0..vals.len() {
						bool_coeff.push(coeff[i]);
						bool_vars.push(vals[i].clone());
					}
				}
				IntEncoding::Log { signed, bits } => {
					let two = C::one() + C::one();
					for i in 0..bits.len() {
						bool_coeff.push(coeff[i] * two.pow(i as u32));
						bool_vars.push(bits[i].clone());
					}
					if *signed {
						let last_coeff = bool_coeff.last_mut().unwrap();
						*last_coeff = -*last_coeff;
					}
				}
			}
		}

		self.encode_bool_lin(&bool_coeff, &bool_vars, cmp, k, &[])
	}

	/// Encode a Boolean linear constraint
	fn encode_bool_lin<C: Coefficient + TryInto<PC>, PC: PositiveCoefficient>(
		&mut self,
		coeff: &[C],
		lits: &[Self::Lit],
		cmp: Comparator,
		k: C,
		cons: &[Constraint<Self::Lit, C>],
	) -> Result {
		let constraint = BoolLin::aggregate(self, coeff, lits, cmp, k, cons)?;

		self.encode_aggregated_bool_lin(&constraint)
	}

	fn encode_aggregated_bool_lin<PC: PositiveCoefficient>(
		&mut self,
		constraint: &BoolLin<PC, Self::Lit>,
	) -> Result {
		use BoolLin::*;
		// TODO: Make better educated choices
		match constraint {
			LinEqual { terms, k } => self.encode_bool_lin_eq_adder(terms, *k),
			LinLessEq { terms, k } => self.encode_bool_lin_le_adder(terms, *k),
			AtMostK { lits, k } => self.encode_bool_lin_le_adder(
				// &lits.iter().map(|l| (l.clone(), PC::one())).collect(),
				lits.iter()
					.map(|l| Part::Amo(vec![(l.clone(), PC::one())]))
					.collect::<Vec<_>>()
					.as_slice(),
				*k,
			),
			EqualK { lits, k } => self.encode_bool_lin_eq_adder(
				// &lits.iter().map(|l| (l.clone(), PC::one())).collect(),
				lits.iter()
					.map(|l| Part::Amo(vec![(l.clone(), PC::one())]))
					.collect::<Vec<_>>()
					.as_slice(),
				*k,
			),
			AtMostOne { lits } => self.encode_amo_pairwise(lits),
			Trivial => Ok(()),
		}
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
	fn encode_bool_lin_eq_adder<PC: PositiveCoefficient>(
		&mut self,
		terms: &[Part<Self::Lit, PC>],
		k: PC,
	) -> Result {
		adder::encode_bool_lin_adder(self, terms, Comparator::Equal, k)
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
	fn encode_bool_lin_le_adder<PC: PositiveCoefficient>(
		&mut self,
		terms: &[Part<Self::Lit, PC>],
		k: PC,
	) -> Result {
		adder::encode_bool_lin_adder(self, terms, Comparator::LessEq, k)
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a totalizer
	fn encode_bool_lin_le_totalizer<PC: PositiveCoefficient>(
		&mut self,
		partition: &[Part<Self::Lit, PC>],
		k: PC,
	) -> Result {
		totalizer::encode_bool_lin_le_totalizer(self, partition, Comparator::LessEq, k)
	}

	fn encode_amo_ladder(&mut self, xs: &Vec<Self::Lit>) -> Result {
		debug_assert!(xs.iter().duplicates().count() == 0);
		debug_assert!(xs.len() >= 2);

		// TODO could be slightly optimised to not introduce fixed lits
		let mut a = self.new_var(); // y_v-1
		self.add_clause(&[a.clone()])?;
		for x in xs {
			let b = self.new_var(); // y_v
			self.add_clause(&[b.negate(), a.clone()])?; // y_v -> y_v-1

			// "Channelling" clauses for x_v <-> (y_v-1 /\ ¬y_v)
			self.add_clause(&[x.negate(), a.clone()])?; // x_v -> y_v-1
			self.add_clause(&[x.negate(), b.negate()])?; // x_v -> ¬y_v
			self.add_clause(&[a.negate(), b.clone(), x.clone()])?; // (y_v-1 /\ ¬y_v) -> x=v
			a = b;
		}
		self.add_clause(&[a.negate()])?;
		Ok(())
	}
}

/// Types that abide by the `ClauseSink` trait can be used as the output for the
/// constraint encodings. This trait also contains basic encodings that never
/// create nh literals.
///
/// To satisfy the trait, the type must implement a
/// [`Self::add_clause`] method.
pub trait ClauseSink {
	/// Type used to represent a Boolean literal in the constraint input and
	/// generated clauses.
	type Lit: Literal;

	/// Add a clause to the `ClauseSink`. The sink is allowed to return `false`
	/// only when the collection of clauses has been *proven* to be
	/// unsatisfiable. This is used as a signal to the encoder that any
>>>>>>> 5809902 (Build separate, small nodes for Le constraint groups)
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
