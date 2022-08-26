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
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;

use itertools::Itertools;
use num::traits::{NumAssignOps, NumOps};
use num::{PrimInt, Signed, Unsigned};

mod adder;
mod aggregate;
mod helpers;
mod totalizer;

pub use aggregate::BoolLin;

/// Literal is the super-trait for types that can be used to represent boolean
/// literals in this library.
///
/// Literals need to implement the following trait to be used as literals:
///
///  - [`std::clone::Clone`] to allow creating a new copy of the literal to create clauses.
///
///  - [`std::ops::Neg`] to allow the negation literals.
///
///  - [`std::cmp::Eq`] and [`std::hash::Hash`] to allow PB constraints to be
///    simplified
pub trait Literal: fmt::Debug + Clone + Eq + Hash {
	/// Returns `true` when the literal a negated boolean variable.
	fn is_negated(&self) -> bool;
	fn negate(&self) -> Self;
}
impl<T: Signed + fmt::Debug + Clone + Eq + Hash + Neg<Output = Self>> Literal for T {
	fn is_negated(&self) -> bool {
		self.is_negative()
	}
	fn negate(&self) -> Self {
		-(self.clone())
	}
}

/// Unsatisfiable is a error type to returned when the problem being encoding is found to be
/// inconsistent.
#[derive(Debug, PartialEq, Eq, PartialOrd)]
pub struct Unsatisfiable;
impl Error for Unsatisfiable {}
impl fmt::Display for Unsatisfiable {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Problem inconsistency detected")
	}
}
pub type Result<T = (), E = Unsatisfiable> = std::result::Result<T, E>;

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

/// IntEncoding is a enumerated type use to represent Boolean encodings of integer variables within
/// this library
pub enum IntEncoding<'a, Lit: Literal, C: Coefficient> {
	/// The Direct variant represents a integer variable encoded using domain or direct encoding of
	/// an integer variable. Each given Boolean literal represents whether the integer takes the
	/// associated value (i.e., X = (first+i) ↔ vals\[i\]).
	Direct { first: C, vals: &'a [Lit] },
	/// The Order variant represents a integer variable using an order encoding. Each given Boolean
	/// literal represents whether the integer is bigger than the associated value
	/// (i.e., X > (first+i) ↔ vals\[i\]).
	Order { first: C, vals: &'a [Lit] },
	/// The Log variant represents a integer variable using a two's complement encoding.
	/// The sum of the Boolean literals multiplied by their associated power of two represents value
	/// of the integer (i.e., X = ∑ 2ⁱ·bits\[i\]).
	Log { signed: bool, bits: &'a [Lit] },
}

// TODO just temporary until I find out how to use IntEncodings for this
#[derive(Debug)]
pub enum Constraint<'a, Lit> {
	AMO(HashSet<&'a Lit>),
	IC(Vec<&'a Lit>),
}

// TODO add EO, and probably something for Unconstrained
#[derive(Debug)]
pub enum Part<Lit, Coefficient> {
	AMO(HashMap<Lit, Coefficient>),
	IC(Vec<(Lit, Coefficient)>),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}

/// The `ClauseDatabase` trait is the common trait implemented by types that are
/// used to manage the encoding of PB constraints and contain their output. This
/// trait can be used for all encoding methods in this library.
///
/// This trait is a supertrait of [`ClauseSink`], which means that implementers
/// should have a [`ClauseSink::add_clause`] method. Futhermore, implementers
/// are required to have a [`Self::new_var`] method.
pub trait ClauseDatabase: ClauseSink {
	/// Method to be used to receive a new Boolean variable that can be used in
	/// the encoding of a constraint.
	fn new_var(&mut self) -> Self::Lit;

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
		cons: &[Constraint<Self::Lit>], // slice
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
				&lits.iter().map(|l| (l.clone(), PC::one())).collect(),
				*k,
			),
			EqualK { lits, k } => self.encode_bool_lin_eq_adder(
				&lits.iter().map(|l| (l.clone(), PC::one())).collect(),
				*k,
			),
			AtMostOne { lits } => self.encode_amo_pairwise(lits),
			Trivial => Ok(()),
		}
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
	fn encode_bool_lin_eq_adder<PC: PositiveCoefficient>(
		&mut self,
		terms: &HashMap<Self::Lit, PC>,
		k: PC,
	) -> Result {
		adder::encode_bool_lin_adder(self, terms, Comparator::Equal, k)
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
	fn encode_bool_lin_le_adder<PC: PositiveCoefficient>(
		&mut self,
		terms: &HashMap<Self::Lit, PC>,
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

	fn encode_amo_ladder(&mut self, xs: &HashSet<Self::Lit>) -> Result {
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
	/// subsequent encoding effort can be abandoned.
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result;

	/// Adds an encoding for an At Most One constraints to `sink` that for every
	/// pair of literals from `lits` states that one of the literals has to be
	/// `false`.
	///
	/// # Required Preprocessing
	///
	/// - `lits` is expected to contain at least 2 literals. In cases where an
	///   AMO constraint has fewer literals, the literals can either be removed
	///   for the problem or the problem is already unsatisfiable
	fn encode_amo_pairwise(&mut self, lits: &HashSet<Self::Lit>) -> Result {
		// Precondition: there are multiple literals in the AMO constraint
		debug_assert!(lits.len() >= 2);
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in lits.iter().tuple_combinations() {
			self.add_clause(&[a.negate(), b.negate()])?
		}
		Ok(())
	}
}

impl<Lit: Literal> ClauseSink for Vec<Vec<Lit>> {
	type Lit = Lit;
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		self.push(cl.iter().map(|x| (*x).clone()).collect());
		Ok(())
	}
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
	fn test_amo_ladder() {
		let mut two = TestDB { nr: 2, db: vec![] };
		two.encode_amo_ladder(&HashSet::from_iter([1, 2])).unwrap();
		assert_eq!(
			two.db,
			vec![
				vec![3],
				vec![-4, 3],
				vec![-1, 3],
				vec![-1, -4],
				vec![-3, 4, 1],
				vec![-5, 4],
				vec![-2, 4],
				vec![-2, -5],
				vec![-4, 5, 2],
				vec![-5]
			]
		);
		assert_eq!(two.nr, 5);
	}

	#[test]
	fn test_amo_pairwise() {
		// TODO: Fix sorting issue!
		// AMO on two literals
		let mut two: Vec<Vec<i32>> = vec![];
		two.encode_amo_pairwise(&HashSet::from_iter([1, 2]))
			.unwrap();
		// assert_eq!(two, vec![vec![-1, -2]]);
		// AMO on a negated literals
		let mut two: Vec<Vec<i32>> = vec![];
		two.encode_amo_pairwise(&HashSet::from_iter([-1, 2]))
			.unwrap();
		// assert_eq!(two, vec![vec![1, -2]]);
		// AMO on three literals
		let mut two: Vec<Vec<i32>> = vec![];
		two.encode_amo_pairwise(&HashSet::from_iter([1, 2, 3]))
			.unwrap();
		// assert_eq!(two, vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]]);
	}

	struct TestDB {
		nr: i32,
		db: Vec<Vec<i32>>,
	}

	impl ClauseSink for TestDB {
		type Lit = i32;

		fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
			self.db.add_clause(cl)
		}
	}

	impl ClauseDatabase for TestDB {
		fn new_var(&mut self) -> Self::Lit {
			self.nr += 1;
			self.nr
		}
	}

	#[test]
	fn test_pb_encode() {
		let mut two = TestDB { nr: 3, db: vec![] };
		assert!(two
			.encode_bool_lin::<i64, u64>(
				&[1, 1, 1, 2],
				&[1, 2, 3, 4],
				crate::Comparator::LessEq,
				1,
				&[]
			)
			.is_ok());
	}
}
