//! `pindakaas` is a collection of encoders to transform pseudo-Boolean (PB)
//! constraints into conjunctive normal form (CNF). PB constraint are in the
//! form ∑ aᵢ·xᵢ ≷ k, where the aᵢ's and k are constant, xᵢ's are boolean
//! literals, and ≷ can be the relationship ≤, =, or ≥. Two forms of PB
//! constraints are seen as special forms of PB constraints: ensuring a set of
//! booleans is *At Most One (AMO)* or *At Most K (AMK)*. There are specialized
//! algorithms for these cases.

use std::clone::Clone;
use std::cmp::Eq;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::ops::Neg;

use itertools::Itertools;
use num::{
	traits::{NumAssignRef, NumRef},
	Integer, PrimInt, Signed, Unsigned,
};

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
pub trait Literal: fmt::Debug + Clone + Eq + Hash + Neg<Output = Self> {
	/// Returns `true` when the literal a negated boolean variable.
	fn is_negative(&self) -> bool;
}
impl<T: Signed + fmt::Debug + Clone + Eq + Hash + Neg<Output = Self>> Literal for T {
	fn is_negative(&self) -> bool {
		self.is_negative()
	}
}

/// Unsatisfiable is a error type to returned when the problem being encoding is found to be
/// inconsistent.
#[derive(Debug)]
pub struct Unsatisfiable;
impl Error for Unsatisfiable {}
impl fmt::Display for Unsatisfiable {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Problem inconsistency detected")
	}
}
type Result = std::result::Result<(), Unsatisfiable>;

/// Coefficient in PB constraints are represented by types that implement the
/// `Coefficient` constraint.
pub trait Coefficient: Clone + Signed + Integer + NumAssignRef + NumRef {}
impl<T: Clone + Signed + Integer + NumAssignRef + NumRef> Coefficient for T {}
/// PositiveCoefficient is a trait used for types used for coefficients that
/// have been simplified.
pub trait PositiveCoefficient:
	Clone + Unsigned + Integer + PrimInt + NumAssignRef + NumRef
{
}
impl<T: Clone + Unsigned + Integer + PrimInt + NumAssignRef + NumRef> PositiveCoefficient for T {}

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
/// are required to have a [`Self::new_lit`] method.
pub trait ClauseDatabase: ClauseSink {
	/// Method to be used to receive a new (unused) litaral that can be used in
	/// the encoding of a constraint.
	fn new_lit(&mut self) -> Self::Lit;

	/// Encode the constraint
	fn encode_pb<C: Coefficient, PC: PositiveCoefficient + TryFrom<C>>(
		&mut self,
		pair: &[(C, Self::Lit)],
		comp: Comparator,
		k: C,
	) -> Result {
		use Comparator::*;

		// Convert ≤ to ≥ and aggregate multiple occurences of the same
		// variable.
		let mut agg = HashMap::with_capacity(pair.len());
		for (coef, lit) in pair {
			let cl = (*lit).clone();
			let var = if cl.is_negative() { -cl } else { cl };
			let entry = agg.entry(var).or_insert(C::zero());
			let mut coef = (*coef).clone();
			if lit.is_negative() ^ (comp == GreaterEq) {
				coef *= -C::one()
			}
			*entry += coef;
		}
		let mut k = if comp == GreaterEq { -k } else { k };
		let comp = if comp == GreaterEq { LessEq } else { comp };
		debug_assert_ne!(comp, GreaterEq);

		// Convert all negative coefficients
		let mut normalized = Vec::with_capacity(agg.len());
		for (mut lit, mut coef) in agg {
			if coef == C::zero() {
				continue;
			}
			if coef.is_negative() {
				coef = -coef;
				lit = -lit;
				k += coef.clone();
			};
			let coef = match PC::try_from(coef) {
				Ok(coef) => coef,
				Err(_) => panic!("Unable to convert coefficient to positive coeffient."),
			};
			normalized.push((coef, lit))
		}

		// trivial case: constraint is unsatisfiable
		if k < C::zero() {
			return Err(Unsatisfiable);
		}
		// trivial case: no literals can be activated
		if k == C::zero() {
			for (_, lit) in normalized {
				self.add_clause(&[-lit])?
			}
			return Ok(());
		}

		let mut k = match PC::try_from(k) {
			Ok(k) => k,
			Err(_) => panic!("Unable to convert coefficient to positive coeffient."),
		};
		// Remove pairs with coef higher than k
		let (impossible, mut considered): (Vec<(PC, Self::Lit)>, Vec<(PC, Self::Lit)>) =
			normalized.drain(..).partition(|(c, _)| c > &k);
		// Force literals that cannot be activated
		for (_, lit) in impossible {
			self.add_clause(&[-lit])?
		}
		// Check whether considered literals can violate / satisfy the constraint
		let mut total = PC::zero();
		for (c, _) in &considered {
			total += c;
		}
		if comp == Comparator::LessEq {
			if total <= k {
				return Ok(());
			} else if normalized.len() == 2 {
				// Simple decision between 2 literals
				return self.add_clause(
					&considered
						.drain(..)
						.map(|(_, lit)| lit)
						.collect::<Vec<Self::Lit>>(),
				);
			}
		} else if comp == Comparator::Equal {
			if total < k {
				return Err(Unsatisfiable);
			} else if total == k {
				for (_, lit) in considered {
					self.add_clause(&[lit])?
				}
				return Ok(());
			}
		}
		debug_assert!(considered.len() > 0);

		// special case: all coefficients are equal (and can be made one)
		if considered.iter().all(|(c, _)| c == &considered[0].0) {
			// trivial case: k cannot be made from the coefficients
			if comp == Equal && k.clone() % &considered[0].0 != PC::zero() {
				return Err(Unsatisfiable);
			}

			k /= &considered[0].0;
			let considered = considered
				.drain(..)
				.map(|(_, lit)| lit)
				.collect::<Vec<Self::Lit>>();
			if k == PC::one() {
				// Encode At Least One constraint
				if comp == Equal {
					self.add_clause(&considered)?
				}
				// Encode At Most One constraint
				return self.encode_amo(&considered);
			}
			// Encode count constraint
			return self.encode_count(&considered, comp, k);
		}

		// Default case: encode pseudo-Boolean constraint
		// TODO: Pick encoding
		self.encode_pb_adder(&considered, comp, k)
	}

	/// Encode the constraint that ∑ litsᵢ ≷ k
	fn encode_count<PC: PositiveCoefficient>(
		&mut self,
		pair: &[Self::Lit],
		comp: Comparator,
		k: PC,
	) -> Result {
		// TODO: implement encoding
		self.encode_pb_adder(
			&pair
				.iter()
				.map(|x| (PC::one(), x.clone()))
				.collect::<Vec<(PC, Self::Lit)>>(),
			comp,
			k,
		)
	}

	/// Encode that at most on literal in `lits` can be true.
	///
	/// # Required Preprocessing
	///
	/// - The literals in `lits` are assumed to the unique. In an AMO constraint
	///   non-unique literals should be preprocessed removed from the problem.
	///
	/// - `lits` is expected to contain at least 2 literals. In cases where an
	///   AMO constraint has fewer literals, the literals can either be removed
	///   for the problem or the problem is already unsatisfiable
	fn encode_amo(&mut self, lits: &[Self::Lit]) -> Result {
		// Precondition: there is no duplicate literals
		debug_assert!(lits.iter().all_unique());
		// Precondition: there are multiple literals in the AMO constraint
		debug_assert!(lits.len() >= 2);
		// TODO: Pick encoding
		self.encode_amo_pairwise(lits)
	}

	/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a binary adders circuits
	fn encode_pb_adder<PC: PositiveCoefficient>(
		&mut self,
		pair: &[(PC, Self::Lit)],
		comp: Comparator,
		k: PC,
	) -> Result {
		// The number of relevant bits in k
		let bits = (PC::zero().count_zeros() - k.count_zeros()) as usize;
		let mut k = (0..bits)
			.map(|b| k & (PC::one() << b) != PC::zero())
			.collect::<Vec<bool>>();
		debug_assert_eq!(k[bits - 1], true);

		// Create structure with which coefficients use which bits
		let mut bucket = vec![Vec::new(); bits];
		for b in 0..bits {
			for (coef, lit) in pair {
				if *coef & (PC::one() << b) != PC::zero() {
					bucket[b].push(lit.clone());
				}
			}
		}

		// Functions to create sum and carry literals
		let sum_lit = |db: &mut Self, lits: &[Self::Lit]| {
			let sum = db.new_lit();
			match lits {
				[a, b, c] => {
					db.add_clause(&[a.clone(), b.clone(), c.clone(), -sum.clone()])?;
					db.add_clause(&[a.clone(), -b.clone(), -c.clone(), -sum.clone()])?;
					db.add_clause(&[-a.clone(), b.clone(), -c.clone(), -sum.clone()])?;
					db.add_clause(&[-a.clone(), -b.clone(), c.clone(), -sum.clone()])?;

					db.add_clause(&[-a.clone(), -b.clone(), -c.clone(), sum.clone()])?;
					db.add_clause(&[-a.clone(), b.clone(), c.clone(), sum.clone()])?;
					db.add_clause(&[a.clone(), -b.clone(), c.clone(), sum.clone()])?;
					db.add_clause(&[a.clone(), b.clone(), -c.clone(), sum.clone()])?;
				}
				_ => unreachable!(),
			}
			Ok(sum)
		};
		let carry_lit = |db: &mut Self, lits: &[Self::Lit]| {
			let carry = db.new_lit();
			match lits {
				[a, b, c] => {
					db.add_clause(&[a.clone(), b.clone(), -carry.clone()])?;
					db.add_clause(&[a.clone(), c.clone(), -carry.clone()])?;
					db.add_clause(&[b.clone(), c.clone(), -carry.clone()])?;

					db.add_clause(&[-a.clone(), -b.clone(), carry.clone()])?;
					db.add_clause(&[-a.clone(), -c.clone(), carry.clone()])?;
					db.add_clause(&[-a.clone(), -b.clone(), carry.clone()])?;
				}
				_ => unreachable!(),
			}
			Ok(carry)
		};
		let force_carry = |db: &mut Self, lits: &[Self::Lit], k: bool| match lits {
			[a, b, c] => {
				let neg = |x: Self::Lit| if k { x } else { -x };
				db.add_clause(&[neg(a.clone()), neg(b.clone())])?;
				db.add_clause(&[neg(a.clone()), neg(c.clone())])?;
				db.add_clause(&[neg(b.clone()), neg(c.clone())])
			}
			[a, b] => {
				if k {
					// TODO: Can we avoid this?
					db.add_clause(&[a.clone()])?;
					db.add_clause(&[b.clone()])
				} else {
					db.add_clause(&[-a.clone(), -b.clone()])
				}
			}
			_ => unreachable!(),
		};
		let force_sum = |db: &mut Self, lits: &[Self::Lit], k: bool| match lits {
			[a, b, c] => {
				if k {
					db.encode_xor3(a, b, c)
				} else {
					db.add_clause(&[-a.clone(), -b.clone(), -c.clone()])?;
					db.add_clause(&[-a.clone(), b.clone(), c.clone()])?;
					db.add_clause(&[a.clone(), -b.clone(), c.clone()])?;
					db.add_clause(&[a.clone(), b.clone(), -c.clone()])
				}
			}
			[a, b] => {
				if k {
					db.encode_xor(a, b)
				} else {
					db.add_clause(&[a.clone(), -b.clone()])?;
					db.add_clause(&[-a.clone(), b.clone()])
				}
			}
			_ => unreachable!(),
		};

		// Compute the sums and carries for each bit layer
		// if comp == Equal, then this is directly enforced (to avoid creating additional literals)
		// otherwise, sum literals are left in the buckets for further processing
		let mut sum = vec![None; bits];
		for b in 0..bits {
			if bucket[b].is_empty() {
				if k[b] && comp == Comparator::Equal {
					return Err(Unsatisfiable);
				}
			} else if bucket[b].len() == 1 {
				let x = bucket[b].pop().unwrap();
				if k[b] && comp == Comparator::Equal {
					self.add_clause(&[x])?
				} else {
					sum[b] = Some(x);
				}
			} else {
				while bucket[b].len() >= 2 {
					let last = bucket[b].len() <= 3;
					let lits = if last {
						bucket[b].split_off(0)
					} else {
						let i = bucket[b].len() - 3;
						bucket[b].split_off(i)
					};
					debug_assert!(lits.len() == 3 || lits.len() == 2);

					// Compute sum
					if last && comp == Comparator::Equal {
						// No need to create a new literal, force the sum to equal the result
						force_sum(self, lits.as_slice(), k[b])?;
					} else {
						bucket[b].push(sum_lit(self, lits.as_slice())?);
					}

					// Compute carry
					if b + 1 >= bucket.len() {
						// Carry will bring the sum to be greater than k, force to be false
						force_carry(self, &lits[..], false)?
					} else if last && comp == Comparator::Equal && bucket[b + 1].is_empty() {
						// No need to create a new literal, force the carry to equal the result
						force_carry(self, &lits[..], k[b + 1])?;
						// Mark k[b + 1] as false (otherwise next step will fail)
						k[b + 1] = false;
					} else {
						bucket[b + 1].push(carry_lit(self, lits.as_slice())?);
					}
				}
				debug_assert!(
					(comp == Comparator::Equal && bucket[b].is_empty())
						|| (comp == Comparator::LessEq && bucket[b].len() == 1)
				);
				sum[b] = bucket[b].pop();
			}
		}
		// In case of equality this has been enforced
		debug_assert!(comp != Comparator::Equal || sum.iter().all(|x| x.is_none()));

		// Enforce less-than constraint
		if comp == Comparator::LessEq {
			// For every zero bit in k:
			// - either the sum bit is also zero, or
			// - a higher sum bit is zero that was one in k.
			for i in 0..bits {
				if !k[i] && sum[i].is_some() {
					self.add_clause(
						&(i..bits)
							.filter_map(|j| if j == i || k[j] { sum[j].clone() } else { None })
							.map(|lit| -lit)
							.collect::<Vec<Self::Lit>>(),
					)?;
				}
			}
		}
		Ok(())
	}
}

/// Types that abide by the `ClauseSink` trait can be used as the output for the
/// constraint encodings. This trait also contains basic encodings that never
/// create new literals.
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
	/// - The literals in `lits` are assumed to the unique. In an AMO constraint
	///   non-unique literals should be preprocessed removed from the problem.
	///
	/// - `lits` is expected to contain at least 2 literals. In cases where an
	///   AMO constraint has fewer literals, the literals can either be removed
	///   for the problem or the problem is already unsatisfiable
	fn encode_amo_pairwise(&mut self, lits: &[Self::Lit]) -> Result {
		// Precondition: there is no duplicate literals
		debug_assert!(lits.iter().all_unique());
		// Precondition: there are multiple literals in the AMO constraint
		debug_assert!(lits.len() >= 2);
		// For every pair of literals (i, j) add "¬i ∨ ¬j"
		for (a, b) in lits.iter().tuple_combinations() {
			self.add_clause(&[-a.clone(), -b.clone()])?
		}
		Ok(())
	}

	/// Adds simple clauses for a binary XOR constraint a ⊻ b.
	fn encode_xor(&mut self, a: &Self::Lit, b: &Self::Lit) -> Result {
		self.add_clause(&[a.clone(), b.clone()])?;
		self.add_clause(&[-a.clone(), -b.clone()])
	}
	/// Adds simple clauses for a ternary XOR constraint a ⊻ b ⊻ c
	fn encode_xor3(&mut self, a: &Self::Lit, b: &Self::Lit, c: &Self::Lit) -> Result {
		self.add_clause(&[a.clone(), b.clone(), c.clone()])?;
		self.add_clause(&[a.clone(), -b.clone(), -c.clone()])?;
		self.add_clause(&[-a.clone(), b.clone(), -c.clone()])?;
		self.add_clause(&[-a.clone(), -b.clone(), c.clone()])
	}
}

impl<Lit: Literal> ClauseSink for Vec<Vec<Lit>> {
	type Lit = Lit;
	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		self.push(cl.into_iter().map(|x| (*x).clone()).collect());
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use crate::{ClauseDatabase, ClauseSink, Literal, Result};

	#[test]
	fn test_int_literals() {
		assert_eq!(is_lit(1i8), true);
		assert_eq!(is_lit(1i16), true);
		assert_eq!(is_lit(1i32), true);
		assert_eq!(is_lit(1i64), true);
		assert_eq!(is_lit(1i128), true);
	}
	fn is_lit<T: Literal>(_: T) -> bool {
		true
	}

	#[test]
	fn test_naive_amo() {
		// AMO on two literals
		let mut two: Vec<Vec<i32>> = vec![];
		two.encode_amo_pairwise(&[1, 2][..]).unwrap();
		assert_eq!(two, vec![vec![-1, -2]]);
		// AMO on a negated literals
		let mut two: Vec<Vec<i32>> = vec![];
		two.encode_amo_pairwise(&[-1, 2][..]).unwrap();
		assert_eq!(two, vec![vec![1, -2]]);
		// AMO on three literals
		let mut two: Vec<Vec<i32>> = vec![];
		two.encode_amo_pairwise(&[1, 2, 3][..]).unwrap();
		assert_eq!(two, vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]]);
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
		fn new_lit(&mut self) -> Self::Lit {
			self.nr += 1;
			self.nr
		}
	}

	#[test]
	fn test_pb_encode() {
		let mut two = TestDB { nr: 3, db: vec![] };
		assert!(two
			.encode_pb::<i64, u64>(
				&[(1, 1), (1, 2), (1, 3), (2, 4)],
				crate::Comparator::LessEq,
				1
			)
			.is_ok());
	}
}
