//! `pindakaas` is a collection of encoders to transform pseudo-Boolean (PB)
//! constraints into conjunctive normal form (CNF). PB constraint are in the
//! form ∑ aᵢ·xᵢ ≷ k, where the aᵢ's and k are constant, xᵢ's are boolean
//! literals, and ≷ can be the relationship ≤, =, or ≥. Two forms of PB
//! constraints are seen as special forms of PB constraints: ensuring a set of
//! booleans is *At Most One (AMO)* or *At Most K (AMK)*. There are specialised
//! algorithms for these cases.

use std::clone::Clone;
use std::cmp::Eq;
use std::hash::Hash;
use std::ops::Neg;

/// Literal is the super-trait for types that can be used to represent boolean
/// literals in this library.
///
/// Literals need to implement the following trait to be used as literals:
///
///  - [`std::clone::Clone`] to allow creating a new copy of the literal to call
///    the [`ClauseSink::add_clause`] method.
///
///  - [`std::ops::Neg`] to allow the adding of negated literals to clauses.
///
///  - [`std::cmp::Eq`] and [`std::hash::Hash`] to allow PB constraints to be
///    simplified
pub trait Literal: Clone + Eq + Hash + Neg<Output = Self> {}
impl<T: Clone + Eq + Hash + Neg<Output = Self>> Literal for T {}

/// Coeffiecients in PB constraints are represented by types that implement the
/// `Coefficient` constraint.
// pub trait Coefficient: Signed + PrimInt {}
type Coeff = i64;

/// PositiveCoefficient is a trait used for types used for coefficients that
/// have been simplified.
// pub trait PositiveCoefficient: Unsigned + PrimInt {}
type PosCoeff = u64;

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
    fn new_lit(&self) -> Self::Lit;

    /// Encode the constraint
    fn encode_pb(&mut self, _pair: &[(Coeff, Self::Lit)], _comp: Comparator, _k: Coeff) -> bool {
        // TODO: implement encoding
        unimplemented!()
    }

    /// Encode the constraint that ∑ coeffᵢ·litsᵢ ≤ k
    fn encode_amk(&mut self, _pair: &[(PosCoeff, Self::Lit)], _k: Coeff) -> bool {
        // TODO: implement encoding
        unimplemented!()
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
    fn encode_amo(&mut self, lits: &[Self::Lit]) -> bool {
        // Precondition: there is no duplicate literals
        debug_assert!(unique_members(lits));
        // Precondition: there are multiple literals in the AMO constraint
        debug_assert!(lits.len() >= 2);
        // TODO: Pick encoding
        self.encode_naive_amo(lits)
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
    fn add_clause(&mut self, cl: &[Self::Lit]) -> bool;

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
    fn encode_naive_amo(&mut self, lits: &[Self::Lit]) -> bool {
        // Precondition: there is no duplicate literals
        debug_assert!(unique_members(lits));
        // Precondition: there are multiple literals in the AMO constraint
        debug_assert!(lits.len() >= 2);
        // For every pair of literals (i, j) add "¬i ∨ ¬j"
        (0..lits.len()).into_iter().all(|i| {
            (i + 1..lits.len())
                .into_iter()
                .all(|j| self.add_clause(&[-(lits[i].clone()), -(lits[j].clone())]))
        })
    }
}

impl ClauseSink for Vec<Vec<i32>> {
    type Lit = i32;
    fn add_clause(&mut self, cl: &[Self::Lit]) -> bool {
        self.push(cl.into_iter().map(|x| (*x).clone()).collect());
        true
    }
}

// ---- Helper Functions ----

/// Checks if all members in a slice are unique
fn unique_members<T: Hash + Eq>(collection: &[T]) -> bool {
    // All members of collection are unique if a hash set constructed with the
    // same elements has the same number of elements.
    collection
        .into_iter()
        .collect::<std::collections::HashSet<_>>()
        .len()
        == collection.len()
}

#[cfg(test)]
mod tests {
    use crate::{ClauseSink, Literal};

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
        two.encode_naive_amo(&[1, 2][..]);
        assert_eq!(two, vec![vec![-1, -2]]);
        // AMO on a negated literals
        let mut two: Vec<Vec<i32>> = vec![];
        two.encode_naive_amo(&[-1, 2][..]);
        assert_eq!(two, vec![vec![1, -2]]);
        // AMO on three literals
        let mut two: Vec<Vec<i32>> = vec![];
        two.encode_naive_amo(&[1, 2, 3][..]);
        assert_eq!(two, vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]]);
    }
}
