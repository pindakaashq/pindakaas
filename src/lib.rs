//! `pindakaas` is a collection of encoders to transform pseudo-Boolean (PB)
//! constraints into conjunctive normal form (CNF). PB constraint are in the
//! form ∑ aᵢ·xᵢ ≷ c, where the aᵢ's and c are constant, xᵢ's are boolean
//! literals, and ≷ can be the relationship ≤, =, or ≥. Two forms of PB
//! constraints are seen as special forms of PB constraints: ensuring a set of
//! booleans is *At Most One (AMO)* or *At Most K (AMK)*. There are specialised
//! algorithms for these cases.

use std::cmp::Eq;
use std::hash::Hash;

/// The type used to represent boolean literals.
///
/// Literals implement [`std::ops::Neg`] to allow the adding of negated literals
/// to clauses and implement [`std::cmp::Eq`] and [`std::hash::Hash`] to allow
/// PB constraints to be simplified.
pub type Lit = i32;

/// The `ClauseDatabase` trait is the common trait implemented by types that are
/// used to manage the encoding of PB constraints and contain their output. This
/// trait can be used for all encoding methods in this library.
///
/// This trait is a supertrait of [`ClauseSink`], which means that implementers
/// should have a [`ClauseSink::add_clause`] method. Futhermore, implementers
/// are required to have a [`Self::new_lit`] method.
pub trait ClauseDatabase: ClauseSink {
    fn new_lit(&self) -> Lit;
}

/// Types that abide by the `ClauseSink` trait can be used as the output for the
/// constraint encodings. This trait also contains basic encodings that never
/// create new literals.
///
/// To satisfy the trait, the type must implement a
/// [`Self::add_clause`] method.
pub trait ClauseSink {
    /// Add a clause to the `ClauseSink`. The sink is allowed to return `false`
    /// only when the collection of clauses has been *proven* to be
    /// unsatisfiable. This is used as a signal to the encoder that any
    /// subsequent encoding effort can be abandoned.
    fn add_clause(&mut self, cl: &[Lit]) -> bool;

    /// Adds an encoding for an At Most One constraints to `sink` that for every
    /// pair of literals from `lits` states that one of the literals has to be
    /// `false`.
    ///
    /// # Undefined Behaviour
    ///
    /// - The literals in `lits` are assumed to the unique. In an AMO constraint
    ///   non-unique literals should be preprocessed removed from the problem.
    ///
    /// - `lits` is expected to contain at least 2 literals. In cases where an
    ///   AMO constraint has fewer literals, the literals can either be removed
    ///   for the problem or the problem is already unsatisfiable
    fn encode_naive_amo(&mut self, lits: &[Lit]) -> bool {
        // Precondition: there is no duplicate literals
        debug_assert!(unique_members(lits));
        // Precondition: there are multiple literals in the AMO constraint
        debug_assert!(lits.len() >= 2);
        // For every pair of literals (i, j) add "¬i ∨ ¬j"
        (0..lits.len()).into_iter().all(|i| {
            (i + 1..lits.len())
                .into_iter()
                .all(|j| self.add_clause(&[-lits[i], -lits[j]]))
        })
    }
}

impl ClauseSink for Vec<Vec<Lit>> {
    fn add_clause(&mut self, cl: &[Lit]) -> bool {
        self.push(cl.to_vec());
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
    use crate::{ClauseSink, Lit};
    use std::cmp::Eq;
    use std::hash::Hash;
    use std::ops::Neg;

    #[test]
    fn test_lit_properties() {
        let x: Lit = 1;
        assert_eq!(lit_properties(x), true);
    }
    fn lit_properties<T: Eq + Hash + Neg>(_: T) -> bool {
        true
    }

    #[test]
    fn test_naive_amo() {
        // AMO on two literals
        let mut two: Vec<Vec<Lit>> = vec![];
        two.encode_naive_amo(&[1, 2][..]);
        assert_eq!(two, vec![vec![-1, -2]]);
        // AMO on a negated literals
        let mut two: Vec<Vec<Lit>> = vec![];
        two.encode_naive_amo(&[-1, 2][..]);
        assert_eq!(two, vec![vec![1, -2]]);
        // AMO on three literals
        let mut two: Vec<Vec<Lit>> = vec![];
        two.encode_naive_amo(&[1, 2, 3][..]);
        assert_eq!(two, vec![vec![-1, -2], vec![-1, -3], vec![-2, -3]]);
    }
}
