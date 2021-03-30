//! `pindakaas` is a collection of encoders to transform pseudo-Boolean (PB)
//! constraints into conjunctive normal form (CNF). PB constraint are in the
//! form ∑ aᵢ·xᵢ ≷ c, where the aᵢ's and c are constant, xᵢ's are boolean
//! literals, and ≷ can be the relationship ≤, =, or ≥. Two forms of PB
//! constraints are seen as special forms of PB constraints: ensuring a set of
//! booleans is *At Most One (AMO)* or *At Most K (AMK)*. There are specialised
//! algorithms for these cases.

use std::cmp::Eq;
use std::hash::Hash;

/// The type used to represent boolean literals. Literals implement
/// [`std::ops::Neg`] to allow the adding of negated literals to clauses and
/// implement [`std::cmp::Eq`] and [`std::hash::Hash`] to allow PB constraints
/// to be simplified.
type Lit = i32;

pub trait ClauseSink {
    fn add_clause(&mut self, cl: &[Lit]) -> bool;
}

impl ClauseSink for Vec<Vec<Lit>> {
    fn add_clause(&mut self, cl: &[Lit]) -> bool {
        self.push(cl.to_vec());
        true
    }
}

pub trait LiteralGenerator {
    fn new_lit(&self) -> Lit;
}

fn is_unique<T: Hash + Eq>(collection: &[T]) -> bool {
    collection
        .into_iter()
        .collect::<std::collections::HashSet<_>>()
        .len()
        == collection.len()
}

/// Adds an encoding for an At Most One constraints to `sink` that for every
/// pair of literals from `lits` states that one of the literals has to be
/// `false`.
///
/// # Undefined Behaviour
///
/// The literals in `lits` are assumed to the unique. In an AMO constraint
/// non-unique literals should be preprocessed removed from the problem.
pub fn naive_amo(lits: &[Lit], sink: &mut dyn ClauseSink) -> bool {
    // Assume that there is no duplicate
    debug_assert!(is_unique(lits));
    (0..lits.len()).into_iter().all(|i| {
        (i..lits.len())
            .into_iter()
            .all(|j| sink.add_clause(&[-lits[i], -lits[j]]))
    })
}

#[cfg(test)]
mod tests {
    use crate::Lit;
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
}
