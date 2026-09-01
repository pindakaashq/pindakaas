//! What a general Boolean linear constraint turns out to be once its terms
//! have been read.
//!
//! [`BoolLinAggregator`](crate::encoder::aggregate::BoolLinAggregator) reads a
//! [`Linear`](crate::constraint::bool_linear::Linear) and reports which of
//! these it is, so that a narrower constraint can be given to an encoder that
//! specialises in it.

pub use crate::encoder::aggregate::{BoolLinAggregator, LinearEncoder, StaticLinEncoder};
use crate::{
	cardinality::Cardinality, constraint::cardinality_one::CardinalityOne,
	int_linear::NormalizedIntLinear,
};

#[derive(Debug)]
/// What a linear constraint turned out to be once aggregated.
///
/// Aggregation works out which terms belong together and what relates them,
/// and hands the general case on as a constraint over the integers those
/// groups encode. What it recognises as counting rather than weighing keeps a
/// form of its own, there being encoders that do only that.
pub enum LinVariant {
	/// Most general form: a sum of integer terms that must be
	/// (smaller-or-)equal to a constant. The groups the aggregator recognised
	/// have each become an integer, encoded on the literals they were found on.
	Linear(NormalizedIntLinear),
	/// Cardinality constraint (also known as a counting constraint): a sum of
	/// Boolean literals that must be (smaller-or-)equal to a positive constant.
	Cardinality(Cardinality),
	/// Cardinality constraint with the constant 1 (i.e. at-least or exactly 1
	/// literal must be true).
	CardinalityOne(CardinalityOne),
	/// Constraint was trivially encoded into clauses.
	Trivial,
}
