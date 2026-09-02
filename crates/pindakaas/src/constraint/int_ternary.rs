//! `x + y ≷ z` over integer terms, and the encoder for it.
//!
//! Every decomposition strategy in [`int_linear`](super::int_linear) breaks a
//! longer constraint into these, so this is the one shape that is encoded
//! directly rather than broken up further.

pub use crate::encoder::int_ternary::{IntTernaryConfig, IntTernaryEncoder};
use crate::constraint::{
	bool_linear::Comparator,
	int_linear::{term_negated, IntLinear, Term},
};

/// A linear constraint over three integer terms, `x + y ≷ z`.
///
/// This is what a decomposition breaks a longer constraint into. The strategies
/// differ in the shape they give the intermediate sums — a chain, a balanced
/// tree, the layers of a decision diagram — but every step of every one of them
/// is the same thing: two terms, and where they come to together. Saying so in
/// the type keeps a decomposition from having to express it as a constraint of
/// any shape at all, which the encoder would then have to recognise again.
///
/// It is not a [`NormalizedIntLinear`](super::int_linear::NormalizedIntLinear):
/// `z` stands on the other side of the comparison, and moving it across would
/// mean a view of it counting the other way rather than a constant.
#[derive(Clone, Debug)]
pub struct IntTernary {
	pub(crate) x: Term,
	pub(crate) y: Term,
	pub(crate) cmp: Comparator,
	pub(crate) z: Term,
}

impl IntTernary {
	/// The constraint `x + y ≷ z`.
	pub fn new(x: Term, y: Term, cmp: Comparator, z: Term) -> Self {
		Self { x, y, cmp, z }
	}

	/// The comparator of the constraint.
	pub fn cmp(&self) -> Comparator {
		self.cmp
	}

	/// The two terms that are added together.
	pub fn addends(&self) -> (&Term, &Term) {
		(&self.x, &self.y)
	}

	/// The term they are compared against.
	pub fn total(&self) -> &Term {
		&self.z
	}
}

impl From<&IntTernary> for IntLinear {
	/// A term over a variable of one value is what it is worth, so it belongs
	/// with the constant rather than among the terms.
	fn from(con: &IntTernary) -> Self {
		let (mut terms, mut k) = (Vec::new(), 0);
		for (term, adds) in [(&con.x, true), (&con.y, true), (&con.z, false)] {
			if term.1.card() == 1 {
				let worth = term.0 * term.1.min();
				k += if adds { -worth } else { worth };
			} else {
				terms.push(if adds {
					term.clone()
				} else {
					term_negated(term)
				});
			}
		}
		Self::new(terms, con.cmp, k)
	}
}
