//! Sorting network constraints, `Σ xs ≷ y`, where `y` is an integer variable
//! rather than a constant.
//!
//! A [`Sorted`] constraint is a cardinality constraint whose right-hand side
//! can itself be constrained, which is what lets one be counted into a variable
//! that another constraint then reads.

use itertools::Itertools;

pub use crate::encoder::sorted::{SortedEncoder, SortedStrategy};
use crate::{
	bool_linear::{LimitComp, LinExp},
	decision::integer::IntVar,
	Checker, Lit, Result, Unsatisfiable, Valuation,
};

/// The constraint that the literals `xs` add up to the integer `y`.
///
/// A cardinality constraint with an integer on the right, so that what was
/// counted is available to whatever else mentions `y`.
#[derive(Debug, Clone)]
pub struct Sorted<'a> {
	pub(crate) xs: &'a [Lit],
	pub(crate) cmp: LimitComp,
	pub(crate) y: &'a IntVar,
}

impl<'a> Sorted<'a> {
	pub(crate) fn new(xs: &'a [Lit], cmp: LimitComp, y: &'a IntVar) -> Self {
		Self { xs, cmp, y }
	}
}

impl Checker for Sorted<'_> {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<()> {
		let lhs = LinExp::from_terms(self.xs.iter().map(|x| (*x, 1)).collect_vec().as_slice())
			.value(sol)?;
		let rhs = self.y.value(sol);

		if match self.cmp {
			LimitComp::LessEq => lhs <= rhs,
			LimitComp::Equal => lhs == rhs,
		} {
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}
}
