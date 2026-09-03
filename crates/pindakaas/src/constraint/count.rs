//! Counting literals into an integer, `Σ lits ≷ y`.
//!
//! A cardinality constraint whose bound is a variable rather than a constant,
//! so that what was counted is available to whatever else mentions `y`. A
//! sorting network states it directly, where going through a general linear
//! constraint would count into intermediate integers first.

use itertools::Itertools;

pub use crate::encoder::sorted::{SortedEncoder, SortedStrategy};
use crate::{
	constraint::linear::{LimitComp, LinExp},
	decision::integer::IntVar,
	Checker, Lit, Result, Unsatisfiable, Valuation,
};

/// The constraint that `lits` add up to the integer `y`.
#[derive(Debug, Clone)]
pub struct Count {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) y: IntVar,
}

impl Count {
	/// The constraint that `lits` add up to `y`, or to at most `y`.
	pub fn new(lits: Vec<Lit>, cmp: LimitComp, y: IntVar) -> Self {
		Self { lits, cmp, y }
	}
}

impl Checker for Count {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<()> {
		let lhs = LinExp::from_terms(self.lits.iter().map(|x| (*x, 1)).collect_vec().as_slice())
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
