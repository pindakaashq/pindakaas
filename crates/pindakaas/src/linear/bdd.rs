use crate::linear::totalizer::{totalize, Structure};
use crate::{ClauseDatabase, Encoder, Linear, PositiveCoefficient, Result};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
#[derive(Default)]
pub struct BddEncoder {
	add_consistency: bool,
}

impl BddEncoder {
	pub fn add_consistency(&mut self, b: bool) {
		self.add_consistency = b;
	}
}

impl<DB: ClauseDatabase, PC: PositiveCoefficient> Encoder<DB, Linear<DB::Lit, PC>> for BddEncoder {
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, PC>) -> Result {
		totalize(db, lin, Structure::Bdd, self.add_consistency)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		at_most_one::tests::amo_test_suite,
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		AtMostOne, Checker, Encoder,
	};
	linear_test_suite!(BddEncoder::default());
	amo_test_suite!(BddEncoder::default());
}
