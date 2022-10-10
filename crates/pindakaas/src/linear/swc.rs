use crate::linear::totalizer::{totalize, Structure};
use crate::{ClauseDatabase, Encoder, Linear, PositiveCoefficient, Result};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
#[derive(Default)]
pub struct SwcEncoder {
	add_consistency: bool,
}

impl SwcEncoder {
	pub fn add_consistency(&mut self, b: bool) {
		self.add_consistency = b;
	}
}

impl<DB: ClauseDatabase, PC: PositiveCoefficient> Encoder<DB, Linear<DB::Lit, PC>> for SwcEncoder {
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, PC>) -> Result {
		totalize(db, lin, Structure::Swc, self.add_consistency)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Checker,
		Encoder,
	};

	linear_test_suite!(SwcEncoder::default());
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
