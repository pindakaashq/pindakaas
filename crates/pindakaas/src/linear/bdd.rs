use crate::linear::totalizer::{totalize, Structure};
use crate::{ClauseDatabase, Encoder, Linear, PositiveCoefficient, Result};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
pub struct BddEncoder {
	add_consistency: bool,
}

impl BddEncoder {
	pub fn add_consistency(&mut self, b: bool) {
		self.add_consistency = b;
	}
}

impl Default for BddEncoder {
	fn default() -> Self {
		Self {
			add_consistency: false,
		}
	}
}

impl<DB: ClauseDatabase, PC: PositiveCoefficient> Encoder<DB, Linear<DB::Lit, PC>> for BddEncoder {
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, PC>) -> Result {
		totalize(db, lin, Structure::Bdd, self.add_consistency)
	}
}
