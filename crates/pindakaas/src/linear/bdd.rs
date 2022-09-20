use crate::linear::totalizer::{totalize, Structure};
use crate::linear::{ClauseDatabase, Encoder, Linear, Literal};
use crate::{PositiveCoefficient, Result};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
pub struct BddEncoder<Lit: Literal, PC: PositiveCoefficient> {
	lin: Linear<Lit, PC>,
}

impl<Lit: Literal, PC: PositiveCoefficient> BddEncoder<Lit, PC> {
	pub fn new(lin: Linear<Lit, PC>) -> Self {
		Self { lin }
	}
}

impl<Lit: Literal, PC: PositiveCoefficient> Encoder for BddEncoder<Lit, PC> {
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		totalize(db, &mut self.lin, Structure::Bdd)
	}
}
