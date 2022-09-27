use crate::linear::totalizer::{totalize, Structure};
use crate::linear::{ClauseDatabase, Encoder, Linear, Literal};
use crate::{PositiveCoefficient, Result};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
pub struct BddEncoder<'a, Lit: Literal, PC: PositiveCoefficient> {
	lin: &'a Linear<Lit, PC>,
}

impl<'a, Lit: Literal, PC: PositiveCoefficient> BddEncoder<'a, Lit, PC> {
	pub fn new(lin: &'a Linear<Lit, PC>) -> Self {
		Self { lin }
	}
}

impl<'a, Lit: Literal, PC: PositiveCoefficient> Encoder for BddEncoder<'a, Lit, PC> {
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		totalize(db, self.lin, Structure::Bdd)
	}
}
