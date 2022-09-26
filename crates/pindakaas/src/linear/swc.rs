use crate::linear::totalizer::{totalize, Structure};
use crate::linear::{ClauseDatabase, Encoder, Linear, Literal};
use crate::{PositiveCoefficient, Result};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
pub struct SwcEncoder<'a, Lit: Literal, PC: PositiveCoefficient> {
	lin: &'a Linear<Lit, PC>,
	add_consistency: bool,
}

impl<'a, Lit: Literal, PC: PositiveCoefficient> SwcEncoder<'a, Lit, PC> {
	pub fn new(lin: &'a Linear<Lit, PC>, add_consistency: bool) -> Self {
		Self {
			lin,
			add_consistency,
		}
	}
}

impl<'a, Lit: Literal, PC: PositiveCoefficient> Encoder for SwcEncoder<'a, Lit, PC> {
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		totalize(db, self.lin, Structure::Swc, self.add_consistency)
	}
}
