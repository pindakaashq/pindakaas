use crate::totalizer::{totalize, Structure};
use crate::{ClauseDatabase, Comparator, Literal, Part, PositiveCoefficient, Result};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a sequential weight counter
pub fn encode_bool_lin_le_swc<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	partition: &[Part<Lit, PC>],
	cmp: Comparator,
	k: PC,
) -> Result {
	totalize(db, partition, cmp, k, Structure::Swc)
}
