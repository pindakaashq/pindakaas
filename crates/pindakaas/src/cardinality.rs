use crate::{
	linear::{LimitComp, LinMarker, PosCoeff},
	CardinalityOne, CheckError, Checker, ClauseDatabase, Coefficient, Encoder, Literal,
	Unsatisfiable,
};

#[derive(Clone, Debug)]
pub struct Cardinality<Lit: Literal, C: Coefficient> {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff<C>,
}

impl<Lit: Literal, C: Coefficient> From<CardinalityOne<Lit>> for Cardinality<Lit, C> {
	fn from(card1: CardinalityOne<Lit>) -> Self {
		Self {
			lits: card1.lits,
			cmp: card1.cmp,
			k: C::one().into(),
		}
	}
}

impl<Lit: Literal, C: Coefficient> Checker for Cardinality<Lit, C> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		let count = self
			.lits
			.iter()
			.filter(|lit| {
				let v = solution.iter().find(|x| x.var() == lit.var());
				*lit == v.unwrap()
			})
			.fold(C::zero(), |acc, _| acc + C::one());
		if match self.cmp {
			LimitComp::LessEq => count <= *self.k,
			LimitComp::Equal => count == *self.k,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

// Automatically implement AtMostOne encoding when you can encode Cardinality constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Cardinality<DB::Lit, i8>> + CardMarker>
	Encoder<DB, CardinalityOne<DB::Lit>> for Enc
{
	fn encode(&mut self, db: &mut DB, con: &CardinalityOne<DB::Lit>) -> crate::Result {
		self.encode(db, &Cardinality::<DB::Lit, i8>::from(con.clone()))
	}
}
// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait CardMarker {}
impl<T: LinMarker> CardMarker for T {}
