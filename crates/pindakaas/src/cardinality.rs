use crate::{
	linear::{LimitComp, LinMarker},
	AtMostOne, CheckError, Checker, ClauseDatabase, Encoder, Literal, PositiveCoefficient,
	Unsatisfiable,
};

#[derive(Clone, Debug)]
pub struct Cardinality<Lit: Literal, PC: PositiveCoefficient> {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PC,
}

impl<Lit: Literal, PC: PositiveCoefficient> From<AtMostOne<Lit>> for Cardinality<Lit, PC> {
	fn from(amo: AtMostOne<Lit>) -> Self {
		Self {
			lits: amo.lits,
			cmp: LimitComp::LessEq,
			k: PC::one(),
		}
	}
}

impl<Lit: Literal, PC: PositiveCoefficient> Checker for Cardinality<Lit, PC> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		let count = self
			.lits
			.iter()
			.filter(|lit| {
				let v = solution.iter().find(|x| x.var() == lit.var());
				*lit == v.unwrap()
			})
			.fold(PC::zero(), |acc, _| acc + PC::one());
		if match self.cmp {
			LimitComp::LessEq => count <= self.k,
			LimitComp::Equal => count == self.k,
		} {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

// Automatically implement AtMostOne encoding when you can encode Cardinality constraints
impl<DB: ClauseDatabase, Enc: Encoder<DB, Cardinality<DB::Lit, u8>> + CardMarker>
	Encoder<DB, AtMostOne<DB::Lit>> for Enc
{
	fn encode(&mut self, db: &mut DB, con: &AtMostOne<DB::Lit>) -> crate::Result {
		self.encode(db, &Cardinality::<DB::Lit, u8>::from(con.clone()))
	}
}
// local marker trait, to ensure the previous definition only applies within this crate
pub(crate) trait CardMarker {}
impl<T: LinMarker> CardMarker for T {}
