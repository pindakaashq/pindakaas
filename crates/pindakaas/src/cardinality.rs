use crate::{linear::LimitComp, CheckError, Checker, Literal, PositiveCoefficient, Unsatisfiable};

#[derive(Debug)]
pub struct Cardinality<Lit: Literal, PC: PositiveCoefficient> {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PC,
}

impl<Lit, PC> From<AtMostOne<Lit>> for Cardinality<Lit, PC> {
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
