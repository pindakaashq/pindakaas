use crate::{CheckError, Checker, Literal, Unsatisfiable};

mod ladder;
mod pairwise;

pub use ladder::LadderEncoder;
pub use pairwise::PairwiseEncoder;

#[derive(Debug)]
pub struct AtMostOne<Lit: Literal> {
	pub(crate) lits: Vec<Lit>,
}

impl<Lit: Literal> Checker for AtMostOne<Lit> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		let abs = |l: Lit| if l.is_negated() { l.negate() } else { l };
		let count = self
			.lits
			.iter()
			.filter(|lit| {
				let v = solution
					.iter()
					.find(|x| abs((*x).clone()) == abs((*lit).clone()));
				*lit == v.unwrap()
			})
			.count();
		if count <= 1 {
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}
