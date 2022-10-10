use crate::{CheckError, Checker, Literal, Unsatisfiable};

mod ladder;
mod pairwise;

pub use ladder::LadderEncoder;
pub use pairwise::PairwiseEncoder;

// TODO: Should be changed to support either AMO or ExactlyOne
#[derive(Debug, Clone)]
pub struct AtMostOne<Lit: Literal> {
	pub(crate) lits: Vec<Lit>,
}

impl<Lit: Literal> Checker for AtMostOne<Lit> {
	type Lit = Lit;

	fn check(&self, solution: &[Self::Lit]) -> Result<(), crate::CheckError<Self::Lit>> {
		let count = self
			.lits
			.iter()
			.filter(|lit| {
				let v = solution.iter().find(|x| x.var() == lit.var());
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

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! amo_test_suite {
		($encoder:expr) => {
			#[test]
			fn test_amo_pair() {
				assert_sol!(
					$encoder,
					2,
					&AtMostOne {
						lits: vec![1, 2]
					}
					=> vec![vec![-1, -2], vec![1, -2], vec![-1, 2]]
				);
			}
			#[test]
			fn test_amo_one_neg() {
				assert_sol!(
					$encoder,
					2,
					&AtMostOne {
						lits: vec![1, -2]
					}
					=> vec![vec![-1, -2], vec![-1, 2], vec![1, 2]]
				);
			}
			#[test]
			fn test_amo_neg_only() {
				assert_sol!(
					$encoder,
					2,
					&AtMostOne {
						lits: vec![-1, -2]
					}
					=> vec![vec![-1, 2], vec![1, -2], vec![1, 2]]
				);
			}
			#[test]
			fn test_amo_triple() {
				assert_sol!(
					$encoder,
					3,
					&AtMostOne {
						lits: vec![1, 2, 3]
					}
					=> vec![vec![-1, -2, -3], vec![1, -2, -3], vec![-1, 2, -3], vec![-1, -2, 3]]
				);
			}
			#[test]
			fn test_amo_large() {
				assert_sol!(
					$encoder,
					50,
					&AtMostOne {
						lits: (1..=50).collect::<Vec<i32>>()
					}
				);
			}
			#[test]
			fn test_amo_large_neg() {
				assert_sol!(
					$encoder,
					50,
					&AtMostOne {
						lits: (-50..=-1).collect::<Vec<i32>>()
					}
				);
			}
			#[test]
			fn test_amo_large_mix() {
				assert_sol!(
					$encoder,
					50,
					&AtMostOne {
						lits: (1..=50).map(|i| if i % 2 != 0 { -i } else { i }).collect::<Vec<i32>>()
					}
				);
			}
		};
	}
	pub(crate) use amo_test_suite;
}
