use crate::{
	linear::LimitComp, CheckError, Checker, ClauseDatabase, Literal, Result, Unsatisfiable,
};

mod ladder;
mod pairwise;

pub use ladder::LadderEncoder;
pub use pairwise::PairwiseEncoder;

#[derive(Debug, Clone)]
pub struct CardinalityOne<Lit: Literal> {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
}

impl<Lit: Literal> Checker for CardinalityOne<Lit> {
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

pub(crate) fn at_least_one_clause<DB: ClauseDatabase>(
	db: &mut DB,
	card1: &CardinalityOne<DB::Lit>,
) -> Result {
	debug_assert_eq!(card1.cmp, LimitComp::Equal);
	db.add_clause(&card1.lits)
}

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! card1_test_suite {
		($encoder:expr) => {
			// ------ At Most One testing ------
			#[test]
			fn test_amo_pair() {
				assert_sol!(
					$encoder,
					2,
					&CardinalityOne {
						lits: vec![1, 2],
						cmp: LimitComp::LessEq
					}
					=> vec![vec![-1, -2], vec![1, -2], vec![-1, 2]]
				);
			}
			#[test]
			fn test_amo_one_neg() {
				assert_sol!(
					$encoder,
					2,
					&CardinalityOne {
						lits: vec![1, -2],
						cmp: LimitComp::LessEq
					}
					=> vec![vec![-1, -2], vec![-1, 2], vec![1, 2]]
				);
			}
			#[test]
			fn test_amo_neg_only() {
				assert_sol!(
					$encoder,
					2,
					&CardinalityOne {
						lits: vec![-1, -2],
						cmp: LimitComp::LessEq
					}
					=> vec![vec![-1, 2], vec![1, -2], vec![1, 2]]
				);
			}
			#[test]
			fn test_amo_triple() {
				assert_sol!(
					$encoder,
					3,
					&CardinalityOne {
						lits: vec![1, 2, 3],
						cmp: LimitComp::LessEq
					}
					=> vec![vec![-1, -2, -3], vec![1, -2, -3], vec![-1, 2, -3], vec![-1, -2, 3]]
				);
			}
			#[test]
			fn test_amo_large() {
				assert_sol!(
					$encoder,
					50,
					&CardinalityOne {
						lits: (1..=50).collect::<Vec<i32>>(),
						cmp: LimitComp::LessEq
					}
				);
			}
			#[test]
			fn test_amo_large_neg() {
				assert_sol!(
					$encoder,
					50,
					&CardinalityOne {
						lits: (-50..=-1).collect::<Vec<i32>>(),
						cmp: LimitComp::LessEq
					}
				);
			}
			#[test]
			fn test_amo_large_mix() {
				assert_sol!(
					$encoder,
					50,
					&CardinalityOne {
						lits: (1..=50).map(|i| if i % 2 != 0 { -i } else { i }).collect::<Vec<i32>>(),
						cmp: LimitComp::LessEq
					}
				);
			}
			// ------ At Most One testing ------
			#[test]
			fn test_eo_pair() {
				assert_sol!(
					$encoder,
					2,
					&CardinalityOne {
						lits: vec![1, 2],
						cmp: LimitComp::Equal
					}
					=> vec![vec![1, -2], vec![-1, 2]]
				);
			}
			#[test]
			fn test_eo_one_neg() {
				assert_sol!(
					$encoder,
					2,
					&CardinalityOne {
						lits: vec![1, -2],
						cmp: LimitComp::Equal
					}
					=> vec![vec![-1, -2], vec![1, 2]]
				);
			}
			#[test]
			fn test_eo_neg_only() {
				assert_sol!(
					$encoder,
					2,
					&CardinalityOne {
						lits: vec![-1, -2],
						cmp: LimitComp::Equal
					}
					=> vec![vec![-1, 2], vec![1, -2]]
				);
			}
			#[test]
			fn test_eo_triple() {
				assert_sol!(
					$encoder,
					3,
					&CardinalityOne {
						lits: vec![1, 2, 3],
						cmp: LimitComp::Equal
					}
					=> vec![vec![1, -2, -3], vec![-1, 2, -3], vec![-1, -2, 3]]
				);
			}
			#[test]
			fn test_eo_large() {
				assert_sol!(
					$encoder,
					50,
					&CardinalityOne {
						lits: (1..=50).collect::<Vec<i32>>(),
						cmp: LimitComp::Equal
					}
				);
			}
			#[test]
			fn test_eo_large_neg() {
				assert_sol!(
					$encoder,
					50,
					&CardinalityOne {
						lits: (-50..=-1).collect::<Vec<i32>>(),
						cmp: LimitComp::Equal
					}
				);
			}
			#[test]
			fn test_eo_large_mix() {
				assert_sol!(
					$encoder,
					50,
					&CardinalityOne {
						lits: (1..=50).map(|i| if i % 2 != 0 { -i } else { i }).collect::<Vec<i32>>(),
						cmp: LimitComp::Equal
					}
				);
			}

		};
	}
	pub(crate) use card1_test_suite;
}
