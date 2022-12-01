use crate::{
	linear::LimitComp, trace::emit_clause, CheckError, Checker, ClauseDatabase, Literal, Result,
	Unsatisfiable,
};

mod bitwise;
mod ladder;
mod pairwise;

pub use bitwise::BitwiseEncoder;
pub use ladder::LadderEncoder;
pub use pairwise::PairwiseEncoder;

#[derive(Debug, Clone)]
pub struct CardinalityOne<Lit: Literal> {
	pub(crate) lits: Vec<Lit>,
	pub(crate) cmp: LimitComp,
}

impl<Lit: Literal> CardinalityOne<Lit> {
	#[cfg(feature = "trace")]
	pub(crate) fn trace_print(&self) -> String {
		let x = itertools::join(self.lits.iter().map(|l| format!("{{{l:?}}}")), " + ");
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} 1")
	}
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
		if match self.cmp {
			LimitComp::LessEq => count <= 1,
			LimitComp::Equal => count == 1,
		} {
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
	emit_clause!(db, &card1.lits)
}

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! card1_test_suite {
		($encoder:expr) => {
            const LARGE_N: i32 = 50;
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
					LARGE_N,
					&CardinalityOne {
						lits: (1..=LARGE_N).collect::<Vec<i32>>(),
						cmp: LimitComp::LessEq
					}
				);
			}
			#[test]
			fn test_amo_large_neg() {
				assert_sol!(
					$encoder,
					LARGE_N,
					&CardinalityOne {
						lits: (-LARGE_N..=-1).collect::<Vec<i32>>(),
						cmp: LimitComp::LessEq
					}
				);
			}
			#[test]
			fn test_amo_large_mix() {
				assert_sol!(
					$encoder,
					LARGE_N,
					&CardinalityOne {
						lits: (1..=LARGE_N).map(|i| if i % 2 != 0 { -i } else { i }).collect::<Vec<i32>>(),
						cmp: LimitComp::LessEq
					}
				);
			}
			// ------ Exactly One testing ------
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
					LARGE_N,
					&CardinalityOne {
						lits: (1..=LARGE_N).collect::<Vec<i32>>(),
						cmp: LimitComp::Equal
					}
				);
			}
			#[test]
			fn test_eo_large_neg() {
				assert_sol!(
					$encoder,
					LARGE_N,
					&CardinalityOne {
						lits: (-LARGE_N..=-1).collect::<Vec<i32>>(),
						cmp: LimitComp::Equal
					}
				);
			}
			#[test]
			fn test_eo_large_mix() {
				assert_sol!(
					$encoder,
					LARGE_N,
					&CardinalityOne {
						lits: (1..=LARGE_N).map(|i| if i % 2 != 0 { -i } else { i }).collect::<Vec<i32>>(),
						cmp: LimitComp::Equal
					}
				);
			}

		};
	}
	pub(crate) use card1_test_suite;
}
