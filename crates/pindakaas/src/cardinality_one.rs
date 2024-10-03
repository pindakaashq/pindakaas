use crate::{
	linear::{LimitComp, Linear},
	trace::emit_clause,
	CheckError, Checker, ClauseDatabase, Lit, Result, Valuation,
};

mod bitwise;
mod ladder;
mod pairwise;

pub use bitwise::BitwiseEncoder;
pub use ladder::LadderEncoder;
pub use pairwise::PairwiseEncoder;

#[derive(Debug, Clone)]
pub struct CardinalityOne {
	pub lits: Vec<Lit>,
	pub cmp: LimitComp,
}

impl CardinalityOne {
	#[cfg(feature = "trace")]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(self.lits.iter().map(trace_print_lit), " + ");
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} 1")
	}
}

impl Checker for CardinalityOne {
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<(), CheckError> {
		Linear::from(self.clone()).check(value)
	}
}

pub(crate) fn at_least_one_clause<DB: ClauseDatabase>(
	db: &mut DB,
	card1: &CardinalityOne,
) -> Result {
	debug_assert_eq!(card1.cmp, LimitComp::Equal);
	emit_clause!(db, card1.lits.iter().copied())
}

#[cfg(test)]
pub(crate) mod tests {
	macro_rules! card1_test_suite {
		($encoder:expr) => {
			const LARGE_N: usize = 50;
			// ------ At Most One testing ------
			#[test]
			fn test_amo_pair() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![a, b],
							cmp: LimitComp::LessEq,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b],
					&expect_file!["cardinality_one/test_amo_pair.sol"],
				);
			}
			#[test]
			fn test_amo_one_neg() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![a, !b],
							cmp: LimitComp::LessEq,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b],
					&expect_file!["cardinality_one/test_amo_one_neg.sol"],
				);
			}
			#[test]
			fn test_amo_neg_only() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![!a, !b],
							cmp: LimitComp::LessEq,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b],
					&expect_file!["cardinality_one/test_amo_neg_only.sol"],
				);
			}
			#[test]
			fn test_amo_triple() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				let c = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![a, b, c],
							cmp: LimitComp::LessEq,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b, c],
					&expect_file!["cardinality_one/test_amo_triple.sol"],
				);
			}
			#[test]
			fn test_amo_large() {
				let mut cnf = Cnf::default();
				let vars = cnf
					.next_var_range(LARGE_N)
					.unwrap()
					.iter_lits()
					.collect_vec();
				let con = CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::LessEq,
				};
				$encoder.encode(&mut cnf, &con).unwrap();

				assert_checker(&cnf, &con);
			}
			#[test]
			fn test_amo_large_neg() {
				let mut cnf = Cnf::default();
				let vars = cnf
					.next_var_range(LARGE_N)
					.unwrap()
					.iter_lits()
					.collect_vec();
				let con = CardinalityOne {
					lits: vars.clone().into_iter().map(|l| !l).collect_vec(),
					cmp: LimitComp::LessEq,
				};
				$encoder.encode(&mut cnf, &con).unwrap();

				assert_checker(&cnf, &con);
			}
			#[test]
			fn test_amo_large_mix() {
				let mut cnf = Cnf::default();
				let vars = cnf
					.next_var_range(LARGE_N)
					.unwrap()
					.iter_lits()
					.collect_vec();

				let con = CardinalityOne {
					lits: vars
						.clone()
						.into_iter()
						.enumerate()
						.map(|(i, l)| if i % 2 == 0 { l } else { !l })
						.collect_vec(),
					cmp: LimitComp::LessEq,
				};
				$encoder.encode(&mut cnf, &con).unwrap();

				assert_checker(&cnf, &con);
			}
			// ------ Exactly One testing ------
			#[test]
			fn test_eo_pair() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![a, b],
							cmp: LimitComp::Equal,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b],
					&expect_file!["cardinality_one/test_eo_pair.sol"],
				);
			}
			#[test]
			fn test_eo_one_neg() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![a, !b],
							cmp: LimitComp::Equal,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b],
					&expect_file!["cardinality_one/test_eo_one_neg.sol"],
				);
			}
			#[test]
			fn test_eo_neg_only() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![!a, !b],
							cmp: LimitComp::Equal,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b],
					&expect_file!["cardinality_one/test_eo_neg_only.sol"],
				);
			}
			#[test]
			fn test_eo_triple() {
				let mut cnf = Cnf::default();
				let a = cnf.new_lit();
				let b = cnf.new_lit();
				let c = cnf.new_lit();
				$encoder
					.encode(
						&mut cnf,
						&CardinalityOne {
							lits: vec![a, b, c],
							cmp: LimitComp::Equal,
						},
					)
					.unwrap();

				assert_solutions(
					&cnf,
					vec![a, b, c],
					&expect_file!["cardinality_one/test_eo_triple.sol"],
				);
			}
			#[test]
			fn test_eo_large() {
				let mut cnf = Cnf::default();
				let vars = cnf
					.next_var_range(LARGE_N)
					.unwrap()
					.iter_lits()
					.collect_vec();
				let con = CardinalityOne {
					lits: vars.clone(),
					cmp: LimitComp::Equal,
				};
				$encoder.encode(&mut cnf, &con).unwrap();

				assert_checker(&cnf, &con);
			}
			#[test]
			fn test_eo_large_neg() {
				let mut cnf = Cnf::default();
				let vars = cnf
					.next_var_range(LARGE_N)
					.unwrap()
					.iter_lits()
					.collect_vec();
				let con = CardinalityOne {
					lits: vars.clone().iter().map(|l| !l).collect_vec(),
					cmp: LimitComp::Equal,
				};
				$encoder.encode(&mut cnf, &con).unwrap();

				assert_checker(&cnf, &con);
			}
			#[test]
			fn test_eo_large_mix() {
				let mut cnf = Cnf::default();
				let vars = cnf
					.next_var_range(LARGE_N)
					.unwrap()
					.iter_lits()
					.collect_vec();
				let con = CardinalityOne {
					lits: vars
						.clone()
						.into_iter()
						.enumerate()
						.map(|(i, l)| if i % 2 == 0 { l } else { !l })
						.collect_vec(),
					cmp: LimitComp::Equal,
				};
				$encoder.encode(&mut cnf, &con).unwrap();

				assert_checker(&cnf, &con);
			}
		};
	}
	pub(crate) use card1_test_suite;
}
