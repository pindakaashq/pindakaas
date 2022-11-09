use crate::{
	int::{IntVarEnc, IntVarOrd},
	linear::{totalizer::build_totalizer, LimitComp},
	CheckError, Checker, ClauseDatabase, Encoder, LinExp, Literal, Result, Unsatisfiable,
};
use iset::{interval_map, IntervalMap};

#[derive(Default)]
pub struct SortedEncoder {}

pub struct Sorted<'a, Lit: Literal> {
	pub(crate) xs: &'a [Lit],
	pub(crate) cmp: LimitComp,
	pub(crate) ys: &'a [Lit],
}

impl<'a, Lit: Literal> Sorted<'a, Lit> {
	pub(crate) fn new(xs: &'a [Lit], cmp: LimitComp, ys: &'a [Lit]) -> Self {
		Self { xs, cmp, ys }
	}
}

impl<'a, Lit: Literal> Checker for Sorted<'a, Lit> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let lhs = LinExp::from_terms(
			self.xs
				.iter()
				.map(|x| (x.clone(), 1))
				.collect::<Vec<_>>()
				.as_slice(),
		)
		.assign(solution)? as usize;

		let rhs = self
			.ys
			.iter()
			.map(|y| Self::assign(y, solution))
			.collect::<Vec<_>>();

		let rhs_eq = LinExp::new()
			.add_chain(
				self.ys
					.iter()
					.map(|y| (y.clone(), 1))
					.collect::<Vec<_>>()
					.as_slice(),
			)
			.assign(solution)? as usize;

		if self.cmp == LimitComp::LessEq && (lhs == 0 || !rhs[lhs - 1].is_negated())
			|| (self.cmp == LimitComp::Equal && lhs == rhs_eq)
		{
			Ok(())
		} else {
			Err(CheckError::Unsatisfiable(Unsatisfiable))
		}
	}
}

impl<DB: ClauseDatabase> Encoder<DB, Sorted<'_, DB::Lit>> for SortedEncoder {
	fn encode(&mut self, db: &mut DB, sorted: &Sorted<DB::Lit>) -> Result {
		let xs = sorted
			.xs
			.iter()
			.enumerate()
			.map(|(i, x)| {
				IntVarOrd::new(
					db,
					interval_map! { 1..2 => Some(x.clone()) },
					format!("x_{i}"),
				)
				.into()
			})
			.collect::<Vec<_>>();

		let n = (sorted.xs.len() + 1) as i64;

		let y = IntVarOrd::new(
			db,
			IntervalMap::from_sorted(
				num::iter::range_inclusive(1, n)
					.zip(sorted.ys.iter())
					.map(|(i, y)| (i..i + 1, Some(y.clone()))),
			),
			"y".to_string(),
		)
		.into();

		let y = build_totalizer(xs, db, 0, 0, false, None, y);

		if let IntVarEnc::Ord(o) = y {
			o.consistent(db)
		} else {
			unreachable!()
		}
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::helpers::tests::{assert_sol, TestDB};

	#[test]
	fn test_small_sorted() {
		let mut db = TestDB::new(4);
		let con = &Sorted::new(&[1, 2], LimitComp::LessEq, &[3, 4]);
		let sols = vec![
			vec![-1, -2, -3, -4],
			vec![-1, -2, -3, 4],
			vec![-1, -2, 3, -4],
			vec![-1, -2, 3, 4],
			vec![-1, 2, 3, -4],
			vec![-1, 2, 3, 4],
			vec![1, -2, 3, -4],
			vec![1, -2, 3, 4],
			// vec![1, 2, -3, 4],
			vec![1, 2, 3, 4],
		];
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}
}
