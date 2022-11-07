use crate::{
	int::IntVarOrd, linear::totalizer::build_totalizer, CheckError, Checker, ClauseDatabase,
	Coefficient, LinExp, Literal, Unsatisfiable,
};
use iset::interval_map;
// use itertools::Itertools;
#[derive(Default)]
pub struct SortedEncoder {}

pub struct Sorted<'a, Lit: Literal> {
	xs: &'a [Lit],
}

impl<'a, Lit: Literal> Sorted<'a, Lit> {
	pub fn new(xs: &'a [Lit]) -> Self {
		Self { xs }
	}
}

impl<'a, Lit: Literal> Checker for Sorted<'a, Lit> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let _lhs: i32 = LinExp::from_terms(
			self.xs
				.iter()
				.map(|x| (x.clone(), 1))
				.collect::<Vec<_>>()
				.as_slice(),
		)
		.assign(solution);
		Ok(())
		// self.xs
		// 	.iter()
		// 	.map(|x| Sorted::<Lit>::assign(x, solution))
		// 	.tuple_windows(|(a, b)| !a.is_negated.cmp(!b.is_negated()))
	}
}

impl SortedEncoder {
	pub fn encode<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		con: &Sorted<DB::Lit>,
	) -> std::result::Result<LinExp<DB::Lit, C>, Unsatisfiable> {
		let xs = con
			.xs
			.iter()
			.enumerate()
			.map(|(i, x)| {
				IntVarOrd::new(
					db,
					interval_map! { C::one()..(C::one()+C::one()) => Some(x.clone()) },
					format!("x_{i}"),
				)
				.into()
			})
			.collect::<Vec<_>>();

		let root = build_totalizer(
			xs,
			db,
			C::zero(),
			con.xs.iter().fold(C::zero(), |acc, _| acc + C::one()),
			0,
			false,
			-C::one(),
		);
		Ok(LinExp::from(&root))
	}
}
