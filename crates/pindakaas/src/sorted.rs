use crate::{
	int::{IntVarEnc, IntVarOrd},
	linear::{totalizer::build_totalizer, LimitComp},
	trace::emit_clause,
	CheckError, Checker, ClauseDatabase, Coefficient, Encoder, LinExp, Literal, Result,
	Unsatisfiable,
};
use iset::{interval_map, IntervalMap};
use itertools::Itertools;

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
			})
			.collect::<Vec<_>>();

		let n = (sorted.xs.len() + 1) as i32;
		let y = IntVarOrd::new(
			db,
			IntervalMap::from_sorted(
				num::iter::range_inclusive(1, n)
					.zip(sorted.ys.iter())
					.map(|(i, y)| (i..i + 1, Some(y.clone()))),
			),
			"y".to_string(),
		);

		match sorted.cmp {
			LimitComp::LessEq => {
				let y = build_totalizer(
					xs.into_iter().map_into().collect::<Vec<_>>(),
					db,
					0,
					0,
					false,
					None,
					y.into(),
				);

				if let IntVarEnc::Ord(o) = y {
					o.consistent(db)
				} else {
					unreachable!()
				}
			}
			LimitComp::Equal => self.sorted(db, &xs, &y, 0),
		}
	}
}

impl SortedEncoder {
	fn next_int_var<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		ub: C,
		lbl: String,
	) -> IntVarOrd<DB::Lit, C> {
		IntVarOrd::new(
			db,
			IntervalMap::from_sorted(
				num::iter::range_inclusive(C::one(), ub).map(|i| (i..(i + C::one()), None)),
			),
			lbl,
		)
	}

	fn sorted<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		// mut xs: Vec<IntVarOrd<DB::Lit, C>>,
		xs: &[IntVarOrd<DB::Lit, C>],
		y: &IntVarOrd<DB::Lit, C>,
		_lvl: usize,
	) -> Result {
		// TODO: Add tracing
		// eprintln!("sorted([{}], {})", xs.iter().join(", "), y);
		match xs {
			[] => Ok(()),
			[x] => {
				x.xs.values(..)
					.zip(y.xs.values(..))
					.try_for_each(|(x, y)| self.equiv(db, x, y, _lvl + 1))?;
				x.xs.values((y.ub() + C::one())..)
					.try_for_each(|x| emit_clause!(db, &[x.negate()]))
			}
			[x1, x2] => self.comp(db, x1, x2, y, _lvl + 1),
			xs => {
				let n = xs.len() / 2;
				let m = std::cmp::min((0..n).fold(C::zero(), |a, _| a + C::one()), y.ub());
				let y1 = self.next_int_var(db, m, String::from("y_1"));
				let m_ = std::cmp::min((n..xs.len()).fold(C::zero(), |a, _| a + C::one()), y.ub());
				let y2 = self.next_int_var(db, m_, String::from("y_2"));
				self.sorted(db, &xs[..n], &y1, _lvl)?;
				self.sorted(db, &xs[n..], &y2, _lvl)?;
				self.merged(db, &y1, &y2, y, _lvl + 1)
			}
		}
	}

	fn merged<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		x1: &IntVarOrd<DB::Lit, C>,
		x2: &IntVarOrd<DB::Lit, C>,
		y: &IntVarOrd<DB::Lit, C>,
		_lvl: usize,
	) -> Result {
		// TODO: Add tracing
		// eprintln!("{:_lvl$}merged({}, {}, {})", "", x1, x2, y, _lvl = _lvl);
		let (a, b, c) = (x1.ub(), x2.ub(), y.ub());
		assert!(y.ub() <= a + b);

		if a.is_zero() && b.is_zero() {
			Ok(())
		} else if a.is_one() && b.is_one() {
			self.comp(db, x1, x2, y, _lvl + 1)
		} else if a.is_odd() && b.is_even() {
			self.merged(db, x2, x1, y, _lvl + 1)
		} else {
			// TODO can more easily be implemented using affine views
			let mut odd_even = |x: &IntVarOrd<DB::Lit, C>| {
				let (odd, even): (Vec<_>, Vec<_>) =
					x.xs.iter(..)
						.map(|(c, l)| (c.end - C::one(), l))
						.partition(|(c, _)| c.is_odd());
				let x1 = if odd.is_empty() {
					None
				} else {
					Some(IntVarOrd::new(
						db,
						IntervalMap::from_sorted(
							odd.into_iter()
								.map(|(c, l)| (((c + C::one()) / (C::one() + C::one())), l))
								.map(|(c, l)| (c..(c + C::one()), Some(l.clone()))),
						),
						format!("{}_odd", x.lbl),
					))
				};

				let x2 = if even.is_empty() {
					None
				} else {
					Some(IntVarOrd::new(
						db,
						IntervalMap::from_sorted(
							even.into_iter()
								.map(|(c, l)| ((c / (C::one() + C::one())), l))
								.map(|(c, l)| (c..(c + C::one()), Some(l.clone()))),
						),
						format!("{}_even", x.lbl),
					))
				};
				(x1, x2)
			};

			let mut merge = |db: &mut DB,
			                 x1: Option<IntVarOrd<_, _>>,
			                 x2: Option<IntVarOrd<_, _>>,
			                 c: C,
			                 lbl: String| match (x1, x2) {
				(None, Some(x2)) => Ok(x2),
				(Some(x1), None) => Ok(x1),
				(Some(x1), Some(x2)) => {
					let z = self.next_int_var(db, std::cmp::min(x1.ub() + x2.ub(), c), lbl);
					self.merged(db, &x1, &x2, &z, _lvl + 1)?;
					Ok(z)
				}
				(None, None) => unreachable!(),
			};

			let (x1_odd, x1_even) = odd_even(x1);
			let (x2_odd, x2_even) = odd_even(x2);

			let c_even_card_net = a <= c && b <= c && a + b > c && c.is_even();
			let c_odd_card_net = a <= c && b <= c && a + b > c && c > C::zero() && c.is_odd();

			let z_odd_ub = if c_even_card_net {
				(c / (C::one() + C::one())) + C::one()
			} else if c_odd_card_net {
				(c + C::one()) / (C::one() + C::one())
			} else {
				x1_odd.as_ref().map(|x| x.ub()).unwrap_or_default()
					+ x2_odd.as_ref().map(|x| x.ub()).unwrap_or_default()
			};

			let z_odd = merge(db, x1_odd, x2_odd, z_odd_ub, String::from("z_odd"))?;

			let z_even_ub = if c_even_card_net {
				c / (C::one() + C::one())
			} else if c_odd_card_net {
				(c - C::one()) / (C::one() + C::one())
			} else {
				x1_even.as_ref().map(|x| x.ub()).unwrap_or_default()
					+ x2_even.as_ref().map(|x| x.ub()).unwrap_or_default()
			};

			let z_even = merge(db, x1_even, x2_even, z_even_ub, String::from("z_even"))?;

			for ((z_even_i, z_odd_i), (y_even, y_odd)) in z_even
				.xs
				.values(..)
				.zip(z_odd.xs.values(..).skip(1))
				.zip(y.xs.values(..).skip(1).tuples())
			{
				self.comp_lits(db, z_even_i, z_odd_i, y_even, Some(y_odd), _lvl + 1)?;
			}

			// TODO this is a bit clunky (and at least inefficient). The first/last lits of z should view y1/yn.
			let y1 = y.xs.values(..).next().unwrap();
			let z1 = z_odd.xs.values(..).next().unwrap();
			self.equiv(db, z1, y1, _lvl + 1)?;

			if c_even_card_net {
				let yn = y.xs.values(..).last().unwrap();
				let za = z_even.xs.values(..).last().unwrap();
				let zb = z_odd.xs.values(..).last().unwrap();
				self.comp_lits(db, za, zb, yn, None, _lvl + 1)?;
			} else if c_odd_card_net {
			} else if a.is_even() && b.is_even() {
				let yn = y.xs.values(..).last().unwrap();
				let zn = z_even.xs.values(..).last().unwrap();
				self.equiv(db, yn, zn, _lvl + 1)?;
			} else if a.is_odd() && b.is_odd() {
				let yn = y.xs.values(..).last().unwrap();
				let zn = z_odd.xs.values(..).last().unwrap();
				self.equiv(db, yn, zn, _lvl + 1)?;
			}

			// TODO: Does this need tracing?
			// eprintln!(
			//	"{:_lvl$}{}",
			//	"",
			//	y.xs.values(..).map(|l| db.to_label(l)).join(", "),
			//	_lvl = _lvl
			// );
			Ok(())
		}
	}

	fn comp<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		x: &IntVarOrd<DB::Lit, C>,
		y: &IntVarOrd<DB::Lit, C>,
		z: &IntVarOrd<DB::Lit, C>,
		_lvl: usize,
	) -> Result {
		// TODO: Add tracing
		// eprintln!("{:_lvl$}comp({}, {}, {})", "", x, y, z, _lvl = _lvl);
		debug_assert!(x.ub() == C::one());
		debug_assert!(y.ub() == C::one());
		debug_assert!(z.ub() == C::one() || z.ub() == C::one() + C::one());

		let x = x.geq(C::one()..(C::one() + C::one()))[0][0].clone();
		let y = y.geq(C::one()..(C::one() + C::one()))[0][0].clone();

		let mut zs = z.xs.values(..);
		let z1 = zs.next().unwrap();
		let z2 = zs.next(); // optional
		self.comp_lits(db, &x, &y, z1, z2, _lvl + 1)
	}

	fn equiv<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
		x: &DB::Lit,
		y: &DB::Lit,
		_: usize,
	) -> Result {
		emit_clause!(db, &[x.negate(), y.clone()])?;
		emit_clause!(db, &[x.clone(), y.negate()])?;
		Ok(())
	}

	fn comp_lits<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
		x: &DB::Lit,
		y: &DB::Lit,
		z1: &DB::Lit,
		z2: Option<&DB::Lit>,
		_lvl: usize,
	) -> Result {
		// TODO: Add tracing
		// eprintln!(
		// 	"{:_lvl$}comp_lits({:?}, {:?}, {:?}, {:?})",
		//	"",
		//	x,
		//	y,
		//	z1,
		//	z2,
		//	_lvl = _lvl
		// );
		emit_clause!(db, &[x.negate(), z1.clone()])?;
		emit_clause!(db, &[y.negate(), z1.clone()])?;

		if let Some(z2) = z2 {
			emit_clause!(db, &[x.negate(), y.negate(), z2.clone()])?;
			emit_clause!(db, &[x.clone(), z2.negate()])?;
			emit_clause!(db, &[y.clone(), z2.negate()])?;
		} else {
			emit_clause!(db, &[x.negate(), y.negate()])?;
		}

		// TODO redundant if no z2
		emit_clause!(db, &[x.clone(), y.clone(), z1.negate()])?;
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::helpers::tests::{assert_sol, TestDB};

	#[test]
	fn test_small_sorted_le() {
		let mut db = TestDB::new(4);
		let con = &Sorted::new(&[1, 2], LimitComp::LessEq, &[3, 4]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_2_sorted_eq() {
		let mut db = TestDB::new(4);
		let con = &Sorted::new(&[1, 2], LimitComp::Equal, &[3, 4]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_3_sorted_eq() {
		let mut db = TestDB::new(6);
		let con = &Sorted::new(&[1, 2, 3], LimitComp::Equal, &[4, 5, 6]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_3_2_sorted_eq() {
		let mut db = TestDB::new(5);
		let con = &Sorted::new(&[1, 2, 3], LimitComp::Equal, &[4, 5]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_4_sorted_eq() {
		let mut db = TestDB::new(8);
		let con = &Sorted::new(&[1, 2, 3, 4], LimitComp::Equal, &[5, 6, 7, 8]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_4_2_sorted_eq() {
		let mut db = TestDB::new(6);
		let con = &Sorted::new(&[1, 2, 3, 4], LimitComp::Equal, &[5, 6]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_4_3_sorted_eq() {
		let mut db = TestDB::new(7);
		let con = &Sorted::new(&[1, 2, 3, 4], LimitComp::Equal, &[5, 6, 7]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_5_sorted_eq() {
		let mut db = TestDB::new(10);
		let con = &Sorted::new(&[1, 2, 3, 4, 5], LimitComp::Equal, &[6, 7, 8, 9, 10]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_5_3_sorted_eq() {
		let mut db = TestDB::new(8);
		let con = &Sorted::new(&[1, 2, 3, 4, 5], LimitComp::Equal, &[6, 7, 8]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_5_6_sorted_eq() {
		let mut db = TestDB::new(11);
		let con = &Sorted::new(&[1, 2, 3, 4, 5, 6], LimitComp::Equal, &[7, 8, 9, 10, 11]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}

	#[test]
	fn test_6_7_sorted_eq() {
		let mut db = TestDB::new(13);
		let con = &Sorted::new(
			&[1, 2, 3, 4, 5, 6, 7],
			LimitComp::Equal,
			&[8, 9, 10, 11, 12, 13],
		);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => SortedEncoder::default(), &con => sols);
	}
}
