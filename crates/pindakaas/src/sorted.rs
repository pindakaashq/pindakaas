use crate::{
	int::{
		add_clauses_for, equivalent, negate_cnf, IntVarEnc, IntVarOrd, TernLeConstraint,
		TernLeEncoder,
	},
	linear::LimitComp,
	trace::emit_clause,
	CheckError, Checker, ClauseDatabase, Coefficient, Encoder, LinExp, Literal, Result,
	Unsatisfiable,
};
use iset::{interval_map, IntervalMap};
use itertools::Itertools;

pub struct SortedEncoder {
	add_consistency: bool,
	strategy: SortedStrategy,
}

#[derive(Debug, PartialEq)]
pub enum SortedStrategy {
	Direct,
	Recursive,
	Mixed(f32),
}

impl Default for SortedEncoder {
	fn default() -> Self {
		Self {
			strategy: SortedStrategy::Mixed(10f32),
			add_consistency: false,
		}
	}
}

impl SortedEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn set_strategy(&mut self, strategy: SortedStrategy) -> &mut Self {
		self.strategy = strategy;
		self
	}
}

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

		let rhs_eq = LinExp::new()
			.add_chain(
				self.ys
					.iter()
					.map(|y| (y.clone(), 1))
					.collect::<Vec<_>>()
					.as_slice(),
			)
			.assign(solution)? as usize;

		if (self.cmp == LimitComp::LessEq && lhs <= rhs_eq)
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
		let n = sorted.xs.len();
		let xs = sorted
			.xs
			.iter()
			.map(|x| Some(x.clone()))
			.enumerate()
			.map(|(i, x)| {
				IntVarOrd::new(db, interval_map! { 1..2_i32 => x }, format!("x_{}", i + 1))
			})
			.collect::<Vec<_>>();

		let y = IntVarOrd::new(
			db,
			IntervalMap::from_sorted(
				num::iter::range_inclusive(1, n as i32 + 1)
					.zip(sorted.ys.iter())
					.map(|(i, y)| (i..(i + 1), Some(y.clone()))),
			),
			"s_x".to_string(),
		);

		if self.add_consistency {
			y.consistent(db).unwrap();
		}

		// TODO
		if sorted.cmp == LimitComp::Equal && self.strategy != SortedStrategy::Recursive {
			unimplemented!("Cannot use {:?} to encode {:?}, since the Recursive strategy will encode complete equality (and the Direct strategy will encode complete LessEq). So the Mixed strategy of the two encodes incomplete LessEq, as in, some solutions will be missing.", self.strategy, sorted.cmp);
		}
		self.sorted(db, &xs, &sorted.cmp, &y, 0)
	}
}

impl<'a, DB: ClauseDatabase, C: Coefficient> Encoder<DB, TernLeConstraint<'a, DB::Lit, C>>
	for SortedEncoder
{
	fn encode(&mut self, db: &mut DB, tern: &TernLeConstraint<DB::Lit, C>) -> Result {
		let TernLeConstraint { x, y, cmp, z } = tern;
		if tern.is_fixed()? {
			Ok(())
		} else if let (IntVarEnc::Ord(x), IntVarEnc::Ord(y), IntVarEnc::Ord(z)) = (x, y, z) {
			self.merged(db, x, y, cmp, z, 0)
		} else {
			TernLeEncoder::default().encode(db, tern)
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
		// TODO We always have the view x>=1 <-> y>=1, which is now realized using equiv
		let y = IntVarOrd::new(
			db,
			IntervalMap::from_sorted(
				num::iter::range_inclusive(C::one(), ub).map(|i| (i..(i + C::one()), None)),
			),
			lbl,
		);
		if self.add_consistency {
			y.consistent(db).unwrap();
		}
		y
	}

	fn lambda(v: u128, c: u128, lambda: f32) -> u128 {
		((v as f32) * lambda) as u128 + c
	}

	fn sorted<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		xs: &[IntVarOrd<DB::Lit, C>],
		cmp: &LimitComp,
		y: &IntVarOrd<DB::Lit, C>,
		_lvl: usize,
	) -> Result {
		let (n, m) = (xs.len(), y.ub());
		let direct = self.use_direct_sort(n as u128, m.to_u128().unwrap());

		// TODO: Add tracing
		// eprintln!(
		//	"{:_lvl$}sorted([{}], {}, {})",
		//	"",
		//	xs.iter().join(", "),
		//	y,
		//	direct,
		//	_lvl = _lvl
		// );

		debug_assert!(xs.iter().all(|x| x.ub() == C::one()));
		if direct {
			return num::range_inclusive(C::one(), m + C::one()).try_for_each(|k| {
				xs.iter()
					.map(|x| x.geq(C::one()..(C::one() + C::one()))[0][0].clone())
					.combinations(k.to_usize().unwrap())
					.try_for_each(|lits| {
						let cl = lits
							.into_iter()
							.map(|lit| lit.negate())
							.chain(y.geq(k..(k + C::one()))[0].iter().cloned())
							.collect::<Vec<_>>();
						emit_clause!(db, cl.as_slice())
					})
			});
		}
		match xs {
			[] => Ok(()),
			[x] => {
				x.xs.values(..)
					.zip(y.xs.values(..))
					.try_for_each(|(x, y)| equivalent(db, x, y))?;
				x.xs.values((y.ub() + C::one())..)
					.try_for_each(|x| emit_clause!(db, &[x.negate()]))
			}
			xs => {
				let n = n / 2;
				let y1 = self.next_int_var(
					db,
					std::cmp::min((0..n).fold(C::zero(), |a, _| a + C::one()), y.ub()),
					String::from("y_1"),
				);
				let y2 = self.next_int_var(
					db,
					std::cmp::min((n..xs.len()).fold(C::zero(), |a, _| a + C::one()), y.ub()),
					String::from("y_2"),
				);

				self.sorted(db, &xs[..n], cmp, &y1, _lvl)?;
				self.sorted(db, &xs[n..], cmp, &y2, _lvl)?;
				self.merged(db, &y1, &y2, cmp, y, _lvl + 1)
			}
		}
	}

	fn use_direct_sort(&self, n: u128, m: u128) -> bool {
		match self.strategy {
			SortedStrategy::Direct => true,
			SortedStrategy::Recursive => false,
			SortedStrategy::Mixed(lambda) => {
				let ((vr, cr), (vd, cd)) = (
					Self::sorted_cost(n, m, false),
					Self::sorted_cost(n, m, true),
				);
				Self::lambda(vd, cd, lambda) < Self::lambda(vr, cr, lambda)
			}
		}
	}

	fn sorted_cost(n: u128, m: u128, direct: bool) -> (u128, u128) {
		if direct {
			(
				m,
				(0..m)
					.map(|k| (n - k + 1..=n).product::<u128>())
					.sum::<u128>(),
			)
		} else {
			match n {
				0 => (0, 0),
				1 => (0, 0),
				2 => (2, 3),
				3 => (2, 3),
				_ => {
					let l = (n as f32 / 2.0) as u128;
					let (v1, c1) = Self::sorted_cost(l, m, direct);
					let (v2, c2) = Self::sorted_cost(n - l, m, direct);
					let (v3, c3) =
						Self::merged_cost(std::cmp::min(l, m), std::cmp::min(n - l, m), m, direct);
					(v1 + v2 + v3, c1 + c2 + c3)
				}
			}
		}
	}

	fn use_direct_merge(&self, a: u128, b: u128, c: u128) -> bool {
		match self.strategy {
			SortedStrategy::Direct => true,
			SortedStrategy::Recursive => false,
			SortedStrategy::Mixed(lambda) => {
				let ((vr, cr), (vd, cd)) = (
					Self::merged_cost(a, b, c, false),
					Self::merged_cost(a, b, c, true),
				);
				Self::lambda(vd, cd, lambda) < Self::lambda(vr, cr, lambda)
			}
		}
	}

	fn merged_cost(a: u128, b: u128, c: u128, direct: bool) -> (u128, u128) {
		if a > b {
			Self::merged_cost(b, a, c, direct)
		} else if direct {
			(
				c,
				(a + b) * c
					- (((c * (c - 1)) as f32) / 2.0) as u128
					- (((b * (b - 1)) as f32) / 2.0) as u128
					- (((a * (c - 1)) as f32) / 2.0) as u128,
			)
		} else {
			match (a, b) {
				(0, 0) => (0, 0),
				(1, 0) => (0, 0),
				(0, 1) => (0, 0),
				(1, 1) => (2, 3),
				_ => {
					use num::Integer;
					let c3 = if c.is_odd() {
						(3 * c - 3) as f32 / 2.0
					} else {
						((3 * c - 2) as f32 / 2.0) + 2.0
					} as u128;
					let v3 = c - 1;
					let (a, b, c) = (a as f32 / 2.0, b as f32 / 2.0, c as f32 / 2.0);
					let ((v1, c1), (v2, c2)) = (
						Self::merged_cost(
							a.ceil() as u128,
							b.ceil() as u128,
							c.floor() as u128 + 1,
							false,
						),
						Self::merged_cost(
							a.floor() as u128,
							b.floor() as u128,
							c.floor() as u128,
							false,
						),
					);
					(v1 + v2 + v3, c1 + c2 + c3)
				}
			}
		}
	}

	fn merged<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		x1: &IntVarOrd<DB::Lit, C>,
		x2: &IntVarOrd<DB::Lit, C>,
		cmp: &LimitComp,
		y: &IntVarOrd<DB::Lit, C>,
		_lvl: usize,
	) -> Result {
		let (a, b, c) = (x1.ub(), x2.ub(), y.ub());
		let direct = self.use_direct_merge(
			a.to_u128().unwrap(),
			b.to_u128().unwrap(),
			c.to_u128().unwrap(),
		);

		// TODO: Add tracing
		// eprintln!(
		//	"{:_lvl$}merged({}, {}, {}, {})",
		//	"",
		//	x1,
		//	x2,
		//	y,
		//	direct,
		//	_lvl = _lvl
		// );

		if direct {
			return TernLeEncoder::default().encode(
				db,
				&TernLeConstraint {
					x: &x1.clone().into(),
					y: &x2.clone().into(),
					cmp: LimitComp::LessEq,
					z: &y.clone().into(), // TODO no consistency implemented for this bound yet
				},
			);
		}

		if a.is_zero() && b.is_zero() {
			Ok(())
		} else if a.is_one() && b.is_one() && c <= C::one() + C::one() {
			let x2 = x2.add(db, &IntVarEnc::Const(C::one()))?;
			let y = y.add(db, &IntVarEnc::Const(C::one()))?;
			self.comp(db, &x1.clone().into(), &x2, cmp, &y, C::one())
		} else {
			let two = C::one() + C::one();
			let x1_floor = x1.div(&two);
			let x1_ceil = x1.add(db, &IntVarEnc::Const(C::one()))?.div(&two);

			let x2_floor = x2.div(&two);
			let x2_ceil = x2.add(db, &IntVarEnc::Const(C::one()))?.div(&two);

			let z_floor = x1_floor.add(db, &x2_floor)?;
			self.encode(
				db,
				&TernLeConstraint::new(&x1_floor, &x2_floor, cmp.clone(), &z_floor),
			)?;

			let z_ceil = x1_ceil.add(db, &x2_ceil)?;
			self.encode(
				db,
				&TernLeConstraint::new(&x1_ceil, &x2_ceil, cmp.clone(), &z_ceil),
			)?;

			for c in num::iter::range_inclusive(C::zero(), c) {
				self.comp(db, &z_floor, &z_ceil, cmp, &y.clone().into(), c)?;
			}

			Ok(())
		}
	}

	fn comp<DB: ClauseDatabase, C: Coefficient>(
		&mut self,
		db: &mut DB,
		x: &IntVarEnc<DB::Lit, C>,
		y: &IntVarEnc<DB::Lit, C>,
		_: &LimitComp,
		z: &IntVarEnc<DB::Lit, C>,
		c: C,
	) -> Result {
		let to_iv = |c: C| c..(c + C::one());
		let empty_clause: Vec<Vec<DB::Lit>> = vec![Vec::new()];
		let c1 = c;
		let c2 = c + C::one();
		let x = x.geq(to_iv(c1)); // c
		let y = y.geq(to_iv(c2)); // c+1
		let z1 = z.geq(to_iv(c1 + c1)); // 2c
		let z2 = z.geq(to_iv(c1 + c2)); // 2c+1

		add_clauses_for(db, negate_cnf(x.clone()), empty_clause.clone(), z1.clone())?;
		add_clauses_for(db, negate_cnf(y.clone()), empty_clause.clone(), z1.clone())?;
		add_clauses_for(db, negate_cnf(x.clone()), negate_cnf(y.clone()), z2.clone())?;

		add_clauses_for(db, x.clone(), empty_clause.clone(), negate_cnf(z2.clone()))?;
		add_clauses_for(db, y.clone(), empty_clause, negate_cnf(z2))?;
		add_clauses_for(db, x, y, negate_cnf(z1))?;
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::helpers::tests::{assert_sol, TestDB};
	use iset::interval_map;

	#[test]
	fn test_2_merged_eq() {
		let mut db = TestDB::new(0);
		let x: IntVarEnc<_, _> =
			IntVarOrd::new(&mut db, interval_map!( 1..2 => None ), "x".to_string()).into();
		let y: IntVarEnc<_, _> =
			IntVarOrd::new(&mut db, interval_map!( 1..2 => None ), "y".to_string()).into();
		let z: IntVarEnc<_, _> = IntVarOrd::new(
			&mut db,
			interval_map!( 1..2 => None, 2..3 => None ),
			"z".to_string(),
		)
		.into();
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;
		let con = TernLeConstraint::<i32, i32>::new(&x, &y, LimitComp::Equal, &z);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		assert_sol!(db => enc, &con => sols);
	}

	#[test]
	fn test_2_sorted_eq() {
		let mut db = TestDB::new(4);
		let con = &Sorted::new(&[1, 2], LimitComp::Equal, &[3, 4]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_3_sorted_eq() {
		let mut db = TestDB::new(6);
		let con = &Sorted::new(&[1, 2, 3], LimitComp::Equal, &[4, 5, 6]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_3_2_sorted_eq() {
		let mut db = TestDB::new(5);
		let con = &Sorted::new(&[1, 2, 3], LimitComp::Equal, &[4, 5]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_4_sorted_eq() {
		let mut db = TestDB::new(8);
		let con = &Sorted::new(&[1, 2, 3, 4], LimitComp::Equal, &[5, 6, 7, 8]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_4_2_sorted_eq() {
		let mut db = TestDB::new(6);
		let con = &Sorted::new(&[1, 2, 3, 4], LimitComp::Equal, &[5, 6]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_4_3_sorted_eq() {
		let mut db = TestDB::new(7);
		let con = &Sorted::new(&[1, 2, 3, 4], LimitComp::Equal, &[5, 6, 7]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	// TODO splr bug
	// #[test]
	// fn test_5_sorted_eq() {
	// 	let mut db = TestDB::new(10);
	// 	let con = &Sorted::new(&[1, 2, 3, 4, 5], LimitComp::Equal, &[6, 7, 8, 9, 10]);
	// 	let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
	// 	let mut enc = SortedEncoder::default();
	// 	enc.set_strategy(SortedStrategy::Recursive);
	// 	assert_sol!(db => enc, &con => sols);
	// }

	#[test]
	fn test_5_3_sorted_eq() {
		let mut db = TestDB::new(8);
		let con = &Sorted::new(&[1, 2, 3, 4, 5], LimitComp::Equal, &[6, 7, 8]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_5_6_sorted_eq() {
		let mut db = TestDB::new(11);
		let con = &Sorted::new(&[1, 2, 3, 4, 5, 6], LimitComp::Equal, &[7, 8, 9, 10, 11]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
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
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_5_1_sorted_eq_negated() {
		let mut db = TestDB::new(6);
		let con = &Sorted::new(&[-1, -2, -3, -4, -5], LimitComp::LessEq, &[6]);
		let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = SortedEncoder::default();
		enc.set_strategy(SortedStrategy::Direct);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_sorted_cost_test() {
		let (n, m) = (50, 16);
		SortedEncoder::sorted_cost(n, m, true); // should not lead to overflow
	}
}
