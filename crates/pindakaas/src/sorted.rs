#![allow(unused_variables, dead_code)]

use cached::proc_macro::cached;

use crate::{
	int::enc::IntVarEnc, linear::LimitComp, CheckError, Checker, ClauseDatabase, Coeff, Encoder,
	Linear, Lit, Result, Valuation,
};

#[derive(Clone)]
pub struct SortedEncoder {
	pub(crate) add_consistency: bool,
	pub(crate) strategy: SortedStrategy,
	pub(crate) overwrite_direct_cmp: Option<LimitComp>,
	pub(crate) overwrite_recursive_cmp: Option<LimitComp>,
	pub(crate) sort_n: SortN,
}
#[allow(dead_code)]
#[derive(Clone)]
pub enum SortN {
	One,
	#[allow(dead_code)] // TODO
	DivTwo,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum SortedStrategy {
	Direct,
	Recursive,
	Mixed(u32),
}

impl Default for SortedEncoder {
	fn default() -> Self {
		Self {
			strategy: SortedStrategy::Mixed(10),
			add_consistency: false,
			overwrite_direct_cmp: Some(LimitComp::LessEq),
			overwrite_recursive_cmp: Some(LimitComp::Equal),
			sort_n: SortN::DivTwo,
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

pub struct Sorted<'a> {
	pub(crate) xs: &'a [Lit],
	pub(crate) cmp: LimitComp,
	pub(crate) y: &'a IntVarEnc,
}

impl<'a> Sorted<'a> {
	pub(crate) fn new(xs: &'a [Lit], cmp: LimitComp, y: &'a IntVarEnc) -> Self {
		Self { xs, cmp, y }
	}
}

impl<'a> Checker for Sorted<'a> {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<(), CheckError> {
		todo!();
		// let lhs = LinExp::from_terms(self.xs.iter().map(|x| (*x, 1)).collect_vec().as_slice())
		// 	.value(sol)?;
		// let rhs = LinExp::from(self.y).value(sol)?;

		// if match self.cmp {
		// 	LimitComp::LessEq => lhs <= rhs,
		// 	LimitComp::Equal => lhs == rhs,
		// } {
		// 	Ok(())
		// } else {
		// 	Err(CheckError::Unsatisfiable(Unsatisfiable))
		// }
	}
}

// impl<DB: ClauseDatabase> Encoder<DB, Sorted<'_>> for SortedEncoder {
// 	fn encode(&self, db: &mut DB, sorted: &Sorted) -> Result {
// 		let xs = sorted
// 			.xs
// 			.iter()
// 			.map(|x| Some(*x))
// 			.enumerate()
// 			.map(|(i, x)| {
// 				// OrdEnc::from_lits(&[x])
// 				todo!();
// 				// IntVarOrd::from_views(
// 				// 	db,
// 				// 	interval_map! { C::one()..(C::one()+C::one()) => x },
// 				// 	format!("x_{}", i + 1),
// 				// )
// 				// .into()
// 			})
// 			.collect_vec();

// 		// if self.add_consistency {
// 		// 	sorted.y.consistent(db, Dom::from_slice(&[0,1])).unwrap();
// 		// }

// 		self.sorted(db, &xs, &sorted.cmp, sorted.y, 0)
// 	}
// }

impl<DB: ClauseDatabase> Encoder<DB, Linear> for SortedEncoder {
	fn encode(&self, db: &mut DB, tern: &Linear) -> Result {
		todo!();
		/*
		let TernLeConstraint { x, y, cmp, z } = tern;
		if tern.is_fixed()? {
			Ok(())
		} else if matches!(x, IntVarEnc::Ord(_))
			&& matches!(y, IntVarEnc::Ord(_))
			&& matches!(z, IntVarEnc::Ord(_))
		{
			self.merged(db, x, y, &(**cmp).try_into().unwrap(), z, 0)
		} else {
			TernLeEncoder::default().encode(db, tern)
		}
		*/
	}
}

impl SortedEncoder {
	fn next_int_var<DB: ClauseDatabase>(&self, db: &mut DB, ub: Coeff, lbl: String) -> IntVarEnc {
		todo!();
		/*
		// TODO We always have the view x>=1 <-> y>=1, which is now realized using equiv
		if ub == 0 {
			IntVarEnc::Const(0)
		} else {
			let y = IntVarOrd::from_bounds(db, 0, ub, lbl);
			if self.add_consistency {
				y.consistent(db).unwrap();
			}
			todo!();
			// y.into()
		}
		*/
	}

	/// The sorted/merged base case of x1{0,1}+x2{0,1}<=y{0,1,2}
	fn smerge<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		x1: &IntVarEnc,
		x2: &IntVarEnc,
		cmp: &LimitComp,
		y: &IntVarEnc,
	) -> Result {
		todo!();
		/*
		// we let x2 take the place of z_ceil, so we need to add 1 to both sides
		let x2 = x2.add(
			db,
			&TernLeEncoder::default(),
			&IntVarEnc::Const(1),
			None,
			None,
		)?;
		let y = y.add(
			db,
			&TernLeEncoder::default(),
			&IntVarEnc::Const(1),
			None,
			None,
		)?;
		self.comp(db, x1, &x2, cmp, &y, 1)
		*/
	}

	fn sorted<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		xs: &[IntVarEnc],
		cmp: &LimitComp,
		y: &IntVarEnc,
		_lvl: usize,
	) -> Result {
		todo!();
		/*
			let (n, m) = (xs.len(), y.ub());
			let direct = false;

			// TODO: Add tracing
			// eprintln!(
			// 	"{:_lvl$}sorted([{}] {} {}, {})",
			// 	"",
			// 	xs.iter().join(", "),
			// 	cmp,
			// 	y,
			// 	direct,
			// 	_lvl = _lvl
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
				[x] => TernLeEncoder::default().encode(
					db,
					&TernLeConstraint {
						x,
						y: &IntVarEnc::Const(C::zero()),
						cmp: &(cmp.clone()).into(),
						z: y,
					},
				),
				[x1, x2] if m <= C::one() + C::one() => self.smerge(db, x1, x2, cmp, y),
				xs => {
					let n = match self.sort_n {
						SortN::One => 1,
						SortN::DivTwo => n / 2,
					};
					let y1 = self.sort(
						db,
						&xs[..n],
						cmp,
						std::cmp::min((0..n).fold(C::zero(), |a, _| a + C::one()), y.ub()),
						String::from("y1"),
						_lvl,
					);
					let y2 = self.sort(
						db,
						&xs[n..],
						cmp,
						std::cmp::min((n..xs.len()).fold(C::zero(), |a, _| a + C::one()), y.ub()),
						String::from("y2"),
						_lvl,
					);

					if let Some(y1) = y1 {
						if let Some(y2) = y2 {
							self.merged(db, &y1, &y2, cmp, y, _lvl + 1)
						} else {
							Ok(())
						}
					} else {
						Ok(())
					}
				}
			}
		*/
	}

	fn sort<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		xs: &[IntVarEnc],
		cmp: &LimitComp,
		ub: Coeff,
		lbl: String,
		_lvl: usize,
	) -> Option<IntVarEnc> {
		match xs {
			[] => None,
			[x] => Some(x.clone()),
			xs => {
				let y = self.next_int_var(db, ub, lbl);
				self.sorted(db, xs, cmp, &y, _lvl).unwrap();
				Some(y)
			}
		}
	}

	fn merged<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		x1: &IntVarEnc,
		x2: &IntVarEnc,
		cmp: &LimitComp,
		y: &IntVarEnc,
		_lvl: usize,
	) -> Result {
		todo!();
		/*
			let (a, b, c) = (x1.ub(), x2.ub(), y.ub());
			let (strat, _cost) = merged_cost(
				a.to_u128().unwrap(),
				b.to_u128().unwrap(),
				c.to_u128().unwrap(),
				self.strategy.clone(),
			);

			match strat {
				SortedStrategy::Direct => {
					let cmp = self.overwrite_direct_cmp.as_ref().unwrap_or(cmp).clone();
					TernLeEncoder::default().encode(
						db,
						&TernLeConstraint {
							x: x1,
							y: x2,
							cmp: &(cmp).into(),
							z: y, // TODO no consistency implemented for this bound yet
						},
					)
				}
				SortedStrategy::Recursive => {
					if a.is_zero() && b.is_zero() {
						Ok(())
					} else if a.is_one() && b.is_one() && c <= 2 {
						self.smerge(db, x1, x2, cmp, y)
					} else {
						let x1_floor = x1.div(&2);
						let x1_ceil = x1
							.add(
								db,
								&mut TernLeEncoder::default(),
								&IntVarEnc::Const(1),
								None,
								None,
							)?
							.div(&2);

						let x2_floor = x2.div(&2);
						let x2_ceil = x2
							.add(
								db,
								&mut TernLeEncoder::default(),
								&IntVarEnc::Const(1),
								None,
								None,
							)?
							.div(&2);

						let z_floor =
							x1_floor.add(db, &mut TernLeEncoder::default(), &x2_floor, None, None)?;
						self.encode(
							db,
							&TernLeConstraint::new(
								&x1_floor,
								&x2_floor,
								&(cmp.clone()).into(),
								&z_floor,
							),
						)?;

						let z_ceil =
							x1_ceil.add(db, &mut TernLeEncoder::default(), &x2_ceil, None, None)?;
						self.encode(
							db,
							&TernLeConstraint::new(&x1_ceil, &x2_ceil, &(cmp.clone()).into(), &z_ceil),
						)?;

						for c in num::iter::range_inclusive(C::zero(), c) {
							self.comp(db, &z_floor, &z_ceil, cmp, y, c)?;
						}

						Ok(())
					}
				}
				_ => unreachable!(),
			}
		*/
	}

	fn comp<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		x: &IntVarEnc,
		y: &IntVarEnc,
		cmp: &LimitComp,
		z: &IntVarEnc,
		c: Coeff,
	) -> Result {
		todo!();
		/*
		let cmp = self.overwrite_recursive_cmp.as_ref().unwrap_or(cmp);
		let to_iv = |c: Coeff| c..(c + 1);
		let empty_clause: Vec<Vec<Lit>> = vec![Vec::new()];
		let c1 = c;
		let c2 = c + 1;
		let x = x.geq(to_iv(c1)); // c
		let y = y.geq(to_iv(c2)); // c+1
		let z1 = z.geq(to_iv(c1 + c1)); // 2c
		let z2 = z.geq(to_iv(c1 + c2)); // 2c+1

		add_clauses_for(
			db,
			vec![negate_cnf(x.clone()), empty_clause.clone(), z1.clone()],
		)?;
		add_clauses_for(
			db,
			vec![negate_cnf(y.clone()), empty_clause.clone(), z1.clone()],
		)?;
		add_clauses_for(
			db,
			vec![negate_cnf(x.clone()), negate_cnf(y.clone()), z2.clone()],
		)?;

		if cmp == &LimitComp::Equal {
			add_clauses_for(
				db,
				vec![x.clone(), empty_clause.clone(), negate_cnf(z2.clone())],
			)?;
			add_clauses_for(db, vec![y.clone(), empty_clause, negate_cnf(z2)])?;
			add_clauses_for(db, vec![x, y, negate_cnf(z1)])?;
		}
		Ok(())
		*/
	}
}

fn merged_dir_cost(a: u128, b: u128, c: u128) -> (u128, u128) {
	if a <= c && b <= c && a + b > c {
		(
			c,
			(a + b) * c - ((c * (c - 1)) / 2) - ((a * (a - 1)) / 2) - ((b * (b - 1)) / 2),
		)
	} else {
		(a + b, a * b + a + b)
	}
}

fn merged_rec_cost(a: u128, b: u128, c: u128, strat: SortedStrategy) -> (u128, u128) {
	let div_ceil = |a: u128, b: u128| {
		a.checked_add(b)
			.unwrap()
			.checked_sub(1)
			.unwrap()
			.checked_div(b)
			.unwrap()
	};

	match (a, b, c) {
		(0, 0, _) => (0, 0),
		(1, 0, _) => unreachable!(),
		(0, 1, _) => (0, 0),
		(1, 1, 1) => (1, 2),
		(1, 1, 2) => (2, 3),
		(a, b, c) => {
			let ((_, (v1, c1)), (_, (v2, c2)), (v3, c3)) = (
				merged_cost(div_ceil(a, 2), div_ceil(b, 2), c / 2 + 1, strat.clone()),
				merged_cost(a / 2, b / 2, c / 2, strat),
				(
					c - 1,
					if c % 2 == 1 {
						(3 * c - 3) / 2
					} else {
						((3 * c - 2) / 2) + 2
					},
				),
			);
			(v1 + v2 + v3, c1 + c2 + c3)
		}
	}
}

fn merged_mix_cost(
	dir_cost: (u128, u128),
	rec_cost: (u128, u128),
	l: u32,
) -> (SortedStrategy, (u128, u128)) {
	if lambda(dir_cost, l) < lambda(rec_cost, l) {
		(SortedStrategy::Direct, dir_cost)
	} else {
		(SortedStrategy::Recursive, rec_cost)
	}
}

#[cached]
fn merged_cost(a: u128, b: u128, c: u128, strat: SortedStrategy) -> (SortedStrategy, (u128, u128)) {
	if a > b {
		merged_cost(b, a, c, strat)
	} else {
		match strat {
			SortedStrategy::Direct => (SortedStrategy::Direct, merged_dir_cost(a, b, c)),
			SortedStrategy::Recursive => {
				(SortedStrategy::Recursive, merged_rec_cost(a, b, c, strat))
			}
			SortedStrategy::Mixed(lambda) => merged_mix_cost(
				merged_dir_cost(a, b, c),
				merged_rec_cost(a, b, c, strat),
				lambda,
			),
		}
	}
}

// TODO safely use floating point for lambda
fn lambda((v, c): (u128, u128), lambda: u32) -> u128 {
	(v * lambda as u128) + c
}

/*
#[cfg(test)]
mod tests {
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		helpers::tests::{assert_sol, TestDB},
		Comparator,
	};

	fn get_sorted_encoder(strategy: SortedStrategy) -> SortedEncoder {
		SortedEncoder {
			strategy,
			overwrite_direct_cmp: None,
			overwrite_recursive_cmp: None,
			..SortedEncoder::default()
		}
	}

	#[test]
	fn test_2_merged_eq() {
		let mut db = TestDB::new(0);
		let x: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 1, String::from("x")).into();
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 1, String::from("y")).into();
		let z: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 2, String::from("z")).into();
		db.num_var = (x.lits() + y.lits() + z.lits()) as i32;
		let con = TernLeConstraint::new(&x, &y, &Comparator::Equal, &z);
		let mut enc = get_sorted_encoder(SortedStrategy::Recursive);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let sols = vec![
			lits![-1, -2, -3, -4],
			lits![1, -2, 3, -4],
			lits![-1, 2, 3, -4],
			lits![1, 2, 3, 4],
		];
		assert_sol!(db => enc, &con => sols);
	}

	#[test]
	fn test_2_sorted_eq() {
		let mut db = TestDB::new(4);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 2, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![1, 2];
		let con = &Sorted::new(&lits, LimitComp::Equal, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let sols = vec![
			lits![-1, -2, -3, -4, -5, -6],
			lits![-1, -2, 3, -4, -5, -6],
			lits![-1, -2, -3, 4, -5, -6],
			lits![-1, -2, 3, 4, -5, -6],
			lits![1, -2, -3, -4, 5, -6],
			lits![-1, 2, -3, -4, 5, -6],
			lits![1, -2, 3, -4, 5, -6],
			lits![-1, 2, 3, -4, 5, -6],
			lits![1, -2, -3, 4, 5, -6],
			lits![-1, 2, -3, 4, 5, -6],
			lits![1, -2, 3, 4, 5, -6],
			lits![-1, 2, 3, 4, 5, -6],
			lits![1, 2, -3, -4, 5, 6],
			lits![1, 2, 3, -4, 5, 6],
			lits![1, 2, -3, 4, 5, 6],
			lits![1, 2, 3, 4, 5, 6],
		];
		let enc = get_sorted_encoder(SortedStrategy::Recursive);
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_3_sorted_eq() {
		let mut db = TestDB::new(6);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 3, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![1, 2, 3];
		let con = &Sorted::new(&lits, LimitComp::Equal, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let sols = vec![
			lits![-1, -2, -3, -4, -5, -6, -7, -8, -9],
			lits![-1, -2, -3, 4, -5, -6, -7, -8, -9],
			lits![-1, -2, -3, -4, 5, -6, -7, -8, -9],
			lits![-1, -2, -3, 4, 5, -6, -7, -8, -9],
			lits![-1, -2, -3, -4, -5, 6, -7, -8, -9],
			lits![-1, -2, -3, 4, -5, 6, -7, -8, -9],
			lits![-1, -2, -3, -4, 5, 6, -7, -8, -9],
			lits![-1, -2, -3, 4, 5, 6, -7, -8, -9],
			lits![1, -2, -3, -4, -5, -6, 7, -8, -9],
			lits![-1, 2, -3, -4, -5, -6, 7, -8, -9],
			lits![-1, -2, 3, -4, -5, -6, 7, -8, -9],
			lits![1, -2, -3, 4, -5, -6, 7, -8, -9],
			lits![-1, 2, -3, 4, -5, -6, 7, -8, -9],
			lits![-1, -2, 3, 4, -5, -6, 7, -8, -9],
			lits![1, -2, -3, -4, 5, -6, 7, -8, -9],
			lits![-1, 2, -3, -4, 5, -6, 7, -8, -9],
			lits![-1, -2, 3, -4, 5, -6, 7, -8, -9],
			lits![1, -2, -3, 4, 5, -6, 7, -8, -9],
			lits![-1, 2, -3, 4, 5, -6, 7, -8, -9],
			lits![-1, -2, 3, 4, 5, -6, 7, -8, -9],
			lits![1, -2, -3, -4, -5, 6, 7, -8, -9],
			lits![-1, 2, -3, -4, -5, 6, 7, -8, -9],
			lits![-1, -2, 3, -4, -5, 6, 7, -8, -9],
			lits![1, -2, -3, 4, -5, 6, 7, -8, -9],
			lits![-1, 2, -3, 4, -5, 6, 7, -8, -9],
			lits![-1, -2, 3, 4, -5, 6, 7, -8, -9],
			lits![1, -2, -3, -4, 5, 6, 7, -8, -9],
			lits![-1, 2, -3, -4, 5, 6, 7, -8, -9],
			lits![-1, -2, 3, -4, 5, 6, 7, -8, -9],
			lits![1, -2, -3, 4, 5, 6, 7, -8, -9],
			lits![-1, 2, -3, 4, 5, 6, 7, -8, -9],
			lits![-1, -2, 3, 4, 5, 6, 7, -8, -9],
			lits![1, 2, -3, -4, -5, -6, 7, 8, -9],
			lits![1, -2, 3, -4, -5, -6, 7, 8, -9],
			lits![-1, 2, 3, -4, -5, -6, 7, 8, -9],
			lits![1, 2, -3, 4, -5, -6, 7, 8, -9],
			lits![1, -2, 3, 4, -5, -6, 7, 8, -9],
			lits![-1, 2, 3, 4, -5, -6, 7, 8, -9],
			lits![1, 2, -3, -4, 5, -6, 7, 8, -9],
			lits![1, -2, 3, -4, 5, -6, 7, 8, -9],
			lits![-1, 2, 3, -4, 5, -6, 7, 8, -9],
			lits![1, 2, -3, 4, 5, -6, 7, 8, -9],
			lits![1, -2, 3, 4, 5, -6, 7, 8, -9],
			lits![-1, 2, 3, 4, 5, -6, 7, 8, -9],
			lits![1, 2, -3, -4, -5, 6, 7, 8, -9],
			lits![1, -2, 3, -4, -5, 6, 7, 8, -9],
			lits![-1, 2, 3, -4, -5, 6, 7, 8, -9],
			lits![1, 2, -3, 4, -5, 6, 7, 8, -9],
			lits![1, -2, 3, 4, -5, 6, 7, 8, -9],
			lits![-1, 2, 3, 4, -5, 6, 7, 8, -9],
			lits![1, 2, -3, -4, 5, 6, 7, 8, -9],
			lits![1, -2, 3, -4, 5, 6, 7, 8, -9],
			lits![-1, 2, 3, -4, 5, 6, 7, 8, -9],
			lits![1, 2, -3, 4, 5, 6, 7, 8, -9],
			lits![1, -2, 3, 4, 5, 6, 7, 8, -9],
			lits![-1, 2, 3, 4, 5, 6, 7, 8, -9],
			lits![1, 2, 3, -4, -5, -6, 7, 8, 9],
			lits![1, 2, 3, 4, -5, -6, 7, 8, 9],
			lits![1, 2, 3, -4, 5, -6, 7, 8, 9],
			lits![1, 2, 3, 4, 5, -6, 7, 8, 9],
			lits![1, 2, 3, -4, -5, 6, 7, 8, 9],
			lits![1, 2, 3, 4, -5, 6, 7, 8, 9],
			lits![1, 2, 3, -4, 5, 6, 7, 8, 9],
			lits![1, 2, 3, 4, 5, 6, 7, 8, 9],
		];
		let enc = get_sorted_encoder(SortedStrategy::Recursive);
		// println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_3_2_sorted_eq() {
		let mut db = TestDB::new(5);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 2, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![1, 2, 3];
		let con = &Sorted::new(&lits, LimitComp::Equal, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);

		let sols = vec![
			lits![-1, -2, -3, -4, -5, -6, -7],
			lits![-1, -2, -3, 4, -5, -6, -7],
			lits![-1, -2, -3, -4, 5, -6, -7],
			lits![-1, -2, -3, 4, 5, -6, -7],
			lits![1, -2, -3, -4, -5, 6, -7],
			lits![-1, 2, -3, -4, -5, 6, -7],
			lits![-1, -2, 3, -4, -5, 6, -7],
			lits![1, -2, -3, 4, -5, 6, -7],
			lits![-1, 2, -3, 4, -5, 6, -7],
			lits![-1, -2, 3, 4, -5, 6, -7],
			lits![1, -2, -3, -4, 5, 6, -7],
			lits![-1, 2, -3, -4, 5, 6, -7],
			lits![-1, -2, 3, -4, 5, 6, -7],
			lits![1, -2, -3, 4, 5, 6, -7],
			lits![-1, 2, -3, 4, 5, 6, -7],
			lits![-1, -2, 3, 4, 5, 6, -7],
			lits![1, 2, -3, -4, -5, 6, 7],
			lits![1, -2, 3, -4, -5, 6, 7],
			lits![-1, 2, 3, -4, -5, 6, 7],
			lits![1, 2, -3, 4, -5, 6, 7],
			lits![1, -2, 3, 4, -5, 6, 7],
			lits![-1, 2, 3, 4, -5, 6, 7],
			lits![1, 2, -3, -4, 5, 6, 7],
			lits![1, -2, 3, -4, 5, 6, 7],
			lits![-1, 2, 3, -4, 5, 6, 7],
			lits![1, 2, -3, 4, 5, 6, 7],
			lits![1, -2, 3, 4, 5, 6, 7],
			lits![-1, 2, 3, 4, 5, 6, 7],
		];
		let enc = get_sorted_encoder(SortedStrategy::Recursive);
		// println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_4_sorted_eq() {
		let mut db = TestDB::new(8);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 4, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![1, 2, 3, 4];
		let con = &Sorted::new(&lits, LimitComp::Equal, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);
		let sols = vec![
			lits![-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, -6, -7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, -5, 6, -7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, 6, -7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, -5, -6, 7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, -6, 7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, -5, 6, 7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, 6, 7, -8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, -5, -6, -7, 8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, -6, -7, 8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, -5, 6, -7, 8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, 6, -7, 8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, -5, -6, 7, 8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, -6, 7, 8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, -5, 6, 7, 8, -9, -10, -11, -12],
			lits![-1, -2, -3, -4, 5, 6, 7, 8, -9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, -6, -7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, -6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, -6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, -6, -7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, -6, -7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, -6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, -6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, -6, -7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, 6, -7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, 6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, 6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, 6, -7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, 6, -7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, 6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, 6, -7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, 6, -7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, -6, 7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, -6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, -6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, -6, 7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, -6, 7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, -6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, -6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, -6, 7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, 6, 7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, 6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, 6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, 6, 7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, 6, 7, -8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, 6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, 6, 7, -8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, 6, 7, -8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, -6, -7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, -6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, -6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, -6, -7, 8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, -6, -7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, -6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, -6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, -6, -7, 8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, 6, -7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, 6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, 6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, 6, -7, 8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, 6, -7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, 6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, 6, -7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, 6, -7, 8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, -6, 7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, -6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, -6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, -6, 7, 8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, -6, 7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, -6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, -6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, -6, 7, 8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, -5, 6, 7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, -5, 6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, -5, 6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, -5, 6, 7, 8, 9, -10, -11, -12],
			lits![1, -2, -3, -4, 5, 6, 7, 8, 9, -10, -11, -12],
			lits![-1, 2, -3, -4, 5, 6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, 3, -4, 5, 6, 7, 8, 9, -10, -11, -12],
			lits![-1, -2, -3, 4, 5, 6, 7, 8, 9, -10, -11, -12],
			lits![1, 2, -3, -4, -5, -6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, -6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, -6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, -6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, -6, -7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, -6, -7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, -6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, -6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, -6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, -6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, -6, -7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, -6, -7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, -5, 6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, 6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, 6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, 6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, 6, -7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, 6, -7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, 6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, 6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, 6, -7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, 6, -7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, 6, -7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, 6, -7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, -5, -6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, -6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, -6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, -6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, -6, 7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, -6, 7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, -6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, -6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, -6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, -6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, -6, 7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, -6, 7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, -5, 6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, 6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, 6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, 6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, 6, 7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, 6, 7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, 6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, 6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, 6, 7, -8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, 6, 7, -8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, 6, 7, -8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, 6, 7, -8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, -5, -6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, -6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, -6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, -6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, -6, -7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, -6, -7, 8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, -6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, -6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, -6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, -6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, -6, -7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, -6, -7, 8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, -5, 6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, 6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, 6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, 6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, 6, -7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, 6, -7, 8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, 6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, 6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, 6, -7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, 6, -7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, 6, -7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, 6, -7, 8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, -5, -6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, -6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, -6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, -6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, -6, 7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, -6, 7, 8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, -6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, -6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, -6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, -6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, -6, 7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, -6, 7, 8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, -5, 6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, -5, 6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, -5, 6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, -5, 6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, -5, 6, 7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, -5, 6, 7, 8, 9, 10, -11, -12],
			lits![1, 2, -3, -4, 5, 6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, 3, -4, 5, 6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, 3, -4, 5, 6, 7, 8, 9, 10, -11, -12],
			lits![1, -2, -3, 4, 5, 6, 7, 8, 9, 10, -11, -12],
			lits![-1, 2, -3, 4, 5, 6, 7, 8, 9, 10, -11, -12],
			lits![-1, -2, 3, 4, 5, 6, 7, 8, 9, 10, -11, -12],
			lits![1, 2, 3, -4, -5, -6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, -6, -7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, -6, -7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, -6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, -6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, -6, -7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, -6, -7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, -6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, -5, 6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, 6, -7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, 6, -7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, 6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, 6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, 6, -7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, 6, -7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, 6, -7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, -5, -6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, -6, 7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, -6, 7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, -6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, -6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, -6, 7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, -6, 7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, -6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, -5, 6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, 6, 7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, 6, 7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, 6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, 6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, 6, 7, -8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, 6, 7, -8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, 6, 7, -8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, -5, -6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, -6, -7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, -6, -7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, -6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, -6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, -6, -7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, -6, -7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, -6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, -5, 6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, 6, -7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, 6, -7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, 6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, 6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, 6, -7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, 6, -7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, 6, -7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, -5, -6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, -6, 7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, -6, 7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, -6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, -6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, -6, 7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, -6, 7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, -6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, -5, 6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, -5, 6, 7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, -5, 6, 7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, -5, 6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, -4, 5, 6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, -3, 4, 5, 6, 7, 8, 9, 10, 11, -12],
			lits![1, -2, 3, 4, 5, 6, 7, 8, 9, 10, 11, -12],
			lits![-1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, -12],
			lits![1, 2, 3, 4, -5, -6, -7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, -6, -7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, -5, 6, -7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, 6, -7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, -5, -6, 7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, -6, 7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, -5, 6, 7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, 6, 7, -8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, -5, -6, -7, 8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, -6, -7, 8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, -5, 6, -7, 8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, 6, -7, 8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, -5, -6, 7, 8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, -6, 7, 8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, -5, 6, 7, 8, 9, 10, 11, 12],
			lits![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
		];
		let enc = get_sorted_encoder(SortedStrategy::Recursive);
		// println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_4_2_sorted_eq() {
		let mut db = TestDB::new(6);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 2, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![1, 2, 3, 4];
		let con = &Sorted::new(&lits, LimitComp::Equal, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);

		let sols = vec![
			lits![-1, -2, -3, -4, -5, -6, -7, -8],
			lits![-1, -2, -3, -4, 5, -6, -7, -8],
			lits![-1, -2, -3, -4, -5, 6, -7, -8],
			lits![-1, -2, -3, -4, 5, 6, -7, -8],
			lits![1, -2, -3, -4, -5, -6, 7, -8],
			lits![-1, 2, -3, -4, -5, -6, 7, -8],
			lits![-1, -2, 3, -4, -5, -6, 7, -8],
			lits![-1, -2, -3, 4, -5, -6, 7, -8],
			lits![1, -2, -3, -4, 5, -6, 7, -8],
			lits![-1, 2, -3, -4, 5, -6, 7, -8],
			lits![-1, -2, 3, -4, 5, -6, 7, -8],
			lits![-1, -2, -3, 4, 5, -6, 7, -8],
			lits![1, -2, -3, -4, -5, 6, 7, -8],
			lits![-1, 2, -3, -4, -5, 6, 7, -8],
			lits![-1, -2, 3, -4, -5, 6, 7, -8],
			lits![-1, -2, -3, 4, -5, 6, 7, -8],
			lits![1, -2, -3, -4, 5, 6, 7, -8],
			lits![-1, 2, -3, -4, 5, 6, 7, -8],
			lits![-1, -2, 3, -4, 5, 6, 7, -8],
			lits![-1, -2, -3, 4, 5, 6, 7, -8],
			lits![1, 2, -3, -4, -5, -6, 7, 8],
			lits![1, -2, 3, -4, -5, -6, 7, 8],
			lits![-1, 2, 3, -4, -5, -6, 7, 8],
			lits![1, -2, -3, 4, -5, -6, 7, 8],
			lits![-1, 2, -3, 4, -5, -6, 7, 8],
			lits![-1, -2, 3, 4, -5, -6, 7, 8],
			lits![1, 2, -3, -4, 5, -6, 7, 8],
			lits![1, -2, 3, -4, 5, -6, 7, 8],
			lits![-1, 2, 3, -4, 5, -6, 7, 8],
			lits![1, -2, -3, 4, 5, -6, 7, 8],
			lits![-1, 2, -3, 4, 5, -6, 7, 8],
			lits![-1, -2, 3, 4, 5, -6, 7, 8],
			lits![1, 2, -3, -4, -5, 6, 7, 8],
			lits![1, -2, 3, -4, -5, 6, 7, 8],
			lits![-1, 2, 3, -4, -5, 6, 7, 8],
			lits![1, -2, -3, 4, -5, 6, 7, 8],
			lits![-1, 2, -3, 4, -5, 6, 7, 8],
			lits![-1, -2, 3, 4, -5, 6, 7, 8],
			lits![1, 2, -3, -4, 5, 6, 7, 8],
			lits![1, -2, 3, -4, 5, 6, 7, 8],
			lits![-1, 2, 3, -4, 5, 6, 7, 8],
			lits![1, -2, -3, 4, 5, 6, 7, 8],
			lits![-1, 2, -3, 4, 5, 6, 7, 8],
			lits![-1, -2, 3, 4, 5, 6, 7, 8],
		];
		let enc = get_sorted_encoder(SortedStrategy::Recursive);
		// println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_4_3_sorted_eq() {
		let mut db = TestDB::new(7);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 3, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![1, 2, 3, 4];
		let con = &Sorted::new(&lits, LimitComp::Equal, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);

		let sols = vec![
			lits![-1, -2, -3, -4, -5, -6, -7, -8, -9, -10],
			lits![-1, -2, -3, -4, 5, -6, -7, -8, -9, -10],
			lits![-1, -2, -3, -4, -5, 6, -7, -8, -9, -10],
			lits![-1, -2, -3, -4, 5, 6, -7, -8, -9, -10],
			lits![-1, -2, -3, -4, -5, -6, 7, -8, -9, -10],
			lits![-1, -2, -3, -4, 5, -6, 7, -8, -9, -10],
			lits![-1, -2, -3, -4, -5, 6, 7, -8, -9, -10],
			lits![-1, -2, -3, -4, 5, 6, 7, -8, -9, -10],
			lits![1, -2, -3, -4, -5, -6, -7, 8, -9, -10],
			lits![-1, 2, -3, -4, -5, -6, -7, 8, -9, -10],
			lits![-1, -2, 3, -4, -5, -6, -7, 8, -9, -10],
			lits![-1, -2, -3, 4, -5, -6, -7, 8, -9, -10],
			lits![1, -2, -3, -4, 5, -6, -7, 8, -9, -10],
			lits![-1, 2, -3, -4, 5, -6, -7, 8, -9, -10],
			lits![-1, -2, 3, -4, 5, -6, -7, 8, -9, -10],
			lits![-1, -2, -3, 4, 5, -6, -7, 8, -9, -10],
			lits![1, -2, -3, -4, -5, 6, -7, 8, -9, -10],
			lits![-1, 2, -3, -4, -5, 6, -7, 8, -9, -10],
			lits![-1, -2, 3, -4, -5, 6, -7, 8, -9, -10],
			lits![-1, -2, -3, 4, -5, 6, -7, 8, -9, -10],
			lits![1, -2, -3, -4, 5, 6, -7, 8, -9, -10],
			lits![-1, 2, -3, -4, 5, 6, -7, 8, -9, -10],
			lits![-1, -2, 3, -4, 5, 6, -7, 8, -9, -10],
			lits![-1, -2, -3, 4, 5, 6, -7, 8, -9, -10],
			lits![1, -2, -3, -4, -5, -6, 7, 8, -9, -10],
			lits![-1, 2, -3, -4, -5, -6, 7, 8, -9, -10],
			lits![-1, -2, 3, -4, -5, -6, 7, 8, -9, -10],
			lits![-1, -2, -3, 4, -5, -6, 7, 8, -9, -10],
			lits![1, -2, -3, -4, 5, -6, 7, 8, -9, -10],
			lits![-1, 2, -3, -4, 5, -6, 7, 8, -9, -10],
			lits![-1, -2, 3, -4, 5, -6, 7, 8, -9, -10],
			lits![-1, -2, -3, 4, 5, -6, 7, 8, -9, -10],
			lits![1, -2, -3, -4, -5, 6, 7, 8, -9, -10],
			lits![-1, 2, -3, -4, -5, 6, 7, 8, -9, -10],
			lits![-1, -2, 3, -4, -5, 6, 7, 8, -9, -10],
			lits![-1, -2, -3, 4, -5, 6, 7, 8, -9, -10],
			lits![1, -2, -3, -4, 5, 6, 7, 8, -9, -10],
			lits![-1, 2, -3, -4, 5, 6, 7, 8, -9, -10],
			lits![-1, -2, 3, -4, 5, 6, 7, 8, -9, -10],
			lits![-1, -2, -3, 4, 5, 6, 7, 8, -9, -10],
			lits![1, 2, -3, -4, -5, -6, -7, 8, 9, -10],
			lits![1, -2, 3, -4, -5, -6, -7, 8, 9, -10],
			lits![-1, 2, 3, -4, -5, -6, -7, 8, 9, -10],
			lits![1, -2, -3, 4, -5, -6, -7, 8, 9, -10],
			lits![-1, 2, -3, 4, -5, -6, -7, 8, 9, -10],
			lits![-1, -2, 3, 4, -5, -6, -7, 8, 9, -10],
			lits![1, 2, -3, -4, 5, -6, -7, 8, 9, -10],
			lits![1, -2, 3, -4, 5, -6, -7, 8, 9, -10],
			lits![-1, 2, 3, -4, 5, -6, -7, 8, 9, -10],
			lits![1, -2, -3, 4, 5, -6, -7, 8, 9, -10],
			lits![-1, 2, -3, 4, 5, -6, -7, 8, 9, -10],
			lits![-1, -2, 3, 4, 5, -6, -7, 8, 9, -10],
			lits![1, 2, -3, -4, -5, 6, -7, 8, 9, -10],
			lits![1, -2, 3, -4, -5, 6, -7, 8, 9, -10],
			lits![-1, 2, 3, -4, -5, 6, -7, 8, 9, -10],
			lits![1, -2, -3, 4, -5, 6, -7, 8, 9, -10],
			lits![-1, 2, -3, 4, -5, 6, -7, 8, 9, -10],
			lits![-1, -2, 3, 4, -5, 6, -7, 8, 9, -10],
			lits![1, 2, -3, -4, 5, 6, -7, 8, 9, -10],
			lits![1, -2, 3, -4, 5, 6, -7, 8, 9, -10],
			lits![-1, 2, 3, -4, 5, 6, -7, 8, 9, -10],
			lits![1, -2, -3, 4, 5, 6, -7, 8, 9, -10],
			lits![-1, 2, -3, 4, 5, 6, -7, 8, 9, -10],
			lits![-1, -2, 3, 4, 5, 6, -7, 8, 9, -10],
			lits![1, 2, -3, -4, -5, -6, 7, 8, 9, -10],
			lits![1, -2, 3, -4, -5, -6, 7, 8, 9, -10],
			lits![-1, 2, 3, -4, -5, -6, 7, 8, 9, -10],
			lits![1, -2, -3, 4, -5, -6, 7, 8, 9, -10],
			lits![-1, 2, -3, 4, -5, -6, 7, 8, 9, -10],
			lits![-1, -2, 3, 4, -5, -6, 7, 8, 9, -10],
			lits![1, 2, -3, -4, 5, -6, 7, 8, 9, -10],
			lits![1, -2, 3, -4, 5, -6, 7, 8, 9, -10],
			lits![-1, 2, 3, -4, 5, -6, 7, 8, 9, -10],
			lits![1, -2, -3, 4, 5, -6, 7, 8, 9, -10],
			lits![-1, 2, -3, 4, 5, -6, 7, 8, 9, -10],
			lits![-1, -2, 3, 4, 5, -6, 7, 8, 9, -10],
			lits![1, 2, -3, -4, -5, 6, 7, 8, 9, -10],
			lits![1, -2, 3, -4, -5, 6, 7, 8, 9, -10],
			lits![-1, 2, 3, -4, -5, 6, 7, 8, 9, -10],
			lits![1, -2, -3, 4, -5, 6, 7, 8, 9, -10],
			lits![-1, 2, -3, 4, -5, 6, 7, 8, 9, -10],
			lits![-1, -2, 3, 4, -5, 6, 7, 8, 9, -10],
			lits![1, 2, -3, -4, 5, 6, 7, 8, 9, -10],
			lits![1, -2, 3, -4, 5, 6, 7, 8, 9, -10],
			lits![-1, 2, 3, -4, 5, 6, 7, 8, 9, -10],
			lits![1, -2, -3, 4, 5, 6, 7, 8, 9, -10],
			lits![-1, 2, -3, 4, 5, 6, 7, 8, 9, -10],
			lits![-1, -2, 3, 4, 5, 6, 7, 8, 9, -10],
			lits![1, 2, 3, -4, -5, -6, -7, 8, 9, 10],
			lits![1, 2, -3, 4, -5, -6, -7, 8, 9, 10],
			lits![1, -2, 3, 4, -5, -6, -7, 8, 9, 10],
			lits![-1, 2, 3, 4, -5, -6, -7, 8, 9, 10],
			lits![1, 2, 3, -4, 5, -6, -7, 8, 9, 10],
			lits![1, 2, -3, 4, 5, -6, -7, 8, 9, 10],
			lits![1, -2, 3, 4, 5, -6, -7, 8, 9, 10],
			lits![-1, 2, 3, 4, 5, -6, -7, 8, 9, 10],
			lits![1, 2, 3, -4, -5, 6, -7, 8, 9, 10],
			lits![1, 2, -3, 4, -5, 6, -7, 8, 9, 10],
			lits![1, -2, 3, 4, -5, 6, -7, 8, 9, 10],
			lits![-1, 2, 3, 4, -5, 6, -7, 8, 9, 10],
			lits![1, 2, 3, -4, 5, 6, -7, 8, 9, 10],
			lits![1, 2, -3, 4, 5, 6, -7, 8, 9, 10],
			lits![1, -2, 3, 4, 5, 6, -7, 8, 9, 10],
			lits![-1, 2, 3, 4, 5, 6, -7, 8, 9, 10],
			lits![1, 2, 3, -4, -5, -6, 7, 8, 9, 10],
			lits![1, 2, -3, 4, -5, -6, 7, 8, 9, 10],
			lits![1, -2, 3, 4, -5, -6, 7, 8, 9, 10],
			lits![-1, 2, 3, 4, -5, -6, 7, 8, 9, 10],
			lits![1, 2, 3, -4, 5, -6, 7, 8, 9, 10],
			lits![1, 2, -3, 4, 5, -6, 7, 8, 9, 10],
			lits![1, -2, 3, 4, 5, -6, 7, 8, 9, 10],
			lits![-1, 2, 3, 4, 5, -6, 7, 8, 9, 10],
			lits![1, 2, 3, -4, -5, 6, 7, 8, 9, 10],
			lits![1, 2, -3, 4, -5, 6, 7, 8, 9, 10],
			lits![1, -2, 3, 4, -5, 6, 7, 8, 9, 10],
			lits![-1, 2, 3, 4, -5, 6, 7, 8, 9, 10],
			lits![1, 2, 3, -4, 5, 6, 7, 8, 9, 10],
			lits![1, 2, -3, 4, 5, 6, 7, 8, 9, 10],
			lits![1, -2, 3, 4, 5, 6, 7, 8, 9, 10],
			lits![-1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
		];
		let enc = get_sorted_encoder(SortedStrategy::Recursive);
		// println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
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
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 3, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![1, 2, 3, 4, 5];
		let con = &Sorted::new(&lits, LimitComp::Equal, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);

		let sols = vec![
			lits![-1, -2, -3, -4, -5, -6, -7, -8, -9, -10, -11],
			lits![-1, -2, -3, -4, -5, 6, -7, -8, -9, -10, -11],
			lits![-1, -2, -3, -4, -5, -6, 7, -8, -9, -10, -11],
			lits![-1, -2, -3, -4, -5, 6, 7, -8, -9, -10, -11],
			lits![-1, -2, -3, -4, -5, -6, -7, 8, -9, -10, -11],
			lits![-1, -2, -3, -4, -5, 6, -7, 8, -9, -10, -11],
			lits![-1, -2, -3, -4, -5, -6, 7, 8, -9, -10, -11],
			lits![-1, -2, -3, -4, -5, 6, 7, 8, -9, -10, -11],
			lits![1, -2, -3, -4, -5, -6, -7, -8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, -6, -7, -8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, -6, -7, -8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, -6, -7, -8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, -6, -7, -8, 9, -10, -11],
			lits![1, -2, -3, -4, -5, 6, -7, -8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, 6, -7, -8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, 6, -7, -8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, 6, -7, -8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, 6, -7, -8, 9, -10, -11],
			lits![1, -2, -3, -4, -5, -6, 7, -8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, -6, 7, -8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, -6, 7, -8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, -6, 7, -8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, -6, 7, -8, 9, -10, -11],
			lits![1, -2, -3, -4, -5, 6, 7, -8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, 6, 7, -8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, 6, 7, -8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, 6, 7, -8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, 6, 7, -8, 9, -10, -11],
			lits![1, -2, -3, -4, -5, -6, -7, 8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, -6, -7, 8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, -6, -7, 8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, -6, -7, 8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, -6, -7, 8, 9, -10, -11],
			lits![1, -2, -3, -4, -5, 6, -7, 8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, 6, -7, 8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, 6, -7, 8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, 6, -7, 8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, 6, -7, 8, 9, -10, -11],
			lits![1, -2, -3, -4, -5, -6, 7, 8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, -6, 7, 8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, -6, 7, 8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, -6, 7, 8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, -6, 7, 8, 9, -10, -11],
			lits![1, -2, -3, -4, -5, 6, 7, 8, 9, -10, -11],
			lits![-1, 2, -3, -4, -5, 6, 7, 8, 9, -10, -11],
			lits![-1, -2, 3, -4, -5, 6, 7, 8, 9, -10, -11],
			lits![-1, -2, -3, 4, -5, 6, 7, 8, 9, -10, -11],
			lits![-1, -2, -3, -4, 5, 6, 7, 8, 9, -10, -11],
			lits![1, 2, -3, -4, -5, -6, -7, -8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, -6, -7, -8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, -6, -7, -8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, -6, -7, -8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, -6, -7, -8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, -6, -7, -8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, -6, -7, -8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, -6, -7, -8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, -6, -7, -8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, -6, -7, -8, 9, 10, -11],
			lits![1, 2, -3, -4, -5, 6, -7, -8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, 6, -7, -8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, 6, -7, -8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, 6, -7, -8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, 6, -7, -8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, 6, -7, -8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, 6, -7, -8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, 6, -7, -8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, 6, -7, -8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, 6, -7, -8, 9, 10, -11],
			lits![1, 2, -3, -4, -5, -6, 7, -8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, -6, 7, -8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, -6, 7, -8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, -6, 7, -8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, -6, 7, -8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, -6, 7, -8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, -6, 7, -8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, -6, 7, -8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, -6, 7, -8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, -6, 7, -8, 9, 10, -11],
			lits![1, 2, -3, -4, -5, 6, 7, -8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, 6, 7, -8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, 6, 7, -8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, 6, 7, -8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, 6, 7, -8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, 6, 7, -8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, 6, 7, -8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, 6, 7, -8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, 6, 7, -8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, 6, 7, -8, 9, 10, -11],
			lits![1, 2, -3, -4, -5, -6, -7, 8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, -6, -7, 8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, -6, -7, 8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, -6, -7, 8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, -6, -7, 8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, -6, -7, 8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, -6, -7, 8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, -6, -7, 8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, -6, -7, 8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, -6, -7, 8, 9, 10, -11],
			lits![1, 2, -3, -4, -5, 6, -7, 8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, 6, -7, 8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, 6, -7, 8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, 6, -7, 8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, 6, -7, 8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, 6, -7, 8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, 6, -7, 8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, 6, -7, 8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, 6, -7, 8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, 6, -7, 8, 9, 10, -11],
			lits![1, 2, -3, -4, -5, -6, 7, 8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, -6, 7, 8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, -6, 7, 8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, -6, 7, 8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, -6, 7, 8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, -6, 7, 8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, -6, 7, 8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, -6, 7, 8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, -6, 7, 8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, -6, 7, 8, 9, 10, -11],
			lits![1, 2, -3, -4, -5, 6, 7, 8, 9, 10, -11],
			lits![1, -2, 3, -4, -5, 6, 7, 8, 9, 10, -11],
			lits![-1, 2, 3, -4, -5, 6, 7, 8, 9, 10, -11],
			lits![1, -2, -3, 4, -5, 6, 7, 8, 9, 10, -11],
			lits![-1, 2, -3, 4, -5, 6, 7, 8, 9, 10, -11],
			lits![-1, -2, 3, 4, -5, 6, 7, 8, 9, 10, -11],
			lits![1, -2, -3, -4, 5, 6, 7, 8, 9, 10, -11],
			lits![-1, 2, -3, -4, 5, 6, 7, 8, 9, 10, -11],
			lits![-1, -2, 3, -4, 5, 6, 7, 8, 9, 10, -11],
			lits![-1, -2, -3, 4, 5, 6, 7, 8, 9, 10, -11],
			lits![1, 2, 3, -4, -5, -6, -7, -8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, -6, -7, -8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, -6, -7, -8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, -6, -7, -8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, -6, -7, -8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, -6, -7, -8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, -6, -7, -8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, -6, -7, -8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, -6, -7, -8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, -6, -7, -8, 9, 10, 11],
			lits![1, 2, 3, -4, -5, 6, -7, -8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, 6, -7, -8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, 6, -7, -8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, 6, -7, -8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, 6, -7, -8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, 6, -7, -8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, 6, -7, -8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, 6, -7, -8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, 6, -7, -8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, 6, -7, -8, 9, 10, 11],
			lits![1, 2, 3, -4, -5, -6, 7, -8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, -6, 7, -8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, -6, 7, -8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, -6, 7, -8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, -6, 7, -8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, -6, 7, -8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, -6, 7, -8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, -6, 7, -8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, -6, 7, -8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, -6, 7, -8, 9, 10, 11],
			lits![1, 2, 3, -4, -5, 6, 7, -8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, 6, 7, -8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, 6, 7, -8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, 6, 7, -8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, 6, 7, -8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, 6, 7, -8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, 6, 7, -8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, 6, 7, -8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, 6, 7, -8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, 6, 7, -8, 9, 10, 11],
			lits![1, 2, 3, -4, -5, -6, -7, 8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, -6, -7, 8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, -6, -7, 8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, -6, -7, 8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, -6, -7, 8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, -6, -7, 8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, -6, -7, 8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, -6, -7, 8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, -6, -7, 8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, -6, -7, 8, 9, 10, 11],
			lits![1, 2, 3, -4, -5, 6, -7, 8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, 6, -7, 8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, 6, -7, 8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, 6, -7, 8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, 6, -7, 8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, 6, -7, 8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, 6, -7, 8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, 6, -7, 8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, 6, -7, 8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, 6, -7, 8, 9, 10, 11],
			lits![1, 2, 3, -4, -5, -6, 7, 8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, -6, 7, 8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, -6, 7, 8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, -6, 7, 8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, -6, 7, 8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, -6, 7, 8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, -6, 7, 8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, -6, 7, 8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, -6, 7, 8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, -6, 7, 8, 9, 10, 11],
			lits![1, 2, 3, -4, -5, 6, 7, 8, 9, 10, 11],
			lits![1, 2, -3, 4, -5, 6, 7, 8, 9, 10, 11],
			lits![1, -2, 3, 4, -5, 6, 7, 8, 9, 10, 11],
			lits![-1, 2, 3, 4, -5, 6, 7, 8, 9, 10, 11],
			lits![1, 2, -3, -4, 5, 6, 7, 8, 9, 10, 11],
			lits![1, -2, 3, -4, 5, 6, 7, 8, 9, 10, 11],
			lits![-1, 2, 3, -4, 5, 6, 7, 8, 9, 10, 11],
			lits![1, -2, -3, 4, 5, 6, 7, 8, 9, 10, 11],
			lits![-1, 2, -3, 4, 5, 6, 7, 8, 9, 10, 11],
			lits![-1, -2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
		];
		let enc = get_sorted_encoder(SortedStrategy::Recursive);
		// println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}

	// #[test]
	fn _test_5_6_sorted_eq() {
		let mut db = TestDB::new(11);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 5, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let con = &Sorted::new(&[1, 2, 3, 4, 5, 6], LimitComp::Equal, &y);
		let sols = db.brute_force_solve(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = get_sorted_encoder(SortedStrategy::Recursive);
		println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}

	// #[test]
	fn _test_6_7_sorted_eq() {
		let mut db = TestDB::new(13);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 6, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let con = &Sorted::new(&[1, 2, 3, 4, 5, 6, 7], LimitComp::Equal, &y);
		let sols = db.brute_force_solve(|sol| con.check(sol).is_ok(), db.num_var);
		let mut enc = get_sorted_encoder(SortedStrategy::Recursive);
		println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}

	#[test]
	fn test_5_1_sorted_eq_negated() {
		let mut db = TestDB::new(6);
		let y: IntVarEnc = IntVarOrd::from_bounds(&mut db, 0, 1, String::from("y")).into();
		db.num_var += y.lits() as i32;
		let lits = lits![-1, -2, -3, -4, -5];
		let con = &Sorted::new(&lits, LimitComp::LessEq, &y);
		// let sols = db.generate_solutions(|sol| con.check(sol).is_ok(), db.num_var);

		let sols = vec![
			lits![1, 2, 3, 4, 5, -6, -7],
			lits![1, 2, 3, 4, 5, 6, -7],
			lits![1, 2, 3, 4, -5, -6, 7],
			lits![1, 2, 3, -4, 5, -6, 7],
			lits![1, 2, -3, 4, 5, -6, 7],
			lits![1, -2, 3, 4, 5, -6, 7],
			lits![-1, 2, 3, 4, 5, -6, 7],
			lits![1, 2, 3, 4, 5, -6, 7],
			lits![1, 2, 3, 4, -5, 6, 7],
			lits![1, 2, 3, -4, 5, 6, 7],
			lits![1, 2, -3, 4, 5, 6, 7],
			lits![1, -2, 3, 4, 5, 6, 7],
			lits![-1, 2, 3, 4, 5, 6, 7],
			lits![1, 2, 3, 4, 5, 6, 7],
		];
		let enc = get_sorted_encoder(SortedStrategy::Direct);
		// println!("\nlet sols = {};", TestDB::_print_solutions(&sols));
		assert_sol!(db => enc, con => sols);
	}
}
*/
