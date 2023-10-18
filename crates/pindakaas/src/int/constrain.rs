use itertools::Itertools;

use crate::helpers::{add_clauses_for, negate_cnf};
use crate::linear::log_enc_add_;
use crate::{helpers::as_binary, linear::LinExp, Coefficient, Literal};
use crate::{CheckError, Checker, ClauseDatabase, Comparator, Encoder, Unsatisfiable};
use std::fmt;

use super::enc::GROUND_BINARY_AT_LB;
use super::{IntVarBin, IntVarEnc, LitOrConst};

#[derive(Debug)]
pub(crate) struct TernLeConstraint<'a, Lit: Literal, C: Coefficient> {
	pub(crate) x: &'a IntVarEnc<Lit, C>,
	pub(crate) y: &'a IntVarEnc<Lit, C>,
	pub(crate) cmp: &'a Comparator,
	pub(crate) z: &'a IntVarEnc<Lit, C>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraint<'a, Lit, C> {
	pub fn new(
		x: &'a IntVarEnc<Lit, C>,
		y: &'a IntVarEnc<Lit, C>,
		cmp: &'a Comparator,
		z: &'a IntVarEnc<Lit, C>,
	) -> Self {
		Self { x, y, cmp, z }
	}

	pub fn is_fixed(&self) -> Result<bool, Unsatisfiable> {
		let TernLeConstraint { x, y, cmp, z } = self;
		if let IntVarEnc::Const(x) = x {
			if let IntVarEnc::Const(y) = y {
				if let IntVarEnc::Const(z) = z {
					return if Self::check(x, y, cmp, z) {
						Ok(true)
					} else {
						Err(Unsatisfiable)
					};
				}
			}
		}
		Ok(false)
	}

	fn check(x: &C, y: &C, cmp: &Comparator, z: &C) -> bool {
		match cmp {
			Comparator::LessEq => *x + *y <= *z,
			Comparator::Equal => *x + *y == *z,
			Comparator::GreaterEq => *x + *y >= *z,
		}
	}
}

impl<'a, Lit: Literal, C: Coefficient> Checker for TernLeConstraint<'a, Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let x = &LinExp::from(self.x).assign(solution)?;
		let y = &LinExp::from(self.y).assign(solution)?;
		let z = &LinExp::from(self.z).assign(solution)?;
		if Self::check(x, y, self.cmp, z) {
			Ok(())
		} else {
			Err(CheckError::Fail(format!(
				"Failed constraint {self} since {x}+{y} # {z}"
			)))
		}
	}
}

impl<Lit: Literal, C: Coefficient> fmt::Display for TernLeConstraint<'_, Lit, C> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} + {} {} {}", self.x, self.y, self.cmp, self.z)
	}
}

#[allow(dead_code)] // TODO
pub(crate) struct TernLeConstraintContainer<Lit: Literal, C: Coefficient> {
	pub(crate) x: IntVarEnc<Lit, C>,
	pub(crate) y: IntVarEnc<Lit, C>,
	pub(crate) cmp: Comparator,
	pub(crate) z: IntVarEnc<Lit, C>,
}

impl<'a, Lit: Literal, C: Coefficient> TernLeConstraintContainer<Lit, C> {
	#[allow(dead_code)]
	pub(crate) fn get(&'a self) -> TernLeConstraint<'a, Lit, C> {
		TernLeConstraint {
			x: &self.x,
			y: &self.y,
			cmp: &self.cmp,
			z: &self.z,
		}
	}
}

#[derive(Debug, Default)]
pub(crate) struct TernLeEncoder {}

const ENCODE_REDUNDANT_X_O_Y_O_Z_B: bool = true;

impl<'a, DB: ClauseDatabase, C: Coefficient> Encoder<DB, TernLeConstraint<'a, DB::Lit, C>>
	for TernLeEncoder
{
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "tern_le_encoder", skip_all, fields(constraint = format!("{} + {} {} {}", tern.x, tern.y, tern.cmp, tern.z)))
	)]
	fn encode(&mut self, db: &mut DB, tern: &TernLeConstraint<DB::Lit, C>) -> crate::Result {
		#[cfg(debug_assertions)]
		{
			const PRINT_TESTCASES: bool = false;
			if PRINT_TESTCASES {
				println!(" // {tern}");
				let x = tern
					.x
					.dom()
					.iter(..)
					.map(|iv| iv.end - C::one())
					.collect::<Vec<_>>();
				let y = tern
					.y
					.dom()
					.iter(..)
					.map(|iv| iv.end - C::one())
					.collect::<Vec<_>>();
				let z = tern
					.z
					.dom()
					.iter(..)
					.map(|iv| iv.end - C::one())
					.collect::<Vec<_>>();
				println!(
					"mod _test_{}_{}_{} {{
                test_int_lin!($encoder, &[{}], &[{}], $cmp, &[{}]);
                }}
                ",
					x.iter().join(""),
					y.iter().join(""),
					z.iter().join(""),
					x.iter().join(", "),
					y.iter().join(", "),
					z.iter().join(", "),
				);
			}
		}

		let TernLeConstraint { x, y, cmp, z } = *tern;

		return match (x, y, z) {
			(IntVarEnc::Const(_), IntVarEnc::Const(_), IntVarEnc::Const(_)) => {
				if tern.check(&[]).is_ok() {
					Ok(())
				} else {
					Err(Unsatisfiable)
				}
			}
			(IntVarEnc::Const(x_con), IntVarEnc::Const(y_con), IntVarEnc::Bin(z_bin)) => z_bin
				.encode_unary_constraint(
					db,
					&match cmp {
						Comparator::Equal => Comparator::Equal,
						Comparator::LessEq => Comparator::GreaterEq,
						Comparator::GreaterEq => Comparator::LessEq,
					},
					*x_con + *y_con,
					false,
				),
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y_con), IntVarEnc::Const(z_con))
			| (IntVarEnc::Const(y_con), IntVarEnc::Bin(x_bin), IntVarEnc::Const(z_con)) => {
				// and rest is const ~ lex constraint
				x_bin.encode_unary_constraint(db, cmp, *z_con - *y_con, false)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y_const), IntVarEnc::Bin(z_bin))
			| (IntVarEnc::Const(y_const), IntVarEnc::Bin(x_bin), IntVarEnc::Bin(z_bin)) => {
				let (x_bin, y_const) = if matches!(cmp, Comparator::LessEq | Comparator::GreaterEq)
				{
					let x_bin = x_bin.add(db, self, *y_const)?;
					x_bin.consistent(db)?;
					(x_bin, C::zero())
				} else {
					(
						x_bin.clone(),
						// TODO unclear why this.
						if GROUND_BINARY_AT_LB {
							C::zero()
						} else {
							*y_const
						},
					)
				};
				log_enc_add_(
					db,
					&x_bin.xs(false).into_iter().collect::<Vec<_>>(),
					&as_binary::<DB::Lit, C>(y_const.into(), Some(x_bin.lits()))
						.into_iter()
						.map(LitOrConst::Const)
						.chain([LitOrConst::Const(false)])
						.collect::<Vec<_>>(),
					cmp,
					&z_bin.xs(false).into_iter().collect::<Vec<_>>(),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Bin(y_bin), IntVarEnc::Bin(z_bin)) => {
				// y and z are also bin ~ use adder
				match cmp {
					Comparator::Equal => log_enc_add_(
						db,
						&x_bin.xs(false),
						&y_bin.xs(false),
						cmp,
						&z_bin.xs(false),
					),
					ineq => {
						// TODO could add Some(z.ub()) IF cmp == Equal?
						let xy = x.add(db, self, y, None, None)?;
						xy.consistent(db)?; // TODO can be removed if grounding is correct
						self.encode(
							db,
							&TernLeConstraint::new(&xy, &IntVarEnc::Const(C::zero()), ineq, z),
						)
					}
				}
			}
			(IntVarEnc::Bin(_), IntVarEnc::Bin(_), _) => {
				// y/y is bin but z is not bin ~ redundantly encode y + z_bin in 0..z # z and z_bin <= z
				// TODO better coupling ;
				// TODO could add Some(z.ub()) IF cmp == Equal?
				let z_bin = x.add(db, self, y, None, None)?;
				z_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(
						&z_bin,
						&IntVarEnc::Const(C::zero()),
						&(*cmp).clone(),
						z,
					),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Ord(y_ord), _)
			| (IntVarEnc::Ord(y_ord), IntVarEnc::Bin(x_bin), _) => {
				// y is order and z is bin or const ~ redundant y_bin = y_ord and x_bin + y_bin # z
				let y_bin = IntVarBin::from_bounds(
					db,
					y_ord.lb(),
					y_ord.ub(),
					format!("{}{cmp}y:B", y_ord.lbl),
				);

				// channel
				self.encode(
					db,
					&TernLeConstraint::new(
						&y_ord.clone().into(),
						&IntVarEnc::Const(C::zero()), // TODO maybe - lb
						cmp,
						&y_bin.clone().into(),
					),
				)
				.unwrap();
				y_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(&x_bin.clone().into(), &y_bin.into(), cmp, z),
				)
			}
			(IntVarEnc::Ord(_), IntVarEnc::Ord(_), IntVarEnc::Bin(_))
				if ENCODE_REDUNDANT_X_O_Y_O_Z_B =>
			{
				// Avoid too many coupling clause
				let xy_ord = x.add(db, self, y, None, None)?;
				// TODO why necessary?
				xy_ord.consistent(db)?;

				// TODO `x:O.add(y:O)` does not add clauses yet
				self.encode(db, &TernLeConstraint::new(x, y, cmp, &xy_ord))?;

				self.encode(
					db,
					&TernLeConstraint::new(&xy_ord, &IntVarEnc::Const(C::zero()), cmp, z),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(c), IntVarEnc::Ord(_))
			| (IntVarEnc::Const(c), IntVarEnc::Bin(x_bin), IntVarEnc::Ord(_)) => {
				let z = z.add(
					db,
					self,
					&IntVarEnc::Const(c.neg()),
					Some(z.lb()),
					Some(z.ub()),
				)?;

				// x + c <= z == z-c >= x == /\ (z'<=a -> x<=a)
				if cmp == &Comparator::LessEq || cmp == &Comparator::Equal {
					for (c_a, z_leq_c_a) in z.leqs() {
						// TODO alt; just propagate by adding lex constraint
						let c_a = if z_leq_c_a.is_empty() {
							c_a.start..(x.ub() + C::one())
						} else {
							c_a
						};

						let x_leq_c_a = x_bin.leq(c_a.clone());
						add_clauses_for(db, vec![negate_cnf(z_leq_c_a.clone()), x_leq_c_a])?;
					}
				}
				if cmp == &Comparator::GreaterEq || cmp == &Comparator::Equal {
					for (c_a, z_geq_c_a) in z.geqs() {
						let c_a = if z_geq_c_a.is_empty() {
							x.lb()..c_a.end
						} else {
							c_a
						};
						let x_geq_c_a = x_bin.geq(c_a.clone());
						add_clauses_for(db, vec![negate_cnf(z_geq_c_a.clone()), x_geq_c_a])?;
					}
				}
				Ok(())
			}
			(x, y, z) => {
				// couple or constrain x:E + y:E <= z:E
				if cmp == &Comparator::LessEq || cmp == &Comparator::Equal {
					for (c_a, x_geq_c_a) in x.geqs() {
						for (c_b, y_geq_c_b) in y.geqs() {
							// TODO is the max actually correct/good?
							let c_c = (std::cmp::max(c_a.start, c_b.start))
								..(((c_a.end - C::one()) + (c_b.end - C::one())) + C::one());

							let z_geq_c_c = z.geq(c_c.clone());

							add_clauses_for(
								db,
								vec![
									negate_cnf(x_geq_c_a.clone()),
									negate_cnf(y_geq_c_b),
									z_geq_c_c,
								],
							)?;
						}
					}
				}
				// x<=a /\ y<=b -> z<=a+b
				if cmp == &Comparator::GreaterEq || cmp == &Comparator::Equal {
					for (c_a, x_leq_c_a) in x.leqs() {
						for (c_b, y_leq_c_b) in y.leqs() {
							let c_c = (c_a.start + c_b.start)
								..(c_a.end - C::one() + c_b.end - C::one()) + C::one();

							let z_leq_c_c = z.leq(c_c.clone());

							add_clauses_for(
								db,
								vec![
									negate_cnf(x_leq_c_a.clone()),
									negate_cnf(y_leq_c_b),
									z_leq_c_c,
								],
							)?;
						}
					}
				}
				return Ok(());
			}
		};
	}
}

#[cfg(test)]
pub mod tests {

	use super::*;
	use crate::{
		helpers::tests::{assert_sol, assert_unsat, TestDB},
		int::{enc::GROUND_BINARY_AT_LB, IntVar, IntVarOrd},
	};
	use iset::{interval_set, IntervalSet};

	#[cfg(feature = "trace")]
	use traced_test::test;

	macro_rules! test_int_lin {
		($encoder:expr,$x:expr,$y:expr,$cmp:expr,$z:expr) => {
			use super::*;
			#[cfg(feature = "trace")]
			use traced_test::test;

			#[test]
			fn o_o_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Ord,
						IntVarEncoding::Ord
					]
				);
			}

			#[test]
			fn o_o_b() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Ord,
						IntVarEncoding::Bin
					]
				);
			}

			#[test]
			fn o_b_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Bin,
						IntVarEncoding::Ord
					]
				);
			}

			#[test]
			fn o_b_b() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Ord,
						IntVarEncoding::Bin,
						IntVarEncoding::Bin
					]
				);
			}

			#[test]
			fn b_o_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Bin,
						IntVarEncoding::Ord,
						IntVarEncoding::Ord
					]
				);
			}

			#[test]
			fn b_o_b() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Bin,
						IntVarEncoding::Ord,
						IntVarEncoding::Bin
					]
				);
			}

			#[test]
			fn b_b_o() {
				test_int_lin_encs!(
					$encoder,
					$x,
					$y,
					$cmp,
					$z,
					&[
						IntVarEncoding::Bin,
						IntVarEncoding::Bin,
						IntVarEncoding::Ord
					]
				);
			}
		};
	}

	macro_rules! test_int_lin_encs {
		($encoder:expr,$x:expr,$y:expr,$cmp:expr,$z:expr,$encs:expr) => {
			let mut db = TestDB::new(0);
			let x = from_dom(&mut db, $x, &$encs[0], String::from("x"));
			let y = from_dom(&mut db, $y, &$encs[1], String::from("y"));
			let z = from_dom(&mut db, $z, &$encs[2], String::from("z"));

			db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

			let tern = TernLeConstraint {
				x: &x,
				y: &y,
				cmp: &$cmp,
				z: &z,
			};

			let sols =
				db.brute_force_solve(
					|sol| {
						tern.check(sol).is_ok()
					},
					db.num_var,
					);

			x.consistent(&mut db).unwrap();
			y.consistent(&mut db).unwrap();
			z.consistent(&mut db).unwrap();
			if sols.is_empty() {
				assert_unsat!(db => TernLeEncoder::default(), &tern)
			} else {
				assert_sol!(db => TernLeEncoder::default(), &tern => sols);
			}
		}
	}

	macro_rules! int_lin_test_suite {
		($encoder:expr,$cmp:expr) => {
			use super::*;

			mod _012_0_012 {
				test_int_lin!($encoder, &[0, 1, 2], &[0], $cmp, &[0, 1, 2]);
			}

			mod _01_1_2 {
				test_int_lin!($encoder, &[0, 1], &[1], $cmp, &[2]);
			}

			mod _01_1_12 {
				test_int_lin!($encoder, &[0, 1], &[1], $cmp, &[1, 2]);
			}

			mod _01_01_012 {
				test_int_lin!($encoder, &[0, 1], &[0, 1], $cmp, &[0, 1, 2]);
			}

			mod _01_012_3 {
				test_int_lin!($encoder, &[0, 1], &[0, 1, 2], $cmp, &[3]);
			}

			mod _01_01_3 {
				test_int_lin!($encoder, &[0, 1], &[0, 1], $cmp, &[3]);
			}

			mod _0123_23_2345 {
				test_int_lin!($encoder, &[0, 1, 2, 3], &[2, 3], $cmp, &[2, 3, 4, 5]);
			}

			mod _test_01_02_01 {
				test_int_lin!($encoder, &[0, 1], &[0, 2], $cmp, &[0, 1]);
			}

			mod _012478_0_0123456789 {
				test_int_lin!(
					$encoder,
					&[0, 1, 2, 4, 7, 8],
					&[0],
					$cmp,
					&[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
				);
			}
		};
	}

	mod int_lin_le {
		int_lin_test_suite!(TernLeEncoder::default(), Comparator::LessEq);
	}

	mod int_lin_ge {
		int_lin_test_suite!(TernLeEncoder::default(), Comparator::GreaterEq);
	}

	mod int_lin_eq {
		int_lin_test_suite!(TernLeEncoder::default(), Comparator::Equal);
	}

	fn get_ord_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: IntervalSet<C>,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarOrd::from_syms(db, dom, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Ord(x)
	}

	fn get_bin_x<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		lb: C,
		ub: C,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		let x = IntVarBin::from_bounds(db, lb, ub, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}

	#[test]
	fn constant_test() {
		let c: IntVarEnc<Lit, _> = IntVarEnc::Const(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(6..7), Vec::<Vec<Lit>>::new());
		assert_eq!(c.geq(45..46), vec![vec![]]);
	}

	#[test]
	fn required_bits_test() {
		if GROUND_BINARY_AT_LB {
			assert_eq!(IntVar::<Lit, C>::required_lits(2, 9), 3); // 8 vals => 3 bits
			assert_eq!(IntVar::<Lit, C>::required_lits(2, 10), 4); // 9 vals => 4 bits
			assert_eq!(IntVar::<Lit, C>::required_lits(3, 10), 3); // 8 vals => 3 bits
		} else {
			assert_eq!(IntVar::<Lit, C>::required_lits(2, 9), 4);
			assert_eq!(IntVar::<Lit, C>::required_lits(2, 10), 4);
			assert_eq!(IntVar::<Lit, C>::required_lits(3, 10), 4);

			// neg lb
			assert_eq!(IntVar::<Lit, C>::required_lits(-7, 2), 4); // -7 = 1001 => 4 bits
			assert_eq!(IntVar::<Lit, C>::required_lits(-7, 9), 5); // 9 > 7 => 5 bits
			assert_eq!(IntVar::<Lit, C>::required_lits(2, 9), 4); // 4 b/c no sign bit
		}
	}

	type Lit = i32;
	type C = i32;

	#[test]
	fn bin_as_lin_exp_test() {
		if GROUND_BINARY_AT_LB {
			let mut db = TestDB::new(0);
			let x = get_bin_x::<_, C>(&mut db, 2, 12, true, "x".to_string());
			let x_lin: LinExp<Lit, C> = LinExp::from(&x);

			assert_eq!(x_lin.assign(&[-1, -2, -3, -4]), Ok(2));
			assert_eq!(x_lin.assign(&[1, -2, -3, -4]), Ok(2 + 1));
			assert_eq!(x_lin.assign(&[1, 2, -3, -4]), Ok(2 + 3));
			assert_eq!(x_lin.assign(&[-1, 2, -3, 4]), Ok(2 + 10));
			assert_eq!(
				x_lin.assign(&[1, 2, -3, 4]),
				Err(CheckError::Unsatisfiable(Unsatisfiable)) // 2 + 11 = 13
			);
			assert_eq!(
				x_lin.assign(&[1, 2, 3, 4]),
				Err(CheckError::Unsatisfiable(Unsatisfiable))
			);
		} else {
			let mut db = TestDB::new(0);
			let x = get_bin_x::<_, C>(&mut db, -4, 12, true, "x".to_string());
			let x_lin: LinExp<Lit, C> = LinExp::from(&x);
			assert_eq!(x_lin.assign(&[-1, -2, -3, -4, -5]), Ok(0));
			assert_eq!(x_lin.assign(&[-1, 2, -3, -4, -5]), Ok(2));
			assert_eq!(x_lin.assign(&[1, 2, -3, -4, -5]), Ok(3));
			assert_eq!(x_lin.assign(&[1, -2, 3, -4, -5]), Ok(5));
			assert_eq!(x_lin.assign(&[-1, -2, 3, 4, -5]), Ok(12));
			assert_eq!(
				x_lin.assign(&[1, -2, 3, 4, -5]), // 13
				Err(CheckError::Unsatisfiable(Unsatisfiable))
			);
			assert_eq!(x_lin.assign(&[1, 2, 3, -4, -5]), Ok(7));
			assert_eq!(x_lin.assign(&[-1, -2, 3, 4, 5]), Ok(-4));
		}
	}

	#[test]
	fn bin_1_test() {
		let mut db = TestDB::new(0);
		let x = if GROUND_BINARY_AT_LB {
			get_bin_x::<_, C>(&mut db, 2, 12, true, "x".to_string())
		} else {
			get_bin_x::<_, C>(&mut db, -4, 6, true, "x".to_string())
		};

		if GROUND_BINARY_AT_LB {
			assert_eq!(x.lits(), 4);
			assert_eq!(x.lb(), 2);
			assert_eq!(x.ub(), 12);

			// geq looks zeroes of at (start+1..) end-2 - lb
			assert_eq!(x.geq(3..4), vec![vec![1, 2, 3, 4]]); // 4-2 - 2 = 4 == 0000 (right-to-left!)
			assert_eq!(x.geq(7..8), vec![vec![1, 2, 4]]); // 8-2 - 2 = 4 == 0100
			assert_eq!(x.geq(7..9), vec![vec![1, 2, 4], vec![2, 4]]); // and 9-2 -2 = 5 = 0101
			assert_eq!(x.geq(5..6), vec![vec![1, 3, 4]]); // 6-2 - 2 = 2 == 0010
			assert_eq!(x.geq(6..7), vec![vec![3, 4]]); // 7-2 - 2 = 3 == 0011

			// leq looks at ones at start+1 - lb?
			assert_eq!(x.leq(6..7), vec![vec![-1, -3]]); // 6+1 - 2 = 5 == 0101
			assert_eq!(x.leq(6..8), vec![vec![-1, -3], vec![-2, -3]]); // and 7+1 - 2 = 6 == 0110
			assert_eq!(
				x.leq(6..9),
				vec![vec![-1, -3], vec![-2, -3], vec![-1, -2, -3]]
			); // and 8+1 -2 = 7 == 0111
			assert_eq!(x.leq(5..8), vec![vec![-3], vec![-1, -3], vec![-2, -3]]); // and 5+1 -2 = 4 == 0100

			assert_eq!(x.geq(1..5), vec![vec![1, 2, 3, 4], vec![2, 3, 4]]); // trues and 0000 and 0001
			assert_eq!(x.geq(15..20), vec![vec![1, 2], vec![2], vec![1], vec![]]); // 16-2 - 2 = 12 = 1100, 1101, 1110, false

			assert_eq!(x.leq(-2..3), vec![vec![], vec![-1]]); //
			assert_eq!(x.leq(15..20), vec![vec![-2, -3, -4], vec![-1, -2, -3, -4]]); // 15+1 -2 = 14 = 1110, 1111, true
		} else {
			// TODO
		}

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			cmp: &Comparator::LessEq,
			z: &IntVarEnc::Const(10),
		}; // <= 10

		db.num_var = x.lits() as Lit;

		let sols = db.brute_force_solve(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern => sols);
	}

	#[test]
	fn bin_geq_2_test() {
		let mut db = TestDB::new(0);
		let x = IntVarBin::from_bounds(&mut db, 0, 12, "x".to_string());
		db.num_var = x.lits() as Lit;
		let tern = TernLeConstraint {
			x: &IntVarEnc::Bin(x),
			y: &IntVarEnc::Const(0),
			cmp: &Comparator::LessEq,
			z: &IntVarEnc::Const(6),
		};
		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		vec![-1, -2, -3, -4], // 0
		vec![1, -2, -3, -4], // 1
		vec![-1, 2, -3, -4], // 2
		vec![1, 2, -3, -4], // 3
		vec![-1, -2, 3, -4], // 4
		vec![1, -2, 3, -4], // 5
		vec![-1, 2, 3, -4],// 6
		]);
	}

	#[test]
	fn ord_geq_test() {
		let mut db = TestDB::new(0);
		let x = get_ord_x::<_, C>(
			&mut db,
			interval_set!(3..5, 5..7, 7..11),
			true,
			"x".to_string(),
		);

		assert_eq!(x.lits(), 3);
		assert_eq!(x.lb(), 2);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(6..7), vec![vec![2]]);
		assert_eq!(x.geq(4..7), vec![vec![2]]);

		let x_lin: LinExp<Lit, C> = LinExp::from(&x);
		assert!(x_lin.assign(&[1, -2, 3]).is_err());
		assert!(x_lin.assign(&[-1, 2, -3]).is_err());
		assert_eq!(x_lin.assign(&[-1, -2, -3]), Ok(2));
		assert_eq!(x_lin.assign(&[1, -2, -3]), Ok(4));
		assert_eq!(x_lin.assign(&[1, 2, -3]), Ok(6));
		assert_eq!(x_lin.assign(&[1, 2, 3]), Ok(10));

		let tern = TernLeConstraint {
			x: &x,
			y: &IntVarEnc::Const(0),
			cmp: &Comparator::LessEq,
			z: &IntVarEnc::Const(6),
		};

		db.num_var = x.lits() as Lit;

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3],
		  vec![1, -2, -3],
		  vec![1, 2, -3],
		]);
	}

	#[test]
	fn ord_plus_ord_le_ord_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 2..7), true, "x".to_string()),
			get_ord_x(&mut db, interval_set!(2..3, 3..5), true, "y".to_string()),
			get_ord_x(&mut db, interval_set!(0..4, 4..11), true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		// let sols = db.brute_force_solve(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<Lit, C>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, 5, -6],
		  vec![-1, -2, -3, -4, 5, 6],
		  vec![-1, -2, 3, -4, 5, -6],
		  vec![-1, -2, 3, -4, 5, 6],
		  vec![-1, -2, 3, 4, 5, 6],
		  vec![1, -2, -3, -4, 5, -6],
		  vec![1, -2, -3, -4, 5, 6],
		  vec![1, -2, 3, -4, 5, -6],
		  vec![1, -2, 3, -4, 5, 6],
		  vec![1, -2, 3, 4, 5, 6],
		  vec![1, 2, -3, -4, 5, 6],
		  vec![1, 2, 3, -4, 5, 6],
		  vec![1, 2, 3, 4, 5, 6],
				]);
	}

	#[test]
	fn ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..2, 2..7), true, "x".to_string()),
			// TODO 'gapped' in interval_set:
			// get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
			IntVarEnc::Const(0),
			get_bin_x(&mut db, 0, 7, true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		let sols = db.brute_force_solve(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern => sols


		);
	}

	#[test]
	fn ord_plus_ord_le_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_ord_x(&mut db, interval_set!(1..3), true, "x".to_string()),
			get_ord_x(&mut db, interval_set!(1..4), true, "y".to_string()),
			get_bin_x(&mut db, 0, 6, true, "z".to_string()),
		);
		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		// let sols = db.brute_force_solve(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarOrd<Lit, C>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5],
		  vec![-1, -2, 3, -4, -5],
		  vec![-1, -2, -3, 4, -5],
		  vec![1, -2, -3, 4, -5],
		  vec![-1, -2, 3, 4, -5],
		  vec![1, -2, 3, 4, -5],
		  vec![-1, 2, 3, 4, -5],
		  vec![-1, -2, -3, -4, 5],
		  vec![1, -2, -3, -4, 5],
		  vec![-1, 2, -3, -4, 5],
		  vec![-1, -2, 3, -4, 5],
		  vec![1, -2, 3, -4, 5],
		  vec![-1, 2, 3, -4, 5],
		  vec![1, 2, 3, -4, 5],
		  vec![-1, -2, -3, 4, 5],
		  vec![1, -2, -3, 4, 5],
		  vec![-1, 2, -3, 4, 5],
		  vec![1, 2, -3, 4, 5],
		]);
	}

	#[test]
	fn bin_le_test() {
		let mut db = TestDB::new(0);
		let n = 4;
		let lb = 0;
		let ub = (2i32.pow(n)) - 1;

		let (x, y, z) = (
			get_bin_x(&mut db, lb, ub, true, "x".to_string()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			IntVarEnc::Const(14),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		let sols = db.brute_force_solve(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
					sols
		);
	}

	#[test]
	fn bin_le_bin_test() {
		let mut db = TestDB::new(0);
		let n = 5;
		let lb = 0;
		let ub = (2i32.pow(n)) - 1;

		let (x, y, z) = (
			get_bin_x(&mut db, lb, ub, true, "x".to_string()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			get_bin_x(&mut db, lb, ub, true, "z".to_string()),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		let sols = db.brute_force_solve(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
					sols
		);
	}

	#[test]
	fn bin_plus_bin_le_bin_test() {
		let mut db = TestDB::new(0);
		let n = 2;
		let (x, y, z) = (
			get_bin_x(&mut db, 0, (2i32.pow(n)) - 1, true, "x".to_string()),
			get_bin_x(&mut db, 0, (2i32.pow(n)) - 1, true, "y".to_string()),
			get_bin_x(&mut db, 0, (2i32.pow(n + 1)) - 2, true, "z".to_string()),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		let sols = db.brute_force_solve(|sol| tern.check(sol).is_ok(), db.num_var);

		assert_sol!(db => TernLeEncoder::default(), &tern =>
					sols
		);
	}

	#[test]
	fn bin_plus_bin_eq_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_bin_x(&mut db, 0, 2, true, "x".to_string()),
			get_bin_x(&mut db, 0, 3, true, "y".to_string()),
			get_bin_x(&mut db, 0, 5, true, "z".to_string()),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::Equal,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		// let sols = db.brute_force_solve(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarBin<Lit, C>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5, -6, -7],
		  vec![1, -2, -3, -4, 5, -6, -7],
		  vec![-1, -2, 3, -4, 5, -6, -7],
		  vec![-1, 2, -3, -4, -5, 6, -7],
		  vec![1, -2, 3, -4, -5, 6, -7],
		  vec![-1, -2, -3, 4, -5, 6, -7],
		  vec![-1, 2, 3, -4, 5, 6, -7],
		  vec![1, -2, -3, 4, 5, 6, -7],
		  vec![-1, -2, 3, 4, 5, 6, -7],
		  vec![-1, 2, -3, 4, -5, -6, 7],
		  vec![1, -2, 3, 4, -5, -6, 7],
		  vec![-1, 2, 3, 4, 5, -6, 7],
		]
		);
	}

	// #[test]
	fn _bin_plus_ord_eq_bin_test() {
		let mut db = TestDB::new(0);
		let (x, y, z) = (
			get_bin_x(&mut db, 0, 6, true, String::from("x")),
			get_ord_x(&mut db, interval_set!(1..6), true, String::from("y")),
			get_bin_x(&mut db, 0, 6, true, String::from("z")),
		);

		let tern = TernLeConstraint {
			x: &x,
			y: &y,
			cmp: &Comparator::LessEq,
			z: &z,
		};
		db.num_var = (x.lits() + y.lits() + z.lits()) as Lit;

		// let sols = db.brute_force_solve(
		// 	|sol| {
		// 		tern.check(sol).is_ok()
		// 			&& x.as_any()
		// 				.downcast_ref::<IntVarBin<Lit, C>>()
		// 				.unwrap()
		// 				._consistency()
		// 				.check(sol)
		// 				.is_ok() && y
		// 			.as_any()
		// 			.downcast_ref::<IntVarOrd<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok() && z
		// 			.as_any()
		// 			.downcast_ref::<IntVarBin<Lit, C>>()
		// 			.unwrap()
		// 			._consistency()
		// 			.check(sol)
		// 			.is_ok()
		// 	},
		// 	db.num_var,
		// );

		assert_sol!(db => TernLeEncoder::default(), &tern =>
		vec![
		  vec![-1, -2, -3, -4, -5, -6, -7],
		  vec![-1, -2, -3, -4, 5, -6, -7],
		  vec![1, -2, -3, -4, 5, -6, -7],
		  vec![-1, -2, -3, -4, -5, 6, -7],
		  vec![1, -2, -3, -4, -5, 6, -7],
		  vec![-1, 2, -3, -4, -5, 6, -7],
		  vec![-1, -2, -3, -4, 5, 6, -7],
		  vec![1, -2, -3, -4, 5, 6, -7],
		  vec![-1, 2, -3, -4, 5, 6, -7],
		  vec![1, 2, -3, -4, 5, 6, -7],
		  vec![-1, -2, -3, -4, -5, -6, 7],
		  vec![1, -2, -3, -4, -5, -6, 7],
		  vec![-1, 2, -3, -4, -5, -6, 7],
		  vec![1, 2, -3, -4, -5, -6, 7],
		  vec![-1, -2, 3, -4, -5, -6, 7],
		  vec![-1, -2, -3, -4, 5, -6, 7],
		  vec![1, -2, -3, -4, 5, -6, 7],
		  vec![-1, 2, -3, -4, 5, -6, 7],
		  vec![1, 2, -3, -4, 5, -6, 7],
		  vec![-1, -2, 3, -4, 5, -6, 7],
		  vec![1, -2, 3, -4, 5, -6, 7],
		  vec![-1, -2, -3, 4, 5, -6, 7],
		  vec![-1, -2, -3, -4, -5, 6, 7],
		  vec![1, -2, -3, -4, -5, 6, 7],
		  vec![-1, 2, -3, -4, -5, 6, 7],
		  vec![1, 2, -3, -4, -5, 6, 7],
		  vec![-1, -2, 3, -4, -5, 6, 7],
		  vec![1, -2, 3, -4, -5, 6, 7],
		  vec![-1, 2, 3, -4, -5, 6, 7],
		  vec![-1, -2, -3, 4, -5, 6, 7],
		  vec![1, -2, -3, 4, -5, 6, 7],
		]
		);
	}

	enum IntVarEncoding {
		// Dir,
		Ord,
		Bin,
	}

	fn from_dom<DB: ClauseDatabase, C: Coefficient>(
		db: &mut DB,
		dom: &[C],
		enc: &IntVarEncoding,
		lbl: String,
	) -> IntVarEnc<DB::Lit, C> {
		if dom.len() == 1 {
			IntVarEnc::Const(dom[0])
		} else {
			match enc {
				IntVarEncoding::Ord => IntVarOrd::from_dom(db, dom, lbl).into(),
				IntVarEncoding::Bin => {
					IntVarBin::from_bounds(db, dom[0], dom[dom.len() - 1], lbl).into()
				}
			}
		}
	}
}
