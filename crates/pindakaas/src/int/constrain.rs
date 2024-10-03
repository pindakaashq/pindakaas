use std::fmt;

use itertools::Itertools;

use super::{enc::GROUND_BINARY_AT_LB, IntVarBin, IntVarEnc, LitOrConst};
use crate::{
	helpers::{add_clauses_for, as_binary, negate_cnf},
	linear::{
		lex_geq_const, lex_leq_const, log_enc_add, log_enc_add_, LimitComp, LinExp, PosCoeff,
	},
	trace::emit_clause,
	CheckError, Checker, ClauseDatabase, Coeff, Encoder, Unsatisfiable, Valuation,
};

#[derive(Debug)]
pub(crate) struct TernLeConstraint<'a> {
	pub(crate) x: &'a IntVarEnc,
	pub(crate) y: &'a IntVarEnc,
	pub(crate) cmp: LimitComp,
	pub(crate) z: &'a IntVarEnc,
}

impl<'a> TernLeConstraint<'a> {
	pub fn new(x: &'a IntVarEnc, y: &'a IntVarEnc, cmp: LimitComp, z: &'a IntVarEnc) -> Self {
		Self { x, y, cmp, z }
	}

	pub fn is_fixed(&self) -> Result<bool, Unsatisfiable> {
		let TernLeConstraint { x, y, cmp, z } = self;
		if let IntVarEnc::Const(x) = x {
			if let IntVarEnc::Const(y) = y {
				if let IntVarEnc::Const(z) = z {
					return if Self::check(*x, *y, cmp, *z) {
						Ok(true)
					} else {
						Err(Unsatisfiable)
					};
				}
			}
		}
		Ok(false)
	}

	fn check(x: Coeff, y: Coeff, cmp: &LimitComp, z: Coeff) -> bool {
		match cmp {
			LimitComp::LessEq => x + y <= z,
			LimitComp::Equal => x + y == z,
		}
	}
}

impl<'a> Checker for TernLeConstraint<'a> {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<(), CheckError> {
		let x = LinExp::from(self.x).value(sol)?;
		let y = LinExp::from(self.y).value(sol)?;
		let z = LinExp::from(self.z).value(sol)?;
		if Self::check(x, y, &self.cmp, z) {
			Ok(())
		} else {
			Err(CheckError::Fail(format!(
				"Failed constraint {self} since {x}+{y} # {z}"
			)))
		}
	}
}

impl fmt::Display for TernLeConstraint<'_> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{} + {} {} {}", self.x, self.y, self.cmp, self.z)
	}
}

#[derive(Debug, Default)]
pub(crate) struct TernLeEncoder {}

const ENCODE_REDUNDANT_X_O_Y_O_Z_B: bool = true;

impl<'a, DB: ClauseDatabase> Encoder<DB, TernLeConstraint<'a>> for TernLeEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "tern_le_encoder", skip_all, fields(constraint = format!("{} + {} {} {}", tern.x, tern.y, tern.cmp, tern.z)))
	)]
	fn encode(&self, db: &mut DB, tern: &TernLeConstraint) -> crate::Result {
		#[cfg(debug_assertions)]
		{
			const PRINT_TESTCASES: bool = false;
			if PRINT_TESTCASES {
				println!(" // {tern}");
				let x = tern.x.dom().iter(..).map(|iv| iv.end - 1).collect_vec();
				let y = tern.y.dom().iter(..).map(|iv| iv.end - 1).collect_vec();
				let z = tern.z.dom().iter(..).map(|iv| iv.end - 1).collect_vec();
				println!(
					"mod _test_{}_{}_{} {{\n\ttest_int_lin!($encoder, &[{}], &[{}], $cmp, &[{}]);\n}}\n",
					x.iter().join(""),
					y.iter().join(""),
					z.iter().join(""),
					x.iter().join(", "),
					y.iter().join(", "),
					z.iter().join(", "),
				);
			}
		}

		let TernLeConstraint { x, y, cmp, z } = tern;

		return match (x, y, z) {
			(IntVarEnc::Const(_), IntVarEnc::Const(_), IntVarEnc::Const(_)) => {
				if tern.check(&|_| None).is_ok() {
					Ok(())
				} else {
					Err(Unsatisfiable)
				}
			}
			(IntVarEnc::Const(x_con), IntVarEnc::Const(y_con), IntVarEnc::Bin(z_bin)) => {
				let lhs = *x_con + *y_con;
				match cmp {
					// put z_bin on the left, const on the right
					LimitComp::LessEq => lex_geq_const(
						db,
						z_bin.xs.iter().map(|x| Some(*x)).collect_vec().as_slice(),
						PosCoeff::new(if GROUND_BINARY_AT_LB {
							lhs - z_bin.lb()
						} else {
							lhs
						}),
						z_bin.lits(),
					),
					LimitComp::Equal => self.encode(
						db,
						&TernLeConstraint {
							x: z,
							y: &IntVarEnc::Const(0),
							cmp: cmp.clone(),
							z: &IntVarEnc::Const(lhs),
						},
					),
				}
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y_con), IntVarEnc::Const(z_con))
			| (IntVarEnc::Const(y_con), IntVarEnc::Bin(x_bin), IntVarEnc::Const(z_con)) => {
				// and rest is const ~ lex constraint
				// assert!(
				// 	cmp == &LimitComp::LessEq,
				// 	"Only support <= for x:B+y:Constant ? z:Constant"
				// );

				let rhs = PosCoeff::new(if GROUND_BINARY_AT_LB {
					*z_con - *y_con - x_bin.lb()
				} else {
					*z_con - *y_con
				});
				match cmp {
					LimitComp::LessEq => lex_leq_const(
						db,
						x_bin.xs.iter().map(|x| Some(*x)).collect_vec().as_slice(),
						rhs,
						x_bin.lits(),
					),
					LimitComp::Equal => as_binary(rhs, Some(x_bin.lits() as u32))
						.into_iter()
						.zip(x_bin.xs.iter().copied())
						.try_for_each(|(b, x)| emit_clause!(db, [if b { x } else { !x }])),
				}
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(y_const), IntVarEnc::Bin(z_bin))
			| (IntVarEnc::Const(y_const), IntVarEnc::Bin(x_bin), IntVarEnc::Bin(z_bin)) => {
				let x_bin = if matches!(cmp, LimitComp::LessEq) {
					let x_bin = x_bin.add(db, self, *y_const)?;
					x_bin.consistent(db)?;
					x_bin
				} else {
					x_bin.clone()
				};
				log_enc_add_(
					db,
					&x_bin.xs.iter().cloned().map(LitOrConst::from).collect_vec(),
					&as_binary(PosCoeff::new(*y_const), Some(x_bin.lits() as u32))
						.into_iter()
						.map(LitOrConst::Const)
						.collect_vec(),
					cmp,
					&z_bin.xs.iter().cloned().map(LitOrConst::from).collect_vec(),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Bin(y_bin), IntVarEnc::Bin(z_bin)) => {
				// y and z are also bin ~ use adder
				match cmp {
					LimitComp::Equal => log_enc_add(db, &x_bin.xs, &y_bin.xs, cmp, &z_bin.xs),
					LimitComp::LessEq => {
						let xy = x.add(db, self, y, None, Some(z.ub()))?;
						xy.consistent(db)?; // TODO can be removed if grounding is correct
						self.encode(
							db,
							&TernLeConstraint::new(&xy, &IntVarEnc::Const(0), LimitComp::LessEq, z),
						)
					}
				}
			}
			(IntVarEnc::Bin(_), IntVarEnc::Bin(_), _) => {
				// y/y is bin but z is not bin ~ redundantly encode y + z_bin in 0..z # z and z_bin <= z
				// TODO better coupling ;
				let z_bin = x.add(db, self, y, None, Some(z.ub()))?;
				z_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(&z_bin, &IntVarEnc::Const(0), cmp.clone(), z),
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

				self.encode(
					db,
					&TernLeConstraint::new(
						&y_ord.clone().into(),
						&IntVarEnc::Const(0), // TODO maybe - lb
						cmp.clone(),
						&y_bin.clone().into(),
					),
				)
				.unwrap();
				y_bin.consistent(db)?;
				self.encode(
					db,
					&TernLeConstraint::new(&x_bin.clone().into(), &y_bin.into(), cmp.clone(), z),
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
				self.encode(db, &TernLeConstraint::new(x, y, cmp.clone(), &xy_ord))?;

				self.encode(
					db,
					&TernLeConstraint::new(&xy_ord, &IntVarEnc::Const(0), cmp.clone(), z),
				)
			}
			(IntVarEnc::Bin(x_bin), IntVarEnc::Const(c), IntVarEnc::Ord(_))
			| (IntVarEnc::Const(c), IntVarEnc::Bin(x_bin), IntVarEnc::Ord(_)) => {
				let z = z.add(db, self, &IntVarEnc::Const(-c), Some(z.lb()), Some(z.ub()))?;

				// x + c <= z == z-c >= x == /\ (z'<=a -> x<=a)
				for (c_a, z_leq_c_a) in z.leqs() {
					// TODO alt; just propagate by adding lex constraint
					let c_a = if z_leq_c_a.is_empty() {
						c_a.start..(x.ub() + 1)
					} else {
						c_a
					};

					let x_leq_c_a = x_bin.leq(c_a.clone());
					add_clauses_for(db, vec![negate_cnf(z_leq_c_a.clone()), x_leq_c_a])?;
				}
				if cmp == &LimitComp::Equal {
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
				for (c_a, x_geq_c_a) in x.geqs() {
					for (c_b, y_geq_c_b) in y.geqs() {
						// TODO is the max actually correct/good?
						let c_c = (std::cmp::max(c_a.start, c_b.start))
							..(((c_a.end - 1) + (c_b.end - 1)) + 1);

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

				// x<=a /\ y<=b -> z<=a+b
				if cmp == &LimitComp::Equal {
					for (c_a, x_leq_c_a) in x.leqs() {
						for (c_b, y_leq_c_b) in y.leqs() {
							let c_c = (c_a.start + c_b.start)..(c_a.end - 1 + c_b.end - 1) + 1;

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

	use std::num::NonZeroI32;

	use iset::{interval_set, IntervalSet};
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		helpers::tests::{assert_solutions, expect_file, make_valuation},
		int::IntVarOrd,
		solver::VarRange,
		Cnf, Lit, Var,
	};

	fn get_ord_x<DB: ClauseDatabase>(
		db: &mut DB,
		dom: IntervalSet<Coeff>,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc {
		let x = IntVarOrd::from_syms(db, dom, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Ord(x)
	}

	fn get_bin_x<DB: ClauseDatabase>(
		db: &mut DB,
		lb: Coeff,
		ub: Coeff,
		consistent: bool,
		lbl: String,
	) -> IntVarEnc {
		let x = IntVarBin::from_bounds(db, lb, ub, lbl);
		if consistent {
			x.consistent(db).unwrap();
		}
		IntVarEnc::Bin(x)
	}

	#[test]
	fn constant_test() {
		let c: IntVarEnc = IntVarEnc::Const(42);
		assert_eq!(c.lb(), 42);
		assert_eq!(c.ub(), 42);
		assert_eq!(c.geq(6..7), Vec::<Vec<_>>::new());
		assert_eq!(c.geq(45..46), vec![vec![]]);
	}

	#[test]
	fn bin_geq_2_test() {
		let mut cnf = Cnf::default();
		let x = IntVarBin::from_bounds(&mut cnf, 0, 12, "x".to_string());
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &IntVarEnc::Bin(x),
					y: &IntVarEnc::Const(0),
					cmp: LimitComp::LessEq,
					z: &IntVarEnc::Const(6),
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_geq_2_test.sol"],
		);
	}

	#[test]
	fn ord_geq_test() {
		let mut cnf = Cnf::default();
		let x = get_ord_x(
			&mut cnf,
			interval_set!(3..5, 5..7, 7..11),
			true,
			"x".to_string(),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);

		assert_eq!(x.lits(), 3);
		assert_eq!(x.lb(), 2);
		assert_eq!(x.ub(), 10);
		assert_eq!(x.geq(6..7), vec![vec![Lit(NonZeroI32::new(2).unwrap())]]);
		assert_eq!(x.geq(4..7), vec![vec![Lit(NonZeroI32::new(2).unwrap())]]);

		let x_lin = LinExp::from(&x);
		assert!(x_lin.value(&make_valuation(&[1, -2, 3])).is_err());
		assert!(x_lin.value(&make_valuation(&[-1, 2, -3])).is_err());
		assert_eq!(x_lin.value(&make_valuation(&[-1, -2, -3])), Ok(2));
		assert_eq!(x_lin.value(&make_valuation(&[1, -2, -3])), Ok(4));
		assert_eq!(x_lin.value(&make_valuation(&[1, 2, -3])), Ok(6));
		assert_eq!(x_lin.value(&make_valuation(&[1, 2, 3])), Ok(10));

		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &IntVarEnc::Const(0),
					cmp: LimitComp::LessEq,
					z: &IntVarEnc::Const(6),
				},
			)
			.unwrap();
		assert_solutions(&cnf, vars, &expect_file!["int/constrain/ord_geq_test.sol"])
	}

	#[test]
	fn ord_plus_ord_le_ord_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_ord_x(&mut cnf, interval_set!(1..2, 2..7), true, "x".to_string()),
			get_ord_x(&mut cnf, interval_set!(2..3, 3..5), true, "y".to_string()),
			get_ord_x(&mut cnf, interval_set!(0..4, 4..11), true, "z".to_string()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);

		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/ord_plus_ord_le_ord_test.sol"],
		);
	}

	#[test]
	fn ord_le_bin_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_ord_x(&mut cnf, interval_set!(1..2, 2..7), true, "x".to_string()),
			// TODO 'gapped' in interval_set:
			// get_ord_x(&mut db, interval_set!(1..2, 5..7), true, "x".to_string()),
			IntVarEnc::Const(0),
			get_bin_x(&mut cnf, 0, 7, true, "z".to_string()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/ord_le_bin_test.sol"],
		);
	}

	#[test]
	fn ord_plus_ord_le_bin_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_ord_x(&mut cnf, interval_set!(1..3), true, "x".to_string()),
			get_ord_x(&mut cnf, interval_set!(1..4), true, "y".to_string()),
			get_bin_x(&mut cnf, 0, 6, true, "z".to_string()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/ord_plus_ord_le_bin_test.sol"],
		);
	}

	#[test]
	fn bin_le_test() {
		let mut cnf = Cnf::default();
		let n = 4;
		let lb = 0;
		let ub = ((2i32.pow(n)) - 1) as Coeff;

		let (x, y, z) = (
			get_bin_x(&mut cnf, lb, ub, true, "x".to_string()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			IntVarEnc::Const(14),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					// cmp: LimitComp::Equal,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(&cnf, vars, &expect_file!["int/constrain/bin_le_test.sol"]);
	}

	#[test]
	fn bin_le_bin_test() {
		let mut cnf = Cnf::default();
		let n = 5;
		let lb = 0;
		let ub = ((2i32.pow(n)) - 1) as Coeff;

		let (x, y, z) = (
			get_bin_x(&mut cnf, lb, ub, true, "x".to_string()),
			IntVarEnc::Const(0),
			// get_bin_x(&mut db, (2i32.pow(n)) - 1, true, "y".to_string()),
			get_bin_x(&mut cnf, lb, ub, true, "z".to_string()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					// cmp: LimitComp::Equal,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_le_bin_test.sol"],
		);
	}

	#[test]
	fn bin_plus_bin_le_bin_test() {
		let mut cnf = Cnf::default();
		let n = 2;
		let (x, y, z) = (
			get_bin_x(
				&mut cnf,
				0,
				((2i32.pow(n)) - 1) as Coeff,
				true,
				"x".to_string(),
			),
			get_bin_x(
				&mut cnf,
				0,
				((2i32.pow(n)) - 1) as Coeff,
				true,
				"y".to_string(),
			),
			get_bin_x(
				&mut cnf,
				0,
				((2i32.pow(n + 1)) - 2) as Coeff,
				true,
				"z".to_string(),
			),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::LessEq,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_plus_bin_le_bin_test.sol"],
		);
	}

	#[test]
	fn bin_plus_bin_eq_bin_test() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			get_bin_x(&mut cnf, 0, 2, true, "x".to_string()),
			get_bin_x(&mut cnf, 0, 3, true, "y".to_string()),
			get_bin_x(&mut cnf, 0, 5, true, "z".to_string()),
		);
		let vars = VarRange::new(
			Var(NonZeroI32::new(1).unwrap()),
			cnf.nvar.next_var.unwrap().prev_var().unwrap(),
		);
		TernLeEncoder::default()
			.encode(
				&mut cnf,
				&TernLeConstraint {
					x: &x,
					y: &y,
					cmp: LimitComp::Equal,
					z: &z,
				},
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vars,
			&expect_file!["int/constrain/bin_plus_bin_eq_bin_test.sol"],
		);
	}
}
