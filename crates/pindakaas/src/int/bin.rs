#![allow(clippy::absurd_extreme_comparisons)]
use std::{
	collections::{HashMap, HashSet},
	path::PathBuf,
};

use itertools::Itertools;

use super::{required_lits, Dom, LitOrConst};
use crate::{
	helpers::{add_clauses_for, as_binary, negate_cnf, pow2, unsigned_binary_range},
	int::{helpers::remove_red, model::PRINT_COUPLING},
	linear::{lex_geq_const, lex_leq_const, PosCoeff},
	trace::{emit_clause, new_var},
	ClauseDatabase, Cnf, Coeff, Comparator, Lit, Unsatisfiable, Var,
};

#[derive(Debug, Clone)]
pub struct BinEnc {
	pub(crate) x: Vec<LitOrConst>,
}

impl BinEnc {
	pub fn new<DB: ClauseDatabase>(db: &mut DB, lits: u32, _lbl: Option<String>) -> Self {
		let _lbl = _lbl.unwrap_or(String::from("b"));
		Self {
			x: (0..lits)
				.map(|_i| new_var!(db, format!("{_lbl}^{_i}")).into())
				.collect(),
		}
	}

	pub(crate) fn from_lits(x: &[LitOrConst]) -> Self {
		Self { x: x.to_vec() }
	}

	pub(crate) fn geq_implies(&self, k: Coeff) -> Coeff {
		if k == 0 {
			0
		} else {
			pow2(k.trailing_zeros()) - 1
		}
	}

	/// Returns conjunction for x>=k, given x>=b
	pub(crate) fn geqs(&self, k: Coeff, a: Coeff) -> Vec<Vec<Lit>> {
		let (range_lb, range_ub) = self.range();

		if k > range_ub {
			vec![]
		} else {
			assert!(k <= a);
			let k = k.clamp(range_lb, range_ub);
			std::iter::successors(Some(k), |k: &Coeff| {
				let k = k + if k == &0 { 1 } else { pow2(k.trailing_zeros()) };
				if k < a {
					Some(k)
				} else {
					None
				}
			})
			.map(|k| {
				as_binary(PosCoeff::new(k), Some(self.bits()))
					.iter()
					.zip(self.xs().iter().cloned())
					// if >=, find 1's, if <=, find 0's
					.filter_map(|(b, x)| b.then_some(x))
					.filter_map(|x| match x {
						// THIS IS A CONJUNCTION
						// TODO make this a bit more clear (maybe simplify function for Cnf)
						LitOrConst::Lit(x) => Some(Ok(x)),
						LitOrConst::Const(true) => None, // literal satisfied
						LitOrConst::Const(false) => Some(Err(Unsatisfiable)), // clause falsified
					})
					.try_collect()
					.unwrap_or_default()
			})
			.collect()
		}
	}

	/// The encoding range
	pub(crate) fn range(&self) -> (Coeff, Coeff) {
		let (range_lb, range_ub) = unsigned_binary_range(self.bits());
		let (range_lb, range_ub) = (*range_lb, *range_ub); // TODO [?] replace all Coeff for PosCoeff in bin.rs
		(range_lb, range_ub)
	}

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub(crate) fn geq(&self, k: Coeff) -> Vec<Lit> {
		let (range_lb, range_ub) = self.range();
		if k > range_ub {
			vec![]
		} else {
			let k = k.clamp(range_lb, range_ub);
			as_binary(PosCoeff::new(k), Some(self.bits()))
				.into_iter()
				.zip(self.xs().iter().cloned())
				// if >=, find 1's, if <=, find 0's
				.filter_map(|(b, x)| b.then_some(x))
				.filter_map(|x| match x {
					// THIS IS A CONJUNCTION
					// TODO make this a bit more clear (maybe simplify function for Cnf)
					LitOrConst::Lit(x) => Some(Ok(x)),
					LitOrConst::Const(true) => None, // literal satisfied
					LitOrConst::Const(false) => Some(Err(Unsatisfiable)), // clause falsified
				})
				.try_collect()
				.unwrap_or_default()
		}
	}

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub(crate) fn ineqs(&self, r_a: Coeff, r_b: Coeff, up: bool) -> Vec<Vec<Lit>> {
		let (range_lb, range_ub) = self.range();
		if PRINT_COUPLING >= 2 {
			print!("\t {up} {r_a}..{r_b} [{range_lb}..{range_ub}] -> ");
		}

		if r_a <= range_lb {
			if up {
				return vec![];
			} else {
				return vec![vec![]];
			}
		}

		if r_b > range_ub {
			if up {
				return vec![vec![]];
			} else {
				return vec![];
			}
		}

		let ineqs = (r_a..=r_b)
			.flat_map(|k| {
				let k = if up { k - 1 } else { k };
				let ineq = self.ineq(k, up); // returns cnf
				if PRINT_COUPLING >= 2 {
					println!("{k} -> ineq = {:?}", ineq);
				}
				ineq
			})
			.collect_vec();

		// // Returning CNF; so a single empty clause
		if ineqs == vec![vec![]] {
			return vec![];
		}

		let ineqs = if up {
			ineqs
		} else {
			ineqs.into_iter().rev().collect()
		};

		if up {
			remove_red(ineqs.into_iter().rev().collect())
				.into_iter()
				.rev()
				.collect_vec()
		} else {
			remove_red(ineqs.into_iter().rev().collect())
		}
	}

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub fn ineq(&self, k: Coeff, up: bool) -> Vec<Vec<Lit>> {
		let clause: Result<Vec<_>, _> = as_binary(PosCoeff::new(k), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter().cloned())
			// if >=, find 0's, if <=, find 0's
			// .filter_map(|(b, x)| (b != up).then_some(x))
			.filter_map(|(b, x)| (b != up).then_some(x))
			// if <=, negate lits at 0's
			.map(|x| if up { x } else { !x })
			.filter_map(|x| match x {
				// This is a DISJUNCTION
				LitOrConst::Lit(x) => Some(Ok(x)),
				LitOrConst::Const(false) => None, // literal falsified
				LitOrConst::Const(true) => Some(Err(Unsatisfiable)), // clause satisfied
			})
			.try_collect();

		match clause {
			Err(Unsatisfiable) => vec![],
			Ok(clause) if clause.is_empty() => vec![],
			Ok(clause) => vec![clause],
		}
	}

	/// Get encoding as unsigned binary representation (if negative dom values, offset by `-2^(k-1)`)
	pub(crate) fn xs(&self) -> Vec<LitOrConst> {
		self.x.clone()
	}

	pub fn consistent<DB: ClauseDatabase>(&self, db: &mut DB, dom: &Dom) -> crate::Result {
		self.encode_unary_constraint(db, &Comparator::GreaterEq, dom.lb(), dom, true)?;
		self.encode_unary_constraint(db, &Comparator::LessEq, dom.ub(), dom, true)?;
		for (a, b) in dom.ranges.iter().tuple_windows() {
			for k in (a.1 + 1)..=(b.0 - 1) {
				self.encode_neq(db, k, dom)?;
			}
		}
		Ok(())
	}

	/// Encode `x # k` where `# ∈ {≤,=,≥}`
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "unary", skip_all, fields(constraint = format!("{} {cmp} {k}", self)))
	)]
	pub(crate) fn encode_unary_constraint<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		cmp: &Comparator,
		k: Coeff,
		dom: &Dom,
		force: bool,
	) -> crate::Result {
		match cmp {
			Comparator::LessEq => {
				if k < dom.lb() {
					Err(Unsatisfiable)
				} else if k >= dom.ub() && !force {
					Ok(())
				} else {
					lex_leq_const(db, &self.xs(), self.normalize(k, dom), self.bits())
				}
			}
			Comparator::Equal => add_clauses_for(db, vec![self.eq(k, dom)]),
			Comparator::GreaterEq => {
				if k > dom.ub() {
					Err(Unsatisfiable)
				} else if k <= dom.lb() && !force {
					Ok(())
				} else {
					lex_geq_const(db, &self.xs(), self.normalize(k, dom), self.bits())
				}
			}
		}
	}

	/// Return conjunction of bits equivalent where `x=k`
	fn eq(&self, k: Coeff, dom: &Dom) -> Vec<Vec<Lit>> {
		as_binary(self.normalize(k, dom), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter())
			.map(|(b, x)| if b { *x } else { !*x })
			.flat_map(|x| match x {
				LitOrConst::Lit(lit) => Some(Ok(vec![lit])),
				LitOrConst::Const(true) => None,
				LitOrConst::Const(false) => Some(Err(Unsatisfiable)),
			})
			.try_collect()
			.unwrap_or(vec![vec![]])
	}

	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn normalize(&self, k: Coeff, dom: &Dom) -> PosCoeff {
		PosCoeff::new(k - dom.lb())
	}

	// TODO Coeff -> PosCoeff
	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn denormalize(&self, k: Coeff, dom: &Dom) -> Coeff {
		k + dom.lb()
	}

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "unary", skip_all, fields(constraint = format!("{} != {k}", self)))
	)]
	pub(crate) fn encode_neq<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		k: Coeff,
		dom: &Dom,
	) -> crate::Result {
		add_clauses_for(db, vec![negate_cnf(self.eq(k, dom))])
	}

	pub(crate) fn as_lin_exp(&self) -> (Vec<(Lit, Coeff)>, Coeff) {
		let mut add = 0; // resulting from fixed terms

		(
			self.x
				.iter()
				.enumerate()
				.filter_map(|(k, x)| {
					let a = pow2(k as u32);

					match x {
						LitOrConst::Lit(l) => Some((*l, a)),
						LitOrConst::Const(true) => {
							add += a;
							None
						}
						LitOrConst::Const(false) => None,
					}
				})
				.collect::<Vec<_>>(),
			add,
		)
	}

	pub(crate) fn lits(&self) -> HashSet<Var> {
		self.x
			.clone()
			.into_iter()
			.filter_map(|x| match x {
				LitOrConst::Lit(x) => Some(x.var()),
				LitOrConst::Const(_) => None,
			})
			.collect()
	}

	/// Number of bits in the encoding
	pub(crate) fn bits(&self) -> u32 {
		self.x.len() as u32
	}

	#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "scm_dnf", skip_all, fields(constraint = format!("DNF:{c}*{self}")))
)]
	pub(crate) fn scm_dnf<DB: ClauseDatabase>(
		&self,
		db: &mut DB,
		c: Coeff,
	) -> Result<Self, Unsatisfiable> {
		if c == 1 {
			return Ok(self.clone());
		}
		// assume shifts; all Const(false) at front
		let bits = self.bits(); // all
		let lits = self.lits().len() as u32; // unfixed
		let xs = self
			.xs()
			.into_iter()
			.skip(usize::try_from(bits - lits).unwrap())
			.map(|x| match x {
				LitOrConst::Lit(x) => x,
				LitOrConst::Const(_) => panic!("Fixed bits not at front in {self}"),
			})
			.collect_vec();

		// TODO [!] remove reading
		let cnf = Cnf::from_file(&PathBuf::from(format!(
			"{}/res/ecm/{lits}_{c}.dimacs",
			env!("CARGO_MANIFEST_DIR")
		)))
		.unwrap_or_else(|_| panic!("Could not find Dnf method cnf for {lits}_{c}"));
		// TODO could replace with some arithmetic
		let map = cnf
			.vars()
			.zip_longest(xs.iter())
			.flat_map(|yx| match yx {
				itertools::EitherOrBoth::Both(x, y) => Some((x, *y)),
				itertools::EitherOrBoth::Left(x) => {
					// var in CNF but not in x -> new var y
					Some((x, new_var!(db, format!("scm_{x}"))))
				}
				itertools::EitherOrBoth::Right(_) => unreachable!(), // cnf has at least as many vars as xs
			})
			.collect::<HashMap<_, _>>();

		// add clauses according to Dnf
		cnf.iter().try_for_each(|clause| {
			emit_clause!(
				db,
				clause
					.iter()
					.map(|x| {
						let lit = map[&x.var()];
						if x.is_negated() {
							!lit
						} else {
							lit
						}
					})
					.collect::<Vec<_>>()
			)
		})?;

		let lits = [false]
			.repeat((bits - lits) as usize)
			.into_iter()
			.map(LitOrConst::from)
			.chain(
				map.into_values()
					.sorted()
					.skip(lits as usize)
					.map(LitOrConst::from),
			)
			.collect_vec();
		Ok(BinEnc::from_lits(&lits))
	}

	pub(crate) fn required_lits(dom: &Dom) -> u32 {
		required_lits(dom.lb(), dom.ub())
	}
}

impl std::fmt::Display for BinEnc {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "[{}]", self.x.iter().rev().join(", "))
	}
}

#[cfg(test)]
mod tests {
	// type Lit = i32;

	use super::*;
	use crate::helpers::tests::{lits, TestDB};

	// #[test]
	// fn test_ineqs() {
	// 	let mut db = TestDB::new(0);
	// 	let x_ = BinEnc::new(&mut db, 3, Some(String::from("x")));
	// 	// &x.ineqs(true, Dom::from_slice(&[0, 2, 3, 5]));
	// 	// panic!();
	// }

	#[test]
	fn test_geqs() {
		let mut db = TestDB::new(0);
		let x = BinEnc::new(&mut db, 3, Some(String::from("x")));
		assert_eq!(x.geqs(1, 6), vec![lits![1], lits![2], lits![3]]);
	}

	#[test]
	fn test_ineq() {
		let mut db = TestDB::new(0);
		let x = BinEnc::new(&mut db, 3, Some(String::from("x")));

		// &x.ineq(false, 2);
		// &negate_cnf(x.ineq(false, 2));
		for (up, ks, expected_lits) in [
			(true, 0, lits![]),
			(true, 1, lits![1]),
			(true, 2, lits![2]),
			(true, 3, lits![1, 2]),
			// (
			// 	true,
			// 	(0, 3),
			// 	vec![vec![1, 2, 3, 4], vec![2, 3, 4], vec![1, 3, 4]],
			// ),
			// (true, (14, 17), vec![vec![1], vec![]]),
			// (true, (0, 0), vec![]),
			// (false, (15, 16), vec![]),
		] {
			assert_eq!(
				x.geq(ks),
				expected_lits,
				"ks {ks:?} with up {up} was expected to return {expected_lits:?}"
			);
		}
	}

	// #[test]
	// fn test_ineqs() {
	// 	let mut db = TestDB::new(0);
	// 	let dom = Dom::from_slice(&[0, 1, 2, 3]);
	// 	let x = BinEnc::new(&mut db, 2, Some(String::from("x")));
	// 	assert_eq!(
	// 		x.ineqs(true, dom),
	// 		(vec![(0, vec![]), (1, vec![1]), (2, vec![2]), (3, vec![1, 2])])
	// 	);
	// }
}
