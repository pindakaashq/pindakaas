use crate::int::{helpers::remove_red, model::PRINT_COUPLING};
use std::{
	collections::{HashMap, HashSet},
	path::PathBuf,
};

use itertools::Itertools;

use crate::{
	helpers::{add_clauses_for, as_binary, negate_cnf, unsigned_binary_range},
	linear::{lex_geq_const, lex_leq_const},
	trace::{emit_clause, new_var},
	ClauseDatabase, Cnf, Coefficient, Comparator, Literal, Unsatisfiable,
};

use super::{Dom, LitOrConst};

#[derive(Debug, Clone)]
pub struct BinEnc<Lit: Literal> {
	pub(crate) x: Vec<LitOrConst<Lit>>,
}

impl<Lit: Literal> BinEnc<Lit> {
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		lits: usize,
		_lbl: Option<String>,
	) -> Self {
		let _lbl = _lbl.unwrap_or(String::from("b"));
		Self {
			x: (0..lits)
				.map(|_i| new_var!(db, format!("{_lbl}^{_i}")).into())
				.collect(),
		}
	}

	pub fn from_lits(x: &[LitOrConst<Lit>]) -> Self {
		Self { x: x.to_vec() }
	}

	pub fn two_comp<C: Coefficient>(&self, dom: &Dom<C>) -> Vec<LitOrConst<Lit>> {
		if dom.lb().is_negative() {
			self.x[..self.x.len() - 1]
				.iter()
				.cloned()
				.chain([-self.x.last().unwrap().clone()])
				.collect()
		} else {
			self.x
				.iter()
				.cloned()
				.chain([LitOrConst::Const(false)])
				.collect()
		}
	}

	pub(crate) fn geq_implies<C: Coefficient>(&self, k: C) -> C {
		if k.is_zero() {
			// C::one()
			C::zero()
		} else {
			let zeroes = usize::try_from((k).trailing_zeros()).unwrap();
			C::one().shl(zeroes) - C::one()
		}
	}

	/// Returns conjunction for x>=k, given x>=b
	pub(crate) fn geqs<C: Coefficient>(&self, k: C, a: C) -> Vec<Vec<Lit>> {
		let (range_lb, range_ub) = unsigned_binary_range::<C>(self.bits());

		if k > range_ub {
			vec![]
		} else {
			assert!(k <= a);
			let k = k.clamp(range_lb, range_ub);
			std::iter::successors(Some(k), |&k: &C| {
				let k = k + if k.is_zero() {
					C::one()
				} else {
					C::one().shl(usize::try_from((k).trailing_zeros()).unwrap())
				};
				if k < a {
					Some(k)
				} else {
					None
				}
			})
			.map(|k| {
				as_binary(k.into(), Some(self.bits()))
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

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub(crate) fn geq<C: Coefficient>(&self, k: C) -> Vec<Lit> {
		let (range_lb, range_ub) = unsigned_binary_range::<C>(self.bits());
		if k > range_ub {
			vec![]
		} else {
			let k = k.clamp(range_lb, range_ub);
			as_binary(k.into(), Some(self.bits()))
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
	pub(crate) fn ineqs<C: Coefficient>(&self, r_a: C, r_b: C, up: bool) -> Vec<Vec<Lit>> {
		let (range_lb, range_ub) = unsigned_binary_range::<C>(self.bits());
		if PRINT_COUPLING {
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

		let ineqs = num::iter::range_inclusive(r_a, r_b)
			.map(|k| self.ineq(if up { k - C::one() } else { k }, up))
			.collect_vec();

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
	pub fn ineq<C: Coefficient>(&self, k: C, up: bool) -> Vec<Lit> {
		// assert!(up);
		// if k > range_ub {
		// 	// return vec![];
		// 	return vec![];
		// }
		// let k = k.clamp(range_lb, range_ub);
		as_binary(k.into(), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter().cloned())
			// if >=, find 0's, if <=, find 0's
			// .filter_map(|(b, x)| (b != up).then_some(x))
			.filter_map(|(b, x)| (b != up).then_some(x))
			// if <=, negate lits at 0's
			.map(|x| if up { x } else { -x })
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

	/// Get encoding as unsigned binary representation (if negative dom values, offset by `-2^(k-1)`)
	pub(crate) fn xs(&self) -> Vec<LitOrConst<Lit>> {
		self.x.clone()
	}

	pub fn consistent<DB: ClauseDatabase<Lit = Lit>, C: Coefficient>(
		&self,
		db: &mut DB,
		dom: &Dom<C>,
	) -> crate::Result {
		self.encode_unary_constraint(db, &Comparator::GreaterEq, dom.lb(), dom, true)?;
		self.encode_unary_constraint(db, &Comparator::LessEq, dom.ub(), dom, true)?;
		for (a, b) in dom.ranges.iter().tuple_windows() {
			for k in num::range_inclusive(a.1 + C::one(), b.0 - C::one()) {
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
	pub(crate) fn encode_unary_constraint<DB: ClauseDatabase<Lit = Lit>, C: Coefficient>(
		&self,
		db: &mut DB,
		cmp: &Comparator,
		k: C,
		dom: &Dom<C>,
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
	fn eq<C: Coefficient>(&self, k: C, dom: &Dom<C>) -> Vec<Vec<Lit>> {
		as_binary(self.normalize(k, dom).into(), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter())
			.map(|(b, x)| if b { x.clone() } else { -x.clone() })
			.flat_map(|x| match x {
				LitOrConst::Lit(lit) => Some(Ok(vec![lit])),
				LitOrConst::Const(true) => None,
				LitOrConst::Const(false) => Some(Err(Unsatisfiable)),
			})
			.try_collect()
			.unwrap_or(vec![vec![]])
	}

	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn normalize<C: Coefficient>(&self, k: C, dom: &Dom<C>) -> C {
		k - dom.lb()
	}

	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn denormalize<C: Coefficient>(&self, k: C, dom: &Dom<C>) -> C {
		k + dom.lb()
	}

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "unary", skip_all, fields(constraint = format!("{} != {k}", self)))
	)]
	pub(crate) fn encode_neq<DB: ClauseDatabase<Lit = Lit>, C: Coefficient>(
		&self,
		db: &mut DB,
		k: C,
		dom: &Dom<C>,
	) -> crate::Result {
		add_clauses_for(db, vec![negate_cnf::<Lit>(self.eq(k, dom))])
	}

	pub(crate) fn as_lin_exp<C: Coefficient>(&self) -> (Vec<(Lit, C)>, C) {
		let mut add = C::zero(); // resulting from fixed terms

		(
			self.x
				.iter()
				.enumerate()
				.filter_map(|(k, x)| match x {
					LitOrConst::Lit(l) => Some((l.clone(), C::one().shl(k))),
					LitOrConst::Const(true) => {
						add += C::one().shl(k);
						None
					}
					LitOrConst::Const(false) => None,
				})
				.collect::<Vec<_>>(),
			add,
		)
	}

	pub(crate) fn lits(&self) -> HashSet<Lit> {
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
	pub(crate) fn bits(&self) -> usize {
		self.x.len()
	}

	#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "scm_dnf", skip_all, fields(constraint = format!("DNF:{c}*{self}")))
)]
	pub(crate) fn scm_dnf<DB: ClauseDatabase<Lit = Lit>, C: Coefficient>(
		&self,
		db: &mut DB,
		c: C,
	) -> Result<Self, Unsatisfiable> {
		if c.is_one() {
			return Ok(self.clone());
		}
		// assume shifts; all Const(false) at front
		let bits = self.bits(); // all
		let lits = self.lits().len(); // unfixed
		let xs = self
			.xs()
			.into_iter()
			.skip(bits - lits)
			.map(|x| match x {
				LitOrConst::Lit(x) => x,
				LitOrConst::Const(_) => panic!("Fixed bits not at front in {self}"),
			})
			.collect_vec();

		let cnf = Cnf::<DB::Lit>::from_file(&PathBuf::from(format!(
			"{}/res/ecm/{lits}_{c}.dimacs",
			env!("CARGO_MANIFEST_DIR")
		)))
		.unwrap_or_else(|_| panic!("Could not find Dnf method cnf for {lits}_{c}"));
		// TODO could replace with some arithmetic
		let map = cnf
			.vars()
			.zip_longest(xs.iter())
			.flat_map(|yx| match yx {
				itertools::EitherOrBoth::Both(x, y) => Some((x, y.clone())),
				itertools::EitherOrBoth::Left(x) => {
					// var in CNF but not in x -> new var y
					Some((x.clone(), new_var!(db, format!("scm_{x}"))))
				}
				itertools::EitherOrBoth::Right(_) => unreachable!(), // cnf has at least as many vars as xs
			})
			.collect::<HashMap<_, _>>();

		// add clauses according to Dnf
		cnf.iter().try_for_each(|clause| {
			emit_clause!(
				db,
				&clause
					.iter()
					.map(|x| {
						let lit = &map[&x.var()];
						if x.is_negated() {
							lit.negate()
						} else {
							lit.clone()
						}
					})
					.collect::<Vec<_>>()
			)
		})?;

		let lits = [false]
			.repeat(bits - lits)
			.into_iter()
			.map(LitOrConst::from)
			.chain(map.into_values().sorted().skip(lits).map(LitOrConst::from))
			.collect_vec();
		Ok(BinEnc::from_lits(&lits))
	}
}

impl<Lit: Literal> std::fmt::Display for BinEnc<Lit> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "[{}]", self.x.iter().join(", "))
	}
}

// #[derive(Clone)]
// pub struct OrdEncIterator {
//     i: usize
// }

// impl<'a, Lit: Literal, C: Coefficient> Default for BinEnc<'a, Lit, C> {
// 	fn default() -> Self {
// 		Self { x: Vec::default() }
// 	}
// }

#[cfg(test)]
mod tests {
	// type Lit = i32;

	use super::*;
	use crate::helpers::tests::TestDB;

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
		assert_eq!(x.geqs(1, 6), vec![vec![1], vec![2], vec![3]]);
	}

	#[test]
	fn test_ineq() {
		let mut db = TestDB::new(0);
		let x = BinEnc::new(&mut db, 3, Some(String::from("x")));

		// &x.ineq(false, 2);
		// &negate_cnf(x.ineq(false, 2));
		for (up, ks, expected_lits) in [
			(true, 0, vec![]),
			(true, 1, vec![1]),
			(true, 2, vec![2]),
			(true, 3, vec![1, 2]),
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

	// type C = i32;
	// #[test]
	// fn test_ineqs() {
	// 	let mut db = TestDB::new(0);
	// 	let dom = Dom::from_slice(&[0, 1, 2, 3]);
	// 	let x = BinEnc::new(&mut db, 2, Some(String::from("x")));
	// 	assert_eq!(
	// 		x.ineqs::<C>(true, dom),
	// 		(vec![(0, vec![]), (1, vec![1]), (2, vec![2]), (3, vec![1, 2])])
	// 	);
	// }
}
