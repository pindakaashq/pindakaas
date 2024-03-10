#![allow(dead_code)]

use std::collections::HashSet;

use itertools::Itertools;

use crate::{
	helpers::{as_binary, two_comp_bounds, unsigned_binary_range},
	linear::{lex_geq_const, lex_leq_const},
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Comparator, Literal, Unsatisfiable,
};

use super::{enc::GROUND_BINARY_AT_LB, Dom, LitOrConst};

#[derive(Debug, Clone)]
pub(crate) struct BinEnc<Lit: Literal> {
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

	pub fn ineqs<C: Coefficient>(
		&self,
		up: bool,
		(range_lb, range_ub): (C, C),
	) -> Vec<(C, Vec<Vec<Lit>>)> {
		let range = if up {
			// also omit first 'hard-coded' x>=lb() == true literal
			(range_lb + C::one(), range_ub)
		} else {
			// same for x<=ub() == true
			(range_lb, range_ub - C::one())
		};

		assert!({
			let r = unsigned_binary_range::<C>(self.bits());
			range.0 >= r.0 && range.1 <= r.1
		});
		// get all conjunctions for every term's domain value
		let xs = num::iter::range_inclusive(range.0, range.1).flat_map(|k| {
			as_binary(k.into(), Some(self.bits()))
				.into_iter()
				.zip(self.xs().iter().cloned())
				// if >=, find 1's, if <=, find 0's
				.filter_map(|(b, x)| (b == up).then_some(x))
				// if <=, negate 1's to not 1's
				.map(|x| if up { x } else { -x })
				.filter_map(|x| match x {
					// THIS IS A CONJUNCTION
					// TODO make this a bit more clear (maybe simplify function for Cnf)
					LitOrConst::Lit(x) => Some(Ok(vec![x])),
					LitOrConst::Const(true) => None,           // literal satisfied
					LitOrConst::Const(false) => Some(Err(())), // clause falsified
				})
				.try_collect()
				.map(|cnf| (k, cnf))
		});

		// hard-code first (or last) fixed term bound literal
		if up {
			[(range_lb, vec![])].into_iter().chain(xs).collect()
		} else {
			xs.chain([(range_ub, vec![])]).collect()
		}
	}

	// pub fn from_lits(x: &[Lit]) -> Self {
	// todo!();
	// 	Self {
	// 		x: x.iter().cloned().map(LitOrConst::from).collect(),
	// 	}
	// }

	// TODO think about whether we need this old version. The new version probably does not account for gaps?
	/*
	// pub fn iter(&self) -> impl Iterator<Item = Vec<Lit>> {
	pub fn ineqs<C: Coefficient>(&self, up: bool, dom: &Dom<C>) -> Vec<Vec<Vec<Lit>>> {
		// TODO exchange for dom bounds
		if up {
			[vec![]]
				.into_iter()
				.chain(
					num::iter::range_inclusive(
						C::zero(),
						unsigned_binary_range_ub::<C>(self.bits()).unwrap(),
					)
					.map(|k| self.normalize(k, dom))
					.map(|k| self.ineq((k, k + C::one()), up)),
					// .map(|k| self.ineq((C::zero(), k + C::one()), up)),
				)
				.collect()
		} else {
			// let range_ub = unsigned_binary_range_ub::<C>(self.bits()).unwrap();
			num::iter::range_inclusive(
				C::one(),
				unsigned_binary_range_ub::<C>(self.bits()).unwrap(),
			)
			.map(|k| self.normalize(k, dom))
			.map(|k| self.ineq((k - C::one(), k), up))
			// .map(|k| self.ineq((k - C::one(), range_ub), up))
			.chain([vec![]])
			.collect()
		}
		// TODO should be able to call ineq(0..2^bits)
		// if up {
		// 	[vec![]]
		// 		.into_iter()
		// 		.chain(self.x.iter().map(|x| vec![vec![x.clone()]]))
		// 		.collect()
		// } else {
		// 	self.x
		// 		.iter()
		// 		.map(|x| vec![vec![x.negate()]])
		// 		.chain([vec![]])
		// 		.collect()
		// }
	}
	*/

	/// Return cnf constraining cnf>=ks.1 assuming x>=ks.0 (or cnf<=ks.0 assuming x<=ks.1)
	pub(crate) fn ineq<C: Coefficient>(&self, ks: (C, C), up: bool) -> Vec<Vec<Lit>> {
		// Go through x>=k.0+1..k.1 (or x<=k.0..k.1-1)
		// (We don't constrain x>=k.0 of course)
		// Do not constrain <lb (or >ub)
		let (range_lb, range_ub) = unsigned_binary_range::<C>(self.bits());
		let ks = if up {
			(
				std::cmp::max(range_lb + C::one(), ks.0 + C::one()),
				std::cmp::min(ks.1, range_ub + C::one()),
			)
		} else {
			(
				std::cmp::max(range_lb - C::one(), ks.0),
				std::cmp::min(range_ub - C::one(), ks.1 - C::one()),
			)
		};
		num::iter::range_inclusive(ks.0, ks.1)
			.filter_map(|v| {
				// x>=v == x>v-1 (or x<=v == x<v+1)
				let v = if up { v - C::one() } else { v + C::one() };

				as_binary(v.into(), Some(self.bits()))
					.into_iter()
					.zip(self.x.iter().cloned())
					// if >=, find 0's, if <=, find 1's
					.filter_map(|(b, x)| (b != up).then_some(x))
					// if <=, negate 1's to not 1's
					.map(|x| if up { x } else { -x })
					// filter out fixed literals (possibly satisfying clause)
					.filter_map(|x| match x {
						LitOrConst::Lit(x) => Some(Ok(x)),
						LitOrConst::Const(true) => Some(Err(())), // clause satisfied
						LitOrConst::Const(false) => None,         // literal falsified
					})
					.collect::<Result<Vec<_>, _>>()
					.ok()
			})
			.collect()
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

	fn has_sign_bit<C: Coefficient>(dom: &Dom<C>) -> bool {
		dom.lb().is_negative()
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
			Comparator::Equal => self
				.eq(k, dom)?
				.into_iter()
				.try_for_each(|cls| emit_clause!(db, &[cls])),
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
	fn eq<C: Coefficient>(&self, k: C, dom: &Dom<C>) -> Result<Vec<Lit>, Unsatisfiable> {
		as_binary(self.normalize(k, dom).into(), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter())
			.map(|(b, x)| if b { x.clone() } else { -x.clone() })
			.flat_map(|x| match x {
				LitOrConst::Lit(lit) => Some(Ok(lit)),
				LitOrConst::Const(true) => None,
				LitOrConst::Const(false) => Some(Err(Unsatisfiable)),
			})
			.collect()
	}

	/// Normalize k to its value in unsigned binary relative to this encoding
	pub(crate) fn normalize<C: Coefficient>(&self, k: C, dom: &Dom<C>) -> C {
		if GROUND_BINARY_AT_LB {
			k - dom.lb()
		} else {
			// encoding is grounded at the lb of the two comp representation
			// (this increases k by subtracting the (negative) lower bound)
			if Self::has_sign_bit(dom) {
				k.checked_sub(&two_comp_bounds::<C>(self.bits()).0).unwrap()
			} else {
				k
			}
		}
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
		emit_clause!(
			db,
			&self.eq(k, dom)?.iter().map(Lit::negate).collect::<Vec<_>>()
		)
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
	// type C = i32;

	use super::*;
	use crate::helpers::tests::TestDB;

	#[test]
	fn test_ineq() {
		let mut db = TestDB::new(0);
		let x = BinEnc::new(&mut db, 4, Some(String::from("x")));

		for (up, ks, expected_cnf) in [
			(true, (0, 1), vec![vec![1, 2, 3, 4]]),
			(
				true,
				(0, 3),
				vec![vec![1, 2, 3, 4], vec![2, 3, 4], vec![1, 3, 4]],
			),
			(true, (14, 17), vec![vec![1], vec![]]),
			(true, (0, 0), vec![]),
			(false, (15, 16), vec![]),
		] {
			assert_eq!(
				x.ineq(ks, up),
				expected_cnf,
				"ks {ks:?} with up {up} was expected to return {expected_cnf:?}"
			);
		}
	}

	// #[test]
	// fn test_ineqs() {
	// 	let mut db = TestDB::new(0);
	// 	let dom = Dom::from_slice(&[0, 1, 2, 3]);
	// 	let x = BinEnc::new(&mut db, 2, Some(String::from("x")));
	// 	assert_eq!(
	// 		x.ineqs::<C>(true, &dom),
	// 		vec![vec![], vec![vec![1]], vec![vec![2]], vec![vec![1], vec![2]]]
	// 	);
	// }
}
