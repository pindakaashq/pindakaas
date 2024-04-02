use std::collections::HashSet;

use itertools::Itertools;

use crate::{
	helpers::{add_clauses_for, as_binary, negate_cnf, two_comp_bounds, unsigned_binary_range},
	linear::{lex_geq_const, lex_leq_const},
	trace::new_var,
	ClauseDatabase, Coefficient, Comparator, Literal, Unsatisfiable,
};

use super::{enc::GROUND_BINARY_AT_LB, Dom, LitOrConst};

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

	/// Returns conjunction for x>=k (or x<=k if !up)
	pub fn ineq<C: Coefficient>(&self, up: bool, k: C) -> Vec<Vec<Lit>> {
		as_binary(k.into(), Some(self.bits()))
			.into_iter()
			.zip(self.xs().iter().cloned())
			// if >=, find 1's, if <=, find 0's
			.filter_map(|(b, x)| (b == up).then_some(x))
			// if <=, negate lits at 0's
			.map(|x| if up { x } else { -x })
			.filter_map(|x| match x {
				// THIS IS A CONJUNCTION
				// TODO make this a bit more clear (maybe simplify function for Cnf)
				LitOrConst::Lit(x) => Some(Ok(vec![x])),
				LitOrConst::Const(true) => None, // literal satisfied
				LitOrConst::Const(false) => Some(Err(Unsatisfiable)), // clause falsified
			})
			.try_collect()
			.unwrap_or(vec![vec![]])
	}

	/// Return (k,x>=k) for all k in dom (or x<=k if !up) where each x>=k is a conjunction
	pub fn ineqs<C: Coefficient>(&self, up: bool, dom: Dom<C>) -> Vec<(C, Vec<Vec<Lit>>, bool)> {
		assert!(
			{
				let r = unsigned_binary_range::<C>(self.bits());
				dom.is_empty() || (dom.lb() >= r.0 && dom.ub() <= r.1)
			},
			"Cannot call BinEnc::ineqs({dom}) on {self}"
		);

		let dom = if dom.is_empty() {
			return vec![];
		} else {
			// TODO for now, go through bounds, which creates redundant entries
			num::iter::range_inclusive(dom.lb(), dom.ub())
		}
		.collect_vec();

		// get all conjunctions for every value in the given range
		let ks = if up {
			let range_lb = *dom.first().unwrap();
			std::iter::once(range_lb - C::one())
				.chain(dom.iter().cloned())
				.collect_vec()
		} else {
			let range_ub = *dom.last().unwrap();
			dom.iter()
				.cloned()
				.chain(std::iter::once(range_ub + C::one()))
				.rev()
				.collect_vec()
		};

		ks.into_iter()
			.tuple_windows()
			.map(|(a, b)| {
				// for two dom elements {..,a,b,..}, return (b, x>=a+1)
				if up {
					(b, self.ineq(up, a + C::one()))
				} else {
					(b, self.ineq(up, a - C::one()))
					// old (before reverse): (a, self.ineq(up, b - C::one()))
				}
			})
			.map(|(k, cnf)| {
				(
					k,
					cnf,
					// powers of two imply all subsequent k's until next power of two
					{
						let k = if up {
							k
						} else {
							unsigned_binary_range::<C>(self.bits()).1 - k
						};

						!(k.is_zero() || k.is_one() || k.trailing_zeros() > 0)
					},
				)
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
	fn test_ineq() {
		let mut db = TestDB::new(0);
		let x = BinEnc::new(&mut db, 3, Some(String::from("x")));

		// &x.ineq(false, 2);
		// &negate_cnf(x.ineq(false, 2));
		for (up, ks, expected_cnf) in [
			(true, 0, vec![]),
			(true, 1, vec![vec![1]]),
			(true, 2, vec![vec![2]]),
			(true, 3, vec![vec![1], vec![2]]),
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
				x.ineq(up, ks),
				expected_cnf,
				"ks {ks:?} with up {up} was expected to return {expected_cnf:?}"
			);
		}
	}

	type C = i32;
	#[test]
	fn test_ineqs() {
		let mut db = TestDB::new(0);
		let dom = Dom::from_slice(&[0, 1, 2, 3]);
		let x = BinEnc::new(&mut db, 2, Some(String::from("x")));
		// dbg!(x.ineqs::<C>(true, dom));
		dbg!(x.ineqs::<C>(false, dom));
		// assert_eq!(
		// 	x.ineqs::<C>(true, &dom),
		// 	vec![vec![], vec![vec![1]], vec![vec![2]], vec![vec![1], vec![2]]]
		// );
	}
}
