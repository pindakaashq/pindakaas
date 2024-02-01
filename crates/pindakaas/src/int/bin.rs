use itertools::Itertools;

use crate::{
	helpers::{as_binary, two_comp_bounds},
	linear::{lex_geq_const, lex_leq_const},
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Comparator, Literal, Unsatisfiable,
};

use super::{enc::GROUND_BINARY_AT_LB, required_lits, Dom, LitOrConst};

#[derive(Debug, Clone)]
pub(crate) struct BinEnc<Lit: Literal> {
	x: Vec<LitOrConst<Lit>>,
}

impl<Lit: Literal> BinEnc<Lit> {
	pub fn new<DB: ClauseDatabase<Lit = Lit>, C: Coefficient>(db: &mut DB, dom: &Dom<C>) -> Self {
		let (lb, ub) = (dom.lb(), dom.ub());
		Self {
			x: (0..required_lits(lb, ub))
				.map(|_i| (new_var!(db, format!("b^{}", _i))).into())
				.chain(
					(!GROUND_BINARY_AT_LB && !lb.is_negative()).then_some(LitOrConst::Const(false)),
				)
				.collect(),
		}
	}

	// pub fn from_lits(x: &[Lit]) -> Self {
	// todo!();
	// 	Self {
	// 		x: x.iter().cloned().map(LitOrConst::from).collect(),
	// 	}
	// }

	// pub fn iter(&self) -> impl Iterator<Item = Vec<Lit>> {
	pub fn ineqs(&self, up: bool) -> Vec<Vec<Vec<Lit>>> {
		todo!();
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

	/// From range to cnf>=k.1 assuming x>=k.0 (or cnf<=k.0)
	pub(crate) fn ineq<C: Coefficient>(&self, k: (C, C), geq: bool) -> Vec<Vec<Lit>> {
		assert!(geq);
		num::iter::range_inclusive(k.0, k.1 - C::one())
			.filter_map(|v| {

				as_binary(v.into(), Some(self.bits()))
					.into_iter()
					.zip(self.xs(true))
					// if >=, find 0's, if <=, find 1's
					.filter_map(|(b, x)| (b != geq).then_some(x))
					// if <=, negate 1's to not 1's
					.map(|x| if geq { x } else { -x })
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

	/// Get bits; option to invert the sign bit to create an unsigned binary representation offset by `-2^(k-1)`
	pub(crate) fn xs(&self, to_unsigned: bool) -> Vec<LitOrConst<Lit>> {
		if GROUND_BINARY_AT_LB {
			self.x.clone()
		} else {
			self.x.clone()
			// self.x[..self.x.len() - 1]
			// 	.iter()
			// 	.cloned()
			// 	.chain({
			// 		let sign = self.x.last().unwrap().clone();
			// 		[if to_unsigned { -sign } else { sign }]
			// 	})
			// 	.collect()
		}
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
					lex_leq_const(db, &self.xs(true), k, self.bits())
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
					lex_geq_const(db, &self.xs(true), k, self.bits())
				}
			}
		}
	}

	/// Return conjunction of bits equivalent where `x=k`
	fn eq<C: Coefficient>(&self, k: C, dom: &Dom<C>) -> Result<Vec<Lit>, Unsatisfiable> {
		as_binary(self.normalize(k, dom).into(), Some(self.bits()))
			.into_iter()
			.zip(self.xs(true).iter())
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
			k.checked_sub(&two_comp_bounds(self.bits()).0).unwrap()
		}
	}

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

	// pub(crate) fn as_lin_exp<C: Coefficient>(&self) -> LinExp<Lit, C> {
	// 	let mut acc = self.lb();
	// 	LinExp::new()
	// 		.add_chain(
	// 			&self
	// 				.xs
	// 				.iter(..)
	// 				.map(|(iv, lit)| {
	// 					let v = iv.end - C::one() - acc;
	// 					acc += v;
	// 					(lit.clone(), v)
	// 				})
	// 				.collect::<Vec<_>>(),
	// 		)
	// 		.add_constant(self.lb())
	// }

	pub(crate) fn lits(&self) -> usize {
		self.x
			.iter()
			.filter(|x| matches!(x, LitOrConst::Lit(_)))
			.count()
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
	// type C = i64;

	use super::*;
	use crate::helpers::tests::TestDB;
	#[test]
	fn test_ineq() {
		// let mut model = Model::<Lit, C>::default();
		// let x = model
		// 	.new_var(&[2, 5, 6, 7, 9], true, None, Some(String::from("x")))
		// 	.unwrap();
		// let x = IntVar::<Lit, C>::new(1, &[2, 5, 6, 7, 9], true, None, Some(String::from("x")))
		// 	.into_ref();
		let mut db = TestDB::new(0);
		let dom = Dom::from_slice(&[2, 5, 6, 7, 9]);
		let x = BinEnc::new(&mut db, &dom);

		for (up, ks, expected_cnf) in [
			(true, (0, 1), vec![vec![1, 2, 3, 4]]),
			(
				true,
				(0, 3),
				vec![vec![1, 2, 3, 4], vec![2, 3, 4], vec![1, 3, 4]],
			),
		] {
			assert_eq!(
				x.ineq(ks, up),
				expected_cnf,
				"ks {ks:?} with up {up} was expected to return {expected_cnf:?}"
			);
		}
	}
}
