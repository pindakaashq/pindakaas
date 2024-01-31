use itertools::Itertools;

use crate::{
	helpers::{as_binary, two_comp_bounds},
	linear::{lex_geq_const, lex_leq_const},
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Comparator, Literal, Unsatisfiable,
};

use super::{enc::GROUND_BINARY_AT_LB, required_lits, Dom, LitOrConst};

#[derive(Debug, Clone)]
pub(crate) struct BinEnc<'a, Lit: Literal, C: Coefficient> {
	x: Vec<LitOrConst<Lit>>,
	dom: &'a Dom<C>,
}

impl<'a, Lit: Literal, C: Coefficient> BinEnc<'a, Lit, C> {
	pub fn new<DB: ClauseDatabase<Lit = Lit>>(db: &mut DB, dom: &'a Dom<C>) -> Self {
		let (lb, ub) = (dom.lb(), dom.ub());
		Self {
			x: (0..required_lits(lb, ub))
				.map(|_i| (new_var!(db, format!("b^{}", _i))).into())
				.chain(
					(!GROUND_BINARY_AT_LB && !lb.is_negative()).then_some(LitOrConst::Const(false)),
				)
				.collect(),
			dom,
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

	/// From domain position to cnf
	pub(crate) fn ineq(&self, p: Option<usize>, up: bool) -> Vec<Vec<Lit>> {
		todo!();
		// match p {
		// 	Some(0) => vec![],    // true
		// 	None => vec![vec![]], // false
		// 	Some(p) => {
		// 		vec![vec![if up {
		// 			self.x[p - 1].clone()
		// 		} else {
		// 			self.x[p - 1].negate()
		// 		}]]
		// 	} // lit
		// }
	}

	/// Get bits; option to invert the sign bit to create an unsigned binary representation offset by `-2^(k-1)`
	pub(crate) fn xs(&self, to_unsigned: bool) -> Vec<LitOrConst<Lit>> {
		if GROUND_BINARY_AT_LB {
			self.x.clone()
		} else {
			self.x[..self.x.len() - 1]
				.iter()
				.cloned()
				.chain({
					let sign = self.x.last().unwrap().clone();
					[if to_unsigned { -sign } else { sign }]
				})
				.collect()
		}
	}

	pub fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> crate::Result {
		self.encode_unary_constraint(db, &Comparator::GreaterEq, self.dom.lb(), true)?;
		self.encode_unary_constraint(db, &Comparator::LessEq, self.dom.ub(), true)?;
		for (a, b) in self.dom.ranges.iter().tuple_windows() {
			for k in num::range_inclusive(a.1 + C::one(), b.0 - C::one()) {
				self.encode_neq(db, k)?;
			}
		}
		Ok(())
	}

	/// Encode `x # k` where `# ∈ {≤,=,≥}`
	pub(crate) fn encode_unary_constraint<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		cmp: &Comparator,
		k: C,
		force: bool,
	) -> crate::Result {
		match cmp {
			Comparator::LessEq => {
				if k < self.dom.lb() {
					Err(Unsatisfiable)
				} else if k >= self.dom.ub() && !force {
					Ok(())
				} else {
					lex_leq_const(db, &self.xs(true), k, self.bits())
				}
			}
			Comparator::Equal => self
				.eq(k)?
				.into_iter()
				.try_for_each(|cls| emit_clause!(db, &[cls])),
			Comparator::GreaterEq => {
				if k > self.dom.ub() {
					Err(Unsatisfiable)
				} else if k <= self.dom.lb() && !force {
					Ok(())
				} else {
					lex_geq_const(db, &self.xs(true), k, self.bits())
				}
			}
		}
	}

	/// Return conjunction of bits equivalent where `x=k`
	fn eq(&self, k: C) -> Result<Vec<Lit>, Unsatisfiable> {
		as_binary(self.normalize(k).into(), Some(self.bits()))
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
	pub(crate) fn normalize(&self, k: C) -> C {
		if GROUND_BINARY_AT_LB {
			k - self.dom.lb()
		} else {
			// encoding is grounded at the lb of the two comp representation
			k.checked_sub(&two_comp_bounds(self.bits()).0).unwrap()
		}
	}

	pub(crate) fn encode_neq<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		k: C,
	) -> crate::Result {
		emit_clause!(db, &self.eq(k)?.iter().map(Lit::negate).collect::<Vec<_>>())
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

impl<'a, Lit: Literal, C: Coefficient> std::fmt::Display for BinEnc<'a, Lit, C> {
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
		dbg!(&x);

		for (up, dom_pos, expected_cnf) in [
			(true, Some(0), vec![]),
			(true, Some(1), vec![vec![1]]),
			(true, Some(2), vec![vec![2]]),
			(true, Some(3), vec![vec![3]]),
			(true, Some(4), vec![vec![4]]),
			(true, None, vec![vec![]]),
			(false, Some(0), vec![]),
			(false, Some(1), vec![vec![-1]]),
			(false, Some(2), vec![vec![-2]]),
			(false, Some(3), vec![vec![-3]]),
			(false, Some(4), vec![vec![-4]]),
			(false, None, vec![vec![]]),
		] {
			assert_eq!(
				x.ineq(dom_pos, up),
				expected_cnf,
				"Domain pos {dom_pos:?} with up {up} was expected to return {expected_cnf:?}"
			);
		}
	}
}
