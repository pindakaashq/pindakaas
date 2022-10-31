use iset::IntervalMap;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	linear::Part,
	trace::{emit_clause, new_var},
	ClauseDatabase, Coefficient, Literal, PosCoeff,
};
use std::{collections::HashSet, hash::BuildHasherDefault, ops::Neg};

#[derive(Clone, Debug, PartialEq)]
pub(crate) enum LitOrConst<Lit: Literal> {
	Lit(Lit),
	Const(bool),
}

impl<Lit: Literal> Neg for LitOrConst<Lit> {
	type Output = Self;

	fn neg(self) -> Self {
		match self {
			Self::Lit(lit) => Self::Lit(lit.negate()),
			Self::Const(b) => Self::Const(!b),
		}
	}
}

impl<Lit: Literal> LitOrConst<Lit> {
	// TODO replace for Signed?
	fn polarity(&self) -> bool {
		match self {
			Self::Lit(lit) => !lit.is_negated(),
			Self::Const(b) => *b,
		}
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Debug, Clone)]
pub(crate) struct IntVar<Lit: Literal, C: Coefficient> {
	xs: IntervalMap<C, Lit>,
	lb: PosCoeff<C>,
	ub: PosCoeff<C>,
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> for IntVar<Lit, C> {
	fn lb(&self) -> &C {
		&self.lb
	}

	fn ub(&self) -> &C {
		&self.ub
	}

	// TODO return ref
	// TODO impl Index
	fn eq(&self, v: &C) -> Vec<LitOrConst<Lit>> {
		self.geq(v)
			.into_iter()
			.chain(self.geq(v).into_iter().map(|v| v.neg()))
			.collect()
	}
	fn geq(&self, v: &C) -> Vec<LitOrConst<Lit>> {
		vec![if v <= self.lb() {
			LitOrConst::Const(true)
		} else if v > self.ub() {
			LitOrConst::Const(false)
		} else {
			match self.xs.overlap(*v).collect::<Vec<_>>()[..] {
				[(_, x)] => LitOrConst::Lit(x.clone()),
				// _ => panic!("No or multiples variables at {v:?} in {self:?}"),
				_ => panic!("No or multiples variables"),
			}
		}]
	}
}

// TODO maybe C -> PosCoeff<C>
#[derive(Clone, Debug)]
pub(crate) struct IntVarBin<Lit: Literal, C: Coefficient> {
	xs: Vec<Lit>,
	lb: C,
	ub: C,
}

impl<Lit: Literal, C: Coefficient> IntVarEnc<Lit, C> for IntVarBin<Lit, C> {
	fn lb(&self) -> &C {
		&self.lb
	}

	fn ub(&self) -> &C {
		&self.ub
	}

	// TODO return ref
	// TODO impl Index
	fn geq(&self, v: &C) -> Vec<LitOrConst<Lit>> {
		let mut v = *v;
		v.unsigned_shl(v.trailing_zeros());
		let mut vs: Vec<LitOrConst<Lit>> = vec![];
		let mut i = 0;
		loop {
			vs.push(LitOrConst::Lit(self.xs[i].clone()));
			v = v.signed_shl(v.signed_shl(1).trailing_zeros() + 1); // TODO not sure if better than just shifting one at a time
			i += v.trailing_zeros() as usize;
			if i >= self.xs.len() {
				return vs;
			}
		}
	}

	fn eq(&self, _: &C) -> Vec<LitOrConst<Lit>> {
		todo!();
	}
}
impl<Lit: Literal, C: Coefficient> IntVar<Lit, C> {
	pub fn new(xs: IntervalMap<C, Lit>, lb: PosCoeff<C>, ub: PosCoeff<C>) -> Self {
		debug_assert!(*lb <= *ub);
		Self { xs, lb, ub }
	}

	pub fn from_terms(terms: Vec<(PosCoeff<C>, Lit)>, lb: PosCoeff<C>, ub: PosCoeff<C>) -> Self {
		// TODO perhaps lb/ub should always be equal to min/max of terms
		debug_assert!(*lb <= *ub);
		Self {
			xs: IntervalMap::from_sorted(
				terms
					.into_iter()
					.map(|(coef, lit)| (*coef..(*coef + C::one()), lit)),
			),
			lb,
			ub,
		}
	}

	pub fn constant(c: PosCoeff<C>) -> Self {
		Self {
			xs: IntervalMap::new(),
			lb: c.clone(),
			ub: c,
		}
	}

	pub fn iter(&self) -> impl Iterator<Item = (LitOrConst<Lit>, PosCoeff<C>)> + '_ {
		std::iter::once((LitOrConst::Const(true), self.lb.clone())).chain(
			self.xs
				.iter(..)
				.map(|(c, l)| (LitOrConst::Lit(l.clone()), (c.end - C::one()).into())),
		)
	}

	pub fn encode_consistency<DB: ClauseDatabase<Lit = Lit> + ?Sized>(&self, db: &mut DB) {
		self.iter()
			.tuple_windows()
			.skip(1)
			.for_each(|((lit_a, _), (lit_b, _))| {
				// TODO clean up
				if let LitOrConst::Lit(a) = lit_a {
					if let LitOrConst::Lit(b) = lit_b {
						emit_clause!(db, &[b.negate(), a]).unwrap();
					} else {
						panic!();
					}
				} else {
					panic!();
				}
			});
	}

	/// Constructs IntVar `y` for linear expression `xs` so that ∑ xs ≦ y, using order encoding
	pub fn from_part_using_le_ord<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		xs: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
	) -> Self {
		// TODO add_consistency on coupled leaves (wherever not equal to principal vars)
		// if add_consistency {
		// 	for leaf in &leaves {
		// 		leaf.encode_consistency(db);
		// 	}
		// }

		// couple given encodings to the order encoding
		// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

		match xs {
			Part::Amo(terms) => {
				let terms: Vec<(PosCoeff<C>, DB::Lit)> = terms
					.iter()
					.map(|(lit, coef)| (coef.clone(), lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: FxHashMap<C, Vec<DB::Lit>> =
					FxHashMap::with_capacity_and_hasher(terms.len(), BuildHasherDefault::default());
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(*coef).or_insert_with(Vec::new).push(lit);
				}

				let xs = h
					.into_iter()
					.map(|(coef, lits)| -> (PosCoeff<C>, _) {
						if lits.len() == 1 {
							(coef.into(), lits[0].clone())
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								emit_clause!(db, &[lit.negate(), o.clone()]).unwrap();
							}
							(coef.into(), o)
						}
					})
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					.collect::<Vec<(_, _)>>();

				let ub = xs
					.iter()
					.map(|(c, _)| (*c.clone()))
					.max()
					.unwrap_or(*ub)
					.into();
				IntVar::from_terms(xs, C::zero().into(), ub)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				IntVar::from_terms(
					terms
						.iter()
						.map(|(lit, coef)| {
							acc += **coef;
							debug_assert!(acc <= *ub);
							(acc.into(), lit.clone())
						})
						.collect(),
					C::zero().into(),
					ub,
				)
			}
			Part::Dom(_terms, _l, _u) => todo!(),
			// Part::Dom(terms, l, u) => build_totalizer(
			// 	terms
			// 		.iter()
			// 		// .chain(std::iter::once(IntVar::new(vec![], -l, -l); % TODO need neg. coefficients and int addition!
			// 		.map(|(lit, coef)| IntVar::new(vec![(*coef, lit.clone())], C::zero(), *coef))
			// 		.collect(),
			// 	db,
			// 	*l,
			// 	std::cmp::min(*u, ub),
			// 	false,
			// 	add_consistency,
			// 	0,
			// ),
		}
	}
}

pub(crate) trait IntVarEnc<Lit: Literal, C: Coefficient> {
	// fn index(&self, v: &C) -> &Self::Output;
	fn geq(&self, v: &C) -> Vec<LitOrConst<Lit>> {
		self.eq(v).into_iter().filter(|x| x.polarity()).collect()
	}

	fn eq(&self, v: &C) -> Vec<LitOrConst<Lit>>;
	fn lb(&self) -> &C;
	fn ub(&self) -> &C;
}
pub(crate) fn ord_plus_ord_le_ord<DB: ClauseDatabase + ?Sized, C: Coefficient>(
	db: &mut DB,
	a: &IntVar<DB::Lit, C>,
	b: &IntVar<DB::Lit, C>,
	c: &IntVar<DB::Lit, C>,
) {
	for (l_a, c_a) in a.iter() {
		for (l_b, c_b) in b.iter() {
			let create_clause =
				|lits: Vec<LitOrConst<DB::Lit>>| -> std::result::Result<Vec<DB::Lit>, ()> {
					lits.into_iter()
						.filter_map(|lit| match lit {
							LitOrConst::Lit(lit) => Some(Ok(lit)),
							LitOrConst::Const(true) => Some(Err(())), // clause satisfied
							LitOrConst::Const(false) => None,         // literal falsified
						})
						.collect()
				};

			// TODO check
			let l_c = c.geq(&(*c_a + *c_b))[0].clone();
			if !(l_a == l_c.clone() || l_b == l_c.clone()) {
				if let Ok(cls) = &create_clause(vec![-l_a.clone(), -l_b, l_c.clone()]) {
					emit_clause!(db, cls).unwrap();
				}
			}
		}
	}
}

pub(crate) fn ord_plus_ord_le_ord_sparse_dom<C: Coefficient>(
	a: Vec<C>,
	b: Vec<C>,
	l: C,
	u: C,
) -> Vec<C> {
	HashSet::<C>::from_iter(a.iter().flat_map(|a| {
		b.iter().filter_map(move |b| {
			// TODO refactor: use then_some when stabilized
			if *a + *b > l && *a + *b <= u {
				Some(*a + *b)
			} else {
				None
			}
		})
	}))
	.into_iter()
	.sorted()
	.collect::<Vec<_>>()
}

#[cfg(test)]
pub mod tests {
	use super::*;

	#[test]
	fn bin_geq_test() {
		let x = IntVarBin {
			xs: vec![1, 2, 3, 4],
			lb: 0,
			ub: 12,
		};
		assert_eq!(x.geq(&3), vec![LitOrConst::Lit(1), LitOrConst::Lit(3)]);
	}
}
