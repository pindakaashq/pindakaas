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

// TODO maybe C -> PosCoeff<C>
#[derive(Debug, Clone)]
pub(crate) struct IntVar<Lit: Literal, C: Coefficient> {
	xs: IntervalMap<C, Lit>,
	lb: PosCoeff<C>,
	ub: PosCoeff<C>,
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

	pub fn lb(&self) -> PosCoeff<C> {
		self.lb.clone()
	}

	pub fn ub(&self) -> PosCoeff<C> {
		self.ub.clone()
	}

	pub fn ge(&self, v: PosCoeff<C>) -> LitOrConst<Lit> {
		if v <= self.lb() {
			LitOrConst::Const(true)
		} else if v > self.ub() {
			LitOrConst::Const(false)
		} else {
			match self.xs.overlap(*v).collect::<Vec<_>>()[..] {
				[(_, x)] => LitOrConst::Lit(x.clone()),
				_ => panic!("No or multiples variables at {v:?} in {self:?}"),
			}
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

			let l_c = c.ge((*c_a + *c_b).into());
			if !(l_a == l_c.clone() || l_b == l_c.clone()) {
				if let Ok(cls) = &create_clause(vec![-l_a.clone(), -l_b, l_c]) {
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
