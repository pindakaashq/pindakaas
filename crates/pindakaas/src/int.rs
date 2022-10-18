use itertools::Itertools;

use crate::{linear::Part, new_var, ClauseDatabase, Coefficient, Literal, PosCoeff};
use std::{
	collections::{HashMap, HashSet},
	ops::Neg,
};

#[derive(Clone, Debug)]
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

#[derive(Debug, Clone)]
pub(crate) struct IntVar<Lit: Literal, C: Coefficient> {
	xs: HashMap<C, Lit>,
	lb: PosCoeff<C>,
	ub: PosCoeff<C>,
}

impl<Lit: Literal, C: Coefficient> IntVar<Lit, C> {
	pub fn new(terms: Vec<(PosCoeff<C>, Lit)>, lb: PosCoeff<C>, ub: PosCoeff<C>) -> Self {
		Self {
			xs: HashMap::from_iter(terms.into_iter().map(|(c, l)| (*c, l))),
			lb,
			ub,
		}
	}

	pub fn constant(c: PosCoeff<C>) -> Self {
		Self {
			xs: HashMap::new(),
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
			LitOrConst::Lit(self.xs[&v].clone())
		}
	}
	pub fn iter(&self) -> impl Iterator<Item = (LitOrConst<Lit>, PosCoeff<C>)> + '_ {
		std::iter::once((LitOrConst::Const(true), self.lb.clone())).chain(
			self.xs
				.iter()
				.map(|(c, l)| (LitOrConst::Lit(l.clone()), (*c).into())),
		)
	}

	pub fn encode_consistency<DB: ClauseDatabase<Lit = Lit> + ?Sized>(&self, db: &mut DB) {
		self.xs.keys().sorted().tuple_windows().for_each(|(a, b)| {
			db.add_clause(&[self.xs[b].negate(), self.xs[a].clone()])
				.unwrap();
		});
	}

	/// Constructs IntVar `x` for a set of variables `S` so that `S` ≦ `x` using order encoding
	pub fn from_part_using_le_ord<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		part: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
	) -> Self {
		match part {
			Part::Amo(terms) => {
				let terms: Vec<(PosCoeff<C>, DB::Lit)> = terms
					.iter()
					.map(|(lit, coef)| (coef.clone(), lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: HashMap<C, Vec<DB::Lit>> = HashMap::with_capacity(terms.len());
				for (coef, lit) in terms {
					h.entry(*coef).or_insert_with(Vec::new).push(lit);
				}

				IntVar::new(
					h.into_iter()
						.map(|(coef, lits)| {
							if lits.len() == 1 {
								(coef.into(), lits[0].clone())
							} else {
								let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
								for lit in lits {
									db.add_clause(&[lit.negate(), o.clone()]).unwrap();
								}
								(coef.into(), o)
							}
						})
						.collect(),
					C::zero().into(),
					ub,
				)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = C::zero(); // running sum
				IntVar::new(
					terms
						.iter()
						.map(|(lit, coef)| {
							acc += **coef;
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

			if let Ok(cls) = &create_clause(vec![-l_a.clone(), -l_b, c.ge((*c_a + *c_b).into())]) {
				db.add_clause(cls).unwrap();
			}
		}
	}
}

pub(crate) fn ord_plus_ord_le_ord_sparse_dom<C: Coefficient>(
	a: Vec<C>,
	b: Vec<C>,
	l: C,
	u: C,
) -> HashSet<C> {
	HashSet::from_iter(a.iter().flat_map(|a| {
		b.iter().filter_map(move |b| {
			// TODO refactor: use then_some when stabilized
			if *a + *b > l && *a + *b <= u {
				Some(*a + *b)
			} else {
				None
			}
		})
	}))
}
