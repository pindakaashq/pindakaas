use crate::linear::{ClauseDatabase, Encoder, LimitComp, Linear, Literal, Part};
use crate::{PositiveCoefficient, Result};
use std::collections::{HashMap, HashSet};
use std::ops::Neg;

pub enum Structure {
	Gt,
	Swc,
	Bdd,
}

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
pub struct TotalizerEncoder<'a, Lit: Literal, PC: PositiveCoefficient> {
	lin: &'a Linear<Lit, PC>,
}

impl<'a, Lit: Literal, PC: PositiveCoefficient> TotalizerEncoder<'a, Lit, PC> {
	pub fn new(lin: &'a Linear<Lit, PC>) -> Self {
		Self { lin }
	}
}

impl<'a, Lit: Literal, PC: PositiveCoefficient> Encoder for TotalizerEncoder<'a, Lit, PC> {
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		totalize(db, self.lin, Structure::Gt)
	}
}

pub fn totalize<DB: ClauseDatabase<Lit = Lit>, Lit: Literal, PC: PositiveCoefficient>(
	db: &mut DB,
	lin: &Linear<Lit, PC>,
	structure: Structure,
) -> Result<()> {
	assert!(lin.cmp == LimitComp::LessEq);
	let x_le_ord = |part: &Part<Lit, PC>| -> IntVar<Lit, PC> {
		match part {
			Part::Amo(terms) => {
				let terms: Vec<(PC, Lit)> = terms
					.iter()
					.map(|(lit, coef)| (*coef, lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: HashMap<PC, Vec<Lit>> = HashMap::with_capacity(terms.len());
				for (coef, lit) in terms {
					h.entry(coef).or_insert_with(Vec::new).push(lit);
				}

				IntVar::new(
					h.into_iter()
						.map(|(coef, lits)| {
							if lits.len() == 1 {
								(coef, lits[0].clone())
							} else {
								let o = db.new_var();
								for lit in lits {
									db.add_clause(&[lit.negate(), o.clone()]).unwrap();
								}
								(coef, o)
							}
						})
						.collect(),
					PC::zero(),
					lin.k,
				)
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = PC::zero(); // running sum
				IntVar::new(
					terms
						.iter()
						.map(|(lit, coef)| {
							acc += *coef;
							(acc, lit.clone())
						})
						.collect(),
					PC::zero(),
					lin.k,
				)
			}
			Part::Dom(terms, _l, u) => build_totalizer(
				terms
					.iter()
					.map(|(lit, coef)| IntVar::new(vec![(*coef, lit.clone())], PC::zero(), lin.k))
					.collect(),
				db,
				PC::zero(), // TODO _l has to be used here, somehow.
				*u,
				false,
			),
		}
	};

	// couple given encodings to the order encoding
	let leaves = lin.terms.iter().map(x_le_ord).collect();
	// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

	match structure {
		Structure::Gt => {
			// The totalizer encoding constructs a binary tree starting from a layer of leaves
			build_totalizer(leaves, db, PC::zero(), lin.k, true);
		}
		Structure::Swc => {
			leaves.into_iter().reduce(|prev, leaf| {
				let next = IntVar::new(
					num::iter::range_inclusive(PC::one(), lin.k)
						.map(|j| (j, db.new_var()))
						.collect(),
					PC::zero(),
					lin.k,
				);
				ord_plus_ord_le_ord(db, &prev, &leaf, &next);
				next
			});
		}
		Structure::Bdd => {
			// TODO still need to figure out 'long edges'
			// TODO bdd construction and reduction
			leaves.into_iter().reduce(|v_i, x_i| {
				let parent = IntVar::new(
					ord_plus_ord_le_ord_sparse_dom(
						v_i.iter().map(|(_, c)| c).collect(),
						x_i.iter().map(|(_, c)| c).collect(),
						PC::zero(),
						lin.k,
					)
					.into_iter()
					.map(|c| (c, db.new_var()))
					.collect(),
					PC::zero(),
					lin.k,
				);
				ord_plus_ord_le_ord(db, &v_i, &x_i, &parent);
				parent
			});
		}
	};
	Ok(())
}

#[derive(Clone, Debug)]
enum LitOrConst<Lit: Literal> {
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
struct IntVar<Lit: Literal, PC: PositiveCoefficient> {
	xs: HashMap<PC, Lit>,
	lb: PC,
	ub: PC,
}

impl<Lit: Literal, PC: PositiveCoefficient> IntVar<Lit, PC> {
	pub fn new(terms: Vec<(PC, Lit)>, lb: PC, ub: PC) -> Self {
		Self {
			xs: HashMap::from_iter(terms),
			lb,
			ub,
		}
	}

	fn lb(&self) -> PC {
		self.lb
	}

	fn ub(&self) -> PC {
		self.ub
	}

	fn ge(&self, v: PC) -> LitOrConst<Lit> {
		if v <= self.lb() {
			LitOrConst::Const(true)
		} else if v > self.ub() {
			LitOrConst::Const(false)
		} else {
			LitOrConst::Lit(self.xs[&v].clone())
		}
	}

	fn iter(&self) -> impl Iterator<Item = (LitOrConst<Lit>, PC)> + '_ {
		std::iter::once((LitOrConst::Const(true), self.lb)).chain(
			self.xs
				.iter()
				.map(|(c, l)| (LitOrConst::Lit(l.clone()), *c)),
		)
	}
}

fn ord_plus_ord_le_ord<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	a: &IntVar<Lit, PC>,
	b: &IntVar<Lit, PC>,
	c: &IntVar<Lit, PC>,
) {
	for (l_a, c_a) in a.iter() {
		for (l_b, c_b) in b.iter() {
			let create_clause = |lits: Vec<LitOrConst<Lit>>| -> std::result::Result<Vec<Lit>, ()> {
				lits.into_iter()
					.filter_map(|lit| match lit {
						LitOrConst::Lit(lit) => Some(Ok(lit)),
						LitOrConst::Const(true) => Some(Err(())), // clause satisfied
						LitOrConst::Const(false) => None,         // literal falsified
					})
					.collect()
			};

			if let Ok(cls) = &create_clause(vec![-l_a.clone(), -l_b, c.ge(c_a + c_b)]) {
				db.add_clause(cls).unwrap();
			}
		}
	}
}

fn build_totalizer<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	mut layer: Vec<IntVar<Lit, PC>>,
	db: &mut DB,
	l: PC,
	u: PC,
	limit_root: bool,
) -> IntVar<Lit, PC> {
	if layer.len() == 1 {
		layer.pop().unwrap()
	} else if limit_root && layer.len() == 2 {
		let parent = IntVar::new(vec![], u, u);
		ord_plus_ord_le_ord(db, &layer[0], &layer[1], &parent);
		parent
	} else {
		build_totalizer(
			layer
				.chunks(2)
				.map(|children| match children {
					[x] => x.clone(),
					[left, right] => {
						let parent = IntVar::new(
							ord_plus_ord_le_ord_sparse_dom(
								left.iter().map(|(_, c)| c).collect(),
								right.iter().map(|(_, c)| c).collect(),
								l,
								u,
							)
							.into_iter()
							.map(|c| (c, db.new_var()))
							.collect(),
							PC::zero(),
							u,
						);
						ord_plus_ord_le_ord(db, left, right, &parent);
						parent
					}
					_ => panic!(),
				})
				.collect(),
			db,
			l,
			u,
			limit_root,
		)
	}
}

fn ord_plus_ord_le_ord_sparse_dom<PC: PositiveCoefficient>(
	a: Vec<PC>,
	b: Vec<PC>,
	l: PC,
	u: PC,
) -> HashSet<PC> {
	HashSet::from_iter(a.iter().flat_map(|a| {
		b.iter().filter_map(move |b| { // TODO refactor: use then_some when stabilized
			if *a + *b > l && *a + *b <= u {
				Some(*a + *b)
			} else {
				None
			}
		})
	}))
}

// #[cfg(test)]
// mod tests {
// 	use super::*;
// 	use crate::tests::TestDB;

// 	#[test]
// 	fn test_totalizer_encode_amo() {
// 		let mut db = TestDB::new(8)
// 		// .with_check(|sol| {
// 		// 	check_pb(
// 		// 		&vec![2, 3, 4, 5, 3, 4, 6, 8],
// 		// 		&vec![1, 2, 3, 4, 5, 6, 7, 8],
// 		// 		Comparator::LessEq,
// 		// 		10,
// 		// 		sol,
// 		// 	)
// 		// })
// 		;
// 		assert!(encode_bool_lin_le_totalizer(
// 			&mut db,
// 			&[
// 				Part::Amo(vec![(1, 2), (2, 3), (3, 4), (4, 5)],),
// 				Part::Amo(vec![(5, 3), (6, 4), (7, 6), (8, 8)],)
// 			],
// 			Comparator::LessEq,
// 			10 as u32
// 		)
// 		.is_ok());
// 		db.check_complete();
// 	}
// 	#[test]
// 	fn test_totalizer_encode_ic() {
// 		let mut db = TestDB::new(8)
// 		// .with_check(|sol| {
// 		// 	check_pb(
// 		// 		&vec![2, 3, 4, 5, 3, 4, 6, 8],
// 		// 		&vec![1, 2, 3, 4, 5, 6, 7, 8],
// 		// 		Comparator::LessEq,
// 		// 		10,
// 		// 		sol,
// 		// 	)
// 		// })
// 		;
// 		assert!(encode_bool_lin_le_totalizer(
// 			&mut db,
// 			&[
// 				Part::Amo(vec![(1, 2), (2, 3), (3, 4), (4, 5)],),
// 				Part::Amo(vec![(5, 3), (6, 4), (7, 6), (8, 8)],)
// 			],
// 			Comparator::LessEq,
// 			10 as u32
// 		)
// 		.is_ok());
// 		db.check_complete();
// 	}
// }
