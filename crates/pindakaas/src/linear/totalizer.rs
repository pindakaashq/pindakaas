use itertools::Itertools;
use std::{
	collections::{HashMap, HashSet},
	ops::Neg,
};

use crate::{
	linear::{LimitComp, Part},
	ClauseDatabase, Coefficient, Encoder, Linear, Literal, PosCoeff, Result,
};

// TODO
macro_rules! new_var {
	($db:expr) => {
		$db.new_var()
	};
	($db:expr, $lbl:expr) => {
		// $db.new_var_with_label($lbl)
		$db.new_var()
	};
}

#[cfg(not(debug_assertions))]
#[macro_export]
macro_rules! new_var {
	($db:expr) => {
		$db.new_var()
	};
	($db:expr, $lbl:expr) => {
		// $db.new_var_with_label($lbl)
		$db.new_var()
	};
}

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Binary Decision Diagram (BDD)
#[derive(Default)]
pub struct TotalizerEncoder {
	add_consistency: bool,
}

impl TotalizerEncoder {
	pub fn add_consistency(&mut self, b: bool) {
		self.add_consistency = b;
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for TotalizerEncoder {
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		totalize(db, lin, Structure::Gt, self.add_consistency)
	}
}

pub enum Structure {
	Gt,
	Swc,
	Bdd,
}

pub fn totalize<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	lin: &Linear<DB::Lit, C>,
	structure: Structure,
	add_consistency: bool,
) -> Result<()> {
	assert!(lin.cmp == LimitComp::LessEq);
	let x_le_ord = |part: &Part<DB::Lit, PosCoeff<C>>| -> IntVar<DB::Lit, C> {
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
					lin.k.clone(),
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
					lin.k.clone(),
				)
			}
			Part::Dom(terms, l, u) => build_totalizer(
				terms
					.iter()
					// .chain(std::iter::once(IntVar::new(vec![], -l, -l); % TODO need neg. coefficients and int addition!
					.map(|(lit, coef)| {
						IntVar::new(
							vec![(coef.clone(), lit.clone())],
							C::zero().into(),
							coef.clone(),
						)
					})
					.collect(),
				db,
				l.clone(),
				std::cmp::min(u.clone(), lin.k.clone()),
				false,
				add_consistency,
				0,
			),
		}
	};

	let leaves = lin.terms.iter().map(x_le_ord).collect::<Vec<_>>();

	// TODO add_consistency on coupled leaves (wherever not equal to principal vars)
	// if add_consistency {
	// 	for leaf in &leaves {
	// 		leaf.encode_consistency(db);
	// 	}
	// }

	// couple given encodings to the order encoding
	// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

	match structure {
		Structure::Gt => {
			// The totalizer encoding constructs a binary tree starting from a layer of leaves
			build_totalizer(
				leaves,
				db,
				C::zero().into(),
				lin.k.clone(),
				true,
				add_consistency,
				0,
			);
		}
		Structure::Swc => {
			leaves
				.into_iter()
				.enumerate()
				.reduce(|(i, prev), (_, leaf)| {
					let next = IntVar::new(
						num::iter::range_inclusive(C::one(), *lin.k)
							.map(|j| (j.into(), new_var!(db, format!("w_{}>={:?}", i + 1, j))))
							.collect(),
						C::zero().into(),
						lin.k.clone(),
					);

					if add_consistency {
						next.encode_consistency(db);
					}

					ord_plus_ord_le_ord(db, &prev, &leaf, &next);
					(i + 1, next)
				});
		}
		Structure::Bdd => {
			// TODO still need to figure out 'long edges'
			// TODO bdd construction and reduction
			leaves.into_iter().enumerate().reduce(|(i, v_i), (_, x_i)| {
				let parent = IntVar::new(
					ord_plus_ord_le_ord_sparse_dom(
						v_i.iter().map(|(_, c)| c).collect(),
						x_i.iter().map(|(_, c)| c).collect(),
						C::zero().into(),
						lin.k.clone(),
					)
					.into_iter()
					.map(|c| (c.into(), new_var!(db, format!("w_{}>={:?}", i + 1, c))))
					.collect(),
					C::zero().into(),
					lin.k.clone(),
				);

				if add_consistency {
					parent.encode_consistency(db);
				}

				ord_plus_ord_le_ord(db, &v_i, &x_i, &parent);
				(i + 1, parent)
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
struct IntVar<Lit: Literal, C: Coefficient> {
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

	fn lb(&self) -> PosCoeff<C> {
		self.lb.clone()
	}

	fn ub(&self) -> PosCoeff<C> {
		self.ub.clone()
	}

	fn ge(&self, v: PosCoeff<C>) -> LitOrConst<Lit> {
		if v <= self.lb() {
			LitOrConst::Const(true)
		} else if v > self.ub() {
			LitOrConst::Const(false)
		} else {
			LitOrConst::Lit(self.xs[&v].clone())
		}
	}

	fn iter(&self) -> impl Iterator<Item = (LitOrConst<Lit>, PosCoeff<C>)> + '_ {
		std::iter::once((LitOrConst::Const(true), self.lb.clone())).chain(
			self.xs
				.iter()
				.map(|(c, l)| (LitOrConst::Lit(l.clone()), (*c).into())),
		)
	}

	fn encode_consistency<DB: ClauseDatabase<Lit = Lit> + ?Sized>(&self, db: &mut DB) {
		self.xs.keys().sorted().tuple_windows().for_each(|(a, b)| {
			db.add_clause(&[self.xs[b].negate(), self.xs[a].clone()])
				.unwrap();
		});
	}
}

fn ord_plus_ord_le_ord<Lit: Literal, DB: ClauseDatabase<Lit = Lit> + ?Sized, C: Coefficient>(
	db: &mut DB,
	a: &IntVar<Lit, C>,
	b: &IntVar<Lit, C>,
	c: &IntVar<Lit, C>,
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

			if let Ok(cls) = &create_clause(vec![-l_a.clone(), -l_b, c.ge((*c_a + *c_b).into())]) {
				db.add_clause(cls).unwrap();
			}
		}
	}
}

fn build_totalizer<Lit: Literal, DB: ClauseDatabase<Lit = Lit> + ?Sized, C: Coefficient>(
	mut layer: Vec<IntVar<Lit, C>>,
	db: &mut DB,
	l: PosCoeff<C>,
	u: PosCoeff<C>,
	limit_root: bool,
	add_consistency: bool,
	level: u32,
) -> IntVar<Lit, C> {
	if layer.len() == 1 {
		let root = layer.pop().unwrap();
		if limit_root {
			let zero = IntVar::constant(C::zero().into());
			let parent = IntVar::constant(u);
			ord_plus_ord_le_ord(db, &root, &zero, &parent);
		}
		root
	} else if limit_root && layer.len() == 2 {
		let parent = IntVar::constant(u);
		ord_plus_ord_le_ord(db, &layer[0], &layer[1], &parent);
		parent
	} else {
		build_totalizer(
			layer
				.chunks(2)
				.enumerate()
				.map(|(_node, children)| match children {
					[x] => x.clone(),
					[left, right] => {
						let l = if layer.len() > 2 {
							C::zero().into()
						} else {
							l.clone()
						};
						let parent = IntVar::new(
							ord_plus_ord_le_ord_sparse_dom(
								left.iter().map(|(_, c)| c).collect(),
								right.iter().map(|(_, c)| c).collect(),
								l.clone(),
								u.clone(),
							)
							.into_iter()
							.map(|c| {
								(
									c.into(),
									new_var!(db, format!("w_{}_{}>={c:?}", level + 1, _node + 1)),
								)
							})
							.collect(),
							l,
							u.clone(),
						);

						if add_consistency {
							parent.encode_consistency(db);
						}

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
			add_consistency,
			level + 1,
		)
	}
}

fn ord_plus_ord_le_ord_sparse_dom<C: Coefficient>(
	a: Vec<PosCoeff<C>>,
	b: Vec<PosCoeff<C>>,
	l: PosCoeff<C>,
	u: PosCoeff<C>,
) -> HashSet<C> {
	let mut set = HashSet::new();
	for x in a {
		for y in b.iter() {
			if *x + **y > *l && *x + **y <= *u {
				set.insert(*x + **y);
			}
		}
	}
	set
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Checker,
		Encoder,
	};

	linear_test_suite!(TotalizerEncoder::default());
	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
}
