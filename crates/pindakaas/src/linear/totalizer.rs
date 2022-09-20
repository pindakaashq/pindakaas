use crate::linear::{ClauseDatabase, Encoder, LimitComp, Linear, Literal, Part};
use crate::{PositiveCoefficient, Result};
use itertools::{Itertools, Position};
use std::collections::HashMap;

pub enum Structure {
	Gt,
	Swc,
	Bdd,
}

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
pub struct TotalizerEncoder<Lit: Literal, PC: PositiveCoefficient> {
	lin: Linear<Lit, PC>,
}

impl<Lit: Literal, PC: PositiveCoefficient> TotalizerEncoder<Lit, PC> {
	pub fn new(lin: Linear<Lit, PC>) -> Self {
		Self { lin }
	}
}

impl<Lit: Literal, PC: PositiveCoefficient> Encoder for TotalizerEncoder<Lit, PC> {
	type Lit = Lit;
	type Ret = ();

	fn encode<DB: ClauseDatabase<Lit = Lit>>(&mut self, db: &mut DB) -> Result<Self::Ret> {
		totalize(db, &mut self.lin, Structure::Gt)
	}
}

pub fn totalize<DB: ClauseDatabase<Lit = Lit>, Lit: Literal, PC: PositiveCoefficient>(
	db: &mut DB,
	lin: &mut Linear<Lit, PC>,
	structure: Structure,
) -> Result<()> {
	assert!(lin.cmp == LimitComp::LessEq);
	// Every layer of the totalizer (binary) tree has nodes containing literals associated with (unique) values (which equal the sum so far)
	let construct_leaf = |part: &Part<Lit, PC>| -> HashMap<PC, Lit> {
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
					.collect()
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(terms) => {
				let mut acc = PC::zero(); // running sum
				terms
					.iter()
					.map(|(lit, coef)| {
						acc += *coef;
						(acc, lit.clone())
					})
					.collect()
			}
			Part::Dom(terms, l, u) => {
				return build_totalizer(
					terms
						.iter()
						.map(|(lit, coef)| HashMap::from_iter([(*coef, lit.clone())]))
						.collect(),
					db,
					*l,
					*u,
				);
			}
		}
	};

	let leaves = lin.terms.iter().map(construct_leaf).collect();
	// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

	match structure {
		// Gt = { Tree structure, one false root node, no consistency on partial sum, sparse nodes }
		Structure::Gt => {
			// The totalizer encoding constructs a binary tree starting from a layer of leaves
			let root = build_totalizer(leaves, db, PC::zero(), lin.k + PC::one());
			// Then, the k+1'th root node variable is set to false
			db.add_clause(&[root.get(&(lin.k+PC::one()))
                .expect("If no lit exists with value k+1 in the root node of the totalizer, the constraint was trivially satisfiable").negate()]).unwrap()
		}
		Structure::Swc => {
			// Every counter s_i has k outputs, with those of s_0 set to false
			let f = db.new_var(); // TODO probably avoidable to create a false lit for this initial layer
			db.add_clause(&[f.negate()])?;
			let s_0 = HashMap::<PC, Lit>::from_iter(
				num::iter::range_inclusive(PC::one(), lin.k).map(|k| (k, f.clone())),
			);

			leaves.into_iter().fold(s_0, |prev, leaf| {
				// x_i reduces limits s_i-1 by K+1-q_i (x_i -> s_i<K+1-q_i)
				for (coef, lit) in leaf.iter() {
					// TODO currently panicking on underflows for some test cases; normalization should have prevented coef>k+1
					let w = lin.k + PC::one() - *coef;
					db.add_clause(&[lit.negate(), prev[&w].negate()]).unwrap();
				}

				let mut next = HashMap::<PC, Lit>::from_iter(
					num::iter::range_inclusive(PC::one(), lin.k).map(|j| (j, db.new_var())),
				);

				ord_le_ord(db, &prev, &mut next); // s_i-1 <= s_i
				ord_le_ord_full(db, &leaf, &mut next); // forall(j in 0..q_i)( x_i-j <= s_i )
				ord_plus_ord_le_ord(db, &prev, &leaf, &mut next, lin.k);
				next
			});
		}
		Structure::Bdd => {
			let v_r = db.new_var(); // the "root" path node
			let v_f = db.new_var(); // the 0-terminal node
			let v_t = db.new_var(); // the 1-terminal node

			// TODO still need to figure out 'long edges'

			leaves.into_iter().with_position().fold(
				HashMap::<PC, Lit>::from_iter(std::iter::once((PC::zero(), v_r.clone()))),
				|v_i, x_i| {
					// the last layer should only contain the 0- and 1-terminal nodes
					let mut v_j = match x_i {
						Position::Last(_) => HashMap::<PC, Lit>::from_iter(
							(num::iter::range_inclusive(PC::zero(), lin.k))
								.map(|k| (k, v_t.clone()))
								.chain(std::iter::once((lin.k + PC::one(), v_f.clone()))),
						),
						_ => HashMap::new(),
					};

					ord_le_ord(db, &v_i, &mut v_j); // v_i <= v_j
					ord_plus_ord_le_ord(db, &v_i, &x_i.into_inner(), &mut v_j, lin.k + PC::one()); // v_i + x_i <= v_j
					v_j
				},
			);

			db.add_clause(&[v_r])?;
			db.add_clause(&[v_f.negate()])?;
			db.add_clause(&[v_t])?;
		}
	};
	Ok(())
}

fn ord_plus_ord_le_ord<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	a: &HashMap<PC, Lit>,
	b: &HashMap<PC, Lit>,
	c: &mut HashMap<PC, Lit>,
	u: PC,
) {
	for (w_a, l_a) in a.iter() {
		for (w_b, l_b) in b.iter() {
			let w = std::cmp::min(*w_a + *w_b, u);
			let l_c = c.entry(w).or_insert_with(|| db.new_var());
			// TODO adds redundant clauses for SWC
			db.add_clause(&[l_a.negate(), l_b.negate(), l_c.clone()])
				.unwrap();
		}
	}
}

fn ord_le_ord_full<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	a: &HashMap<PC, Lit>,
	b: &mut HashMap<PC, Lit>,
) {
	// TODO figure out if these two versions can fall under the same inequality coupling
	for (w_a, l_a) in a.iter() {
		for (_, l_b) in b.iter().filter(|(w_b, _)| *w_b <= w_a) {
			db.add_clause(&[l_a.negate(), l_b.clone()]).unwrap();
		}
	}
}

fn ord_le_ord<Lit: Literal, DB: ClauseDatabase<Lit = Lit> + ?Sized, PC: PositiveCoefficient>(
	db: &mut DB,
	a: &HashMap<PC, Lit>,
	b: &mut HashMap<PC, Lit>,
) {
	for (w_a, l_a) in a.iter() {
		let l_b = b.entry(*w_a).or_insert_with(|| db.new_var());
		db.add_clause(&[l_a.negate(), l_b.clone()]).unwrap();
	}
}

/// Build a totalizer (binary) tree and return the top node
fn build_totalizer<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	mut layer: Vec<HashMap<PC, Lit>>,
	db: &mut DB,
	_l: PC,
	u: PC,
) -> HashMap<PC, Lit> {
	if layer.len() == 1 {
		layer.pop().unwrap()
	} else {
		build_totalizer(
			layer
				.chunks(2)
				.map(|children| {
					if children.len() == 1 {
						return children[0].clone();
					}
					// merge two adjacent nodes of the current layer into one parent node
					// any child lit implies the parent lit with the same value
					let mut parent = HashMap::new();
					let (left, right) = (&children[0], &children[1]);
					ord_le_ord(db, left, &mut parent);
					ord_le_ord(db, right, &mut parent);
					ord_plus_ord_le_ord(db, left, right, &mut parent, u);
					parent
				})
				.collect(),
			db,
			_l,
			u,
		)
	}
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
