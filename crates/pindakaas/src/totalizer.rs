use crate::{ClauseDatabase, Comparator, Literal, Part, PositiveCoefficient, Result};
use itertools::{Itertools, Position};
use std::collections::HashMap;

#[allow(dead_code)]
#[derive(Debug)]
pub enum Structure {
	Gt,
	Swc,
	Bdd,
}

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a totalizer
pub fn encode_bool_lin_le_totalizer<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	partition: &[Part<Lit, PC>],
	cmp: Comparator,
	k: PC,
) -> Result {
	totalize(db, partition, cmp, k, Structure::Gt)
}

pub fn totalize<Lit: Literal, DB: ClauseDatabase<Lit = Lit> + ?Sized, PC: PositiveCoefficient>(
	db: &mut DB,
	partition: &[Part<Lit, PC>],
	cmp: Comparator,
	k: PC,
	structure: Structure,
) -> Result {
	debug_assert!(cmp == Comparator::LessEq);
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
					None,
				);
			}
		}
	};

	let leaves = partition.iter().map(construct_leaf).collect();
	// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

	match structure {
		// Gt = { Tree structure, one false root node, no consistency on partial sum, sparse nodes }
		Structure::Gt => {
			// The totalizer encoding constructs a binary tree starting from a layer of leaves
			let root = build_totalizer(leaves, db, PC::zero(), k + PC::one(), None);
			// Then, the k+1'th root node variable is set to false
			db.add_clause(&[root.get(&(k+PC::one()))
                .expect("If no lit exists with value k+1 in the root node of the totalizer, the constraint was trivially satisfiable").negate()]).unwrap()
		}
		// Swc = { Sequential structure, all nodes constrained (/ pushing down clauses?), with consistency on partial sum, full nodes }
		Structure::Swc => {
			// Every counter s_i has k outputs, with those of s_0 set to false
			let f = db.new_var(); // TODO probably avoidable to create a false lit for this initial layer
			db.add_clause(&[f.negate()])?;
			// TODO nightly Step trait feature; replace with stable somehow
			let s_0 = HashMap::<PC, Lit>::from_iter((PC::zero()..=k).map(|k| (k, f.clone())));
			leaves.into_iter().fold(s_0, |acc, leaf| {
				for (coef, lit) in leaf.iter() {
					// TODO currently panicking on underflows for some test cases; normalization should have prevented coef>k+1
					db.add_clause(&[lit.negate(), acc[&(k + PC::one() - *coef)].negate()])
						.unwrap();
				}
				let acc = build_totalizer(vec![acc, leaf], db, PC::zero(), k, None);

                // every counter has consistency constraints
				acc.keys()
					.sorted()
					.tuple_windows()
					.for_each(|(a, b)| db.add_clause(&[acc[b].negate(), acc[a].clone()]).unwrap());
				acc
			});
		}
		// Bdd = { Sequential structure, only root node constrained (in some way), no consistency on partial sum, sparse nodes } + reduction construction algs
		Structure::Bdd => {
			let v_r = db.new_var(); // the "root" path node
			let v_f = db.new_var(); // the 0-terminal node
			let v_t = db.new_var(); // the 1-terminal node

			// TODO still need to prevent leaf->v
			// TODO still need to figure out 'long edges'

			leaves.into_iter().with_position().fold(
				HashMap::<PC, Lit>::from_iter(std::iter::once((PC::zero(), v_r.clone()))),
				|acc, leaf| {
					// the last layer should only contain the 0- and 1-terminal nodes
					let parent = match leaf {
						Position::Last(_) => Some(HashMap::<PC, Lit>::from_iter(
							(PC::zero()..=k)
								.map(|k| (k, v_t.clone()))
								.chain(std::iter::once((k + PC::one(), v_f.clone()))),
						)),
						_ => None,
					};

					build_totalizer(
						vec![acc, leaf.into_inner()],
						db,
						PC::zero(),
						k + PC::one(),
						parent,
					)
				},
			);

			db.add_clause(&[v_r])?;
			db.add_clause(&[v_f.negate()])?;
			db.add_clause(&[v_t])?;
		}
	};
	Ok(())
}

/// Build a totalizer (binary) tree and return the top node
fn build_totalizer<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	mut layer: Vec<HashMap<PC, Lit>>,
	db: &mut DB,
	l: PC,
	u: PC,
	parent: Option<HashMap<PC, Lit>>,
) -> HashMap<PC, Lit> {
	loop {
		// Fix case of odd number of leaf nodes; by adding an empty right-hand node, we will get a correct parent node
		if layer.len() % 2 == 1 {
			layer.push(HashMap::new());
		}

		// merge two adjacent nodes of the current layer into one parent node
		layer = layer
			.chunks(2)
			.map(|children| {
				// TODO if !right.is_empty(), return left (or chain left to this iff odd or something  ..)
				let mut parent = HashMap::new();
				let (left, right) = (&children[0], &children[1]);

				// any child lit implies the parent lit with the same value
				for c in left.iter().chain(right.iter()) {
					let w = std::cmp::min(*c.0, u + PC::one()); // not capped in literature, but should be slightly better
					let p = parent.entry(w).or_insert_with(|| db.new_var());
					// TODO we do not need to create nodes where w<l (but current vars need to be passed on)
					db.add_clause(&[c.1.negate(), p.clone()]).unwrap();
				}

				// two lits together imply the parent lit with the sum of their values
				// TODO can be optimised if by sorting both children by value
				for a in left {
					for b in right {
						let w = std::cmp::min(*a.0 + *b.0, u);
						let p = parent.entry(w).or_insert_with(|| db.new_var());
						// TODO figure out what to do if w<l here as well.
						db.add_clause(&[a.1.negate(), b.1.negate(), p.clone()])
							.unwrap();
					}
				}

				parent
			})
			.collect();

<<<<<<< HEAD
		if layer.len() == 1 {
			return layer.pop().unwrap();
		}
=======
					// any child lit implies the parent lit with the same value
					let mut parent = parent.clone().unwrap_or_default();
					for (w, lit) in left.iter().chain(right.iter()) {
						let p = parent.entry(*w).or_insert_with(|| db.new_var());
						// TODO we do not need to create nodes where w<l (but current vars need to be passed on)
						db.add_clause(&[lit.negate(), p.clone()]).unwrap();
					}

					// two lits together imply the parent lit with the sum of their values
					// TODO can be optimised if by sorting both children by value
					for (w_a, l_a) in left.iter() {
						for (w_b, l_b) in right.iter() {
							let w = std::cmp::min(*w_a + *w_b, u);
							let p = parent.entry(w).or_insert_with(|| db.new_var());
							// TODO figure out what to do if w<l here as well.
							db.add_clause(&[l_a.negate(), l_b.negate(), p.clone()])
								.unwrap();
						}
					}

					parent
				})
				.collect(),
			db,
			_l,
			u,
			None,
		)
>>>>>>> 0d676a7 (Add BDD encoder using totalizers)
	}
}

}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::TestDB;

	#[test]
	fn test_totalizer_encode_amo() {
		let mut db = TestDB::new(8)
		// .with_check(|sol| {
		// 	check_pb(
		// 		&vec![2, 3, 4, 5, 3, 4, 6, 8],
		// 		&vec![1, 2, 3, 4, 5, 6, 7, 8],
		// 		Comparator::LessEq,
		// 		10,
		// 		sol,
		// 	)
		// })
		;
		assert!(encode_bool_lin_le_totalizer(
			&mut db,
			&[
				Part::Amo(vec![(1, 2), (2, 3), (3, 4), (4, 5)],),
				Part::Amo(vec![(5, 3), (6, 4), (7, 6), (8, 8)],)
			],
			Comparator::LessEq,
			10 as u32
		)
		.is_ok());
		db.check_complete();
	}
	#[test]
	fn test_totalizer_encode_ic() {
		let mut db = TestDB::new(8)
		// .with_check(|sol| {
		// 	check_pb(
		// 		&vec![2, 3, 4, 5, 3, 4, 6, 8],
		// 		&vec![1, 2, 3, 4, 5, 6, 7, 8],
		// 		Comparator::LessEq,
		// 		10,
		// 		sol,
		// 	)
		// })
		;
		assert!(encode_bool_lin_le_totalizer(
			&mut db,
			&[
				Part::Amo(vec![(1, 2), (2, 3), (3, 4), (4, 5)],),
				Part::Amo(vec![(5, 3), (6, 4), (7, 6), (8, 8)],)
			],
			Comparator::LessEq,
			10 as u32
		)
		.is_ok());
		db.check_complete();
	}
}
