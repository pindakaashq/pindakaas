use crate::{ClauseDatabase, Comparator, Literal, Part, PositiveCoefficient, Result};
use itertools::Itertools;
use std::collections::HashMap;

pub enum Structure {
	Gt,
	Swc,
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
				);
			}
		}
	};

	let leaves = partition.into_iter().map(construct_leaf).collect();
	// TODO experiment with adding consistency constraint to totalizer nodes (including on leaves!)

	let root = match structure {
		Structure::Gt => build_totalizer(leaves, db, PC::zero(), k + PC::one()),
		Structure::Swc => leaves
			.into_iter()
			.fold(HashMap::<PC, Lit>::new(), |acc, leaf| {
				let acc = build_totalizer(vec![acc, leaf], db, PC::zero(), k + PC::one());
				acc.keys()
					.sorted()
					.tuple_windows()
					.for_each(|(a, b)| db.add_clause(&[acc[b].negate(), acc[a].clone()]).unwrap());
				acc
			}),
	};

	// Set root node lit with value k+1 to false
	// The k+1 lit is guaranteed to exists, since all node values are capped at k+1, and the constraint is non-trivial
	let root_gt_k = root.get(&(k+PC::one()))
                .expect("If no lit exists with value k+1 in the root node of the totalizer, the constraint was trivially satisfiable");
	db.add_clause(&[root_gt_k.negate()]).unwrap(); // TODO return result from this function?
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

		if layer.len() == 1 {
			return layer.pop().unwrap();
		}
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
