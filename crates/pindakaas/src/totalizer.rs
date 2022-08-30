#![allow(unused_variables, dead_code, unused_imports)]
use crate::helpers::encode_xor;
use crate::{
	ClauseDatabase, ClauseSink, Comparator, Literal, Part, PositiveCoefficient, Result,
	Unsatisfiable,
};
use itertools::Itertools;
use std::collections::HashMap;

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
	debug_assert!(cmp == Comparator::LessEq);

	// Every layer of the totalizer (binary) tree has nodes containing literals associated with (unique) values (which equal the sum so far)

	// TODO assert no duplicate coefs in AMO's (not relevant to handle for the moment)
	let mut layer: Vec<HashMap<PC, Lit>> = partition
		.iter()
		.map(|part| match part {
			Part::Amo(terms) => terms
				.iter()
				.map(|(lit, coef)| (*coef, lit.clone()))
				.collect(),
			Part::Ic(terms) => {
				let mut acc = PC::zero(); // running sum
				terms
					.iter()
					.sorted_by_key(|x| x.1) // TODO IC lit partition still need to be sorted by the chain, so for now sort by coefficient
					.map(|(lit, coef)| {
						acc += *coef;
						(acc, lit.clone())
					})
					.collect()
			}
		})
		.collect();

	// TODO perhaps this single leaf node case should be detected as trivial as well
	// Fix case of one leaf node; by adding an empty right-hand node, we will get a correct root node
	if layer.len() == 1 {
		layer.push(HashMap::new());
	}

	while layer.len() > 1 {
		// merge two adjacent nodes of the current layer into one parent node
		layer = layer
			.chunks(2)
			.map(|children| {
				let mut parent = HashMap::new();

				// any child lit implies the parent lit with the same value
				for c in children[0].iter().chain(children[1].iter()) {
					let w = std::cmp::min(*c.0, k + PC::one()); // not capped in literature, but should be slightly better
					let p = parent.entry(w).or_insert_with(|| db.new_var());
					db.add_clause(&[c.1.negate(), p.clone()]).unwrap();
				}

				// two lits together imply the parent lit with the sum of their values
				// TODO can be optimised if by sorting both children by value
				for l in &children[0] {
					for r in &children[1] {
						let w = std::cmp::min(*l.0 + *r.0, k + PC::one());
						let p = parent.entry(w).or_insert_with(|| db.new_var());
						db.add_clause(&[l.1.negate(), r.1.negate(), p.clone()])
							.unwrap();
					}
				}

				parent
			})
			.collect();
	}

	// Set root node lit with value k+1 to false
	// The k+1 lit is guaranteed to exists, since all node values are capped at k+1, and the constraint is non-trivial
	let root_gt_k = layer[0].get(&(k+PC::one()))
        .expect("If no lit exists with value k+1 in the root node of the totalizer, the constraint was trivially satisfiable");
	db.add_clause(&[root_gt_k.negate()])?;

	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;

	struct TestDB {
		nr: i32,
		db: Vec<Vec<i32>>,
	}

	impl ClauseSink for TestDB {
		type Lit = i32;

		fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
			self.db.add_clause(cl)
		}
	}

	impl ClauseDatabase for TestDB {
		fn new_var(&mut self) -> Self::Lit {
			self.nr += 1;
			self.nr
		}
	}

	#[test]
	fn test_totalizer_encode_amo() {
		let mut db = TestDB { nr: 8, db: vec![] };
		assert!(encode_bool_lin_le_totalizer(
			&mut db,
			&[
				Part::Amo(HashMap::from_iter([(1, 2), (2, 3), (3, 4), (4, 5)]),),
				Part::Amo(HashMap::from_iter([(5, 3), (6, 4), (7, 6), (8, 8)]),)
			],
			Comparator::LessEq,
			usize::try_from(10).unwrap()
		)
		.is_ok());
	}
	#[test]
	fn test_totalizer_encode_ic() {
		let mut db = TestDB { nr: 8, db: vec![] };
		assert!(encode_bool_lin_le_totalizer(
			&mut db,
			&[
				Part::Amo(HashMap::from_iter([(1, 2), (2, 3), (3, 4), (4, 5)]),),
				Part::Amo(HashMap::from_iter([(5, 3), (6, 4), (7, 6), (8, 8)]),)
			],
			Comparator::LessEq,
			usize::try_from(10).unwrap()
		)
		.is_ok());
	}
}
