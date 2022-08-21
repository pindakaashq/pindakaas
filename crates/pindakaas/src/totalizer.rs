#![allow(unused_variables, dead_code, unused_imports)]
use crate::helpers::encode_xor;
use crate::{
	ClauseDatabase, ClauseSink, Comparator, Literal, PositiveCoefficient, Result, Unsatisfiable,
};
// use itertools::Itertools;
use std::collections::HashMap;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a totalizer
pub fn encode_bool_lin_le_totalizer<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	groups: &Vec<(&HashMap<Lit, PC>, &Option<crate::Constraint>)>,
	cmp: Comparator,
	k: PC,
) -> Result {
	debug_assert!(cmp == Comparator::LessEq);

	// Every layer of the totalizer (binary) tree has nodes containing literals associated with (unique) values (which equal to the sum so far)

	// TODO assert no duplicate coefs in AMO's (not relevant to handle for the moment)
	let mut layer: Vec<HashMap<PC, Lit>> = groups
		.iter()
		.map(|(pairs, constraint)| match constraint {
			Some(crate::Constraint::AMO) => pairs
				.iter()
				.map(|(lit, coef)| (coef.clone(), lit.clone()))
				.collect(),
			Some(crate::Constraint::IC) => todo!(),
			None => todo!(),
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
					let p = parent.entry(w).or_insert(db.new_var());
					db.add_clause(&[c.1.negate(), p.clone()]).unwrap();
				}

				// two lits together imply the parent lit with the sum of their values
				// TODO can be optimised if by sorting both children by value
				for l in &children[0] {
					for r in &children[1] {
						let w = std::cmp::min(*l.0 + *r.0, k + PC::one());
						let p = parent.entry(w).or_insert(db.new_var());
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
	fn test_totalizer_encode() {
		let mut two = TestDB { nr: 3, db: vec![] };
		assert!(encode_bool_lin_le_totalizer(
			&mut two,
			&vec![
				(
					&HashMap::from_iter([(1, 2), (2, 3), (3, 4), (4, 5)]),
					&Some(crate::Constraint::AMO)
				),
				(
					&HashMap::from_iter([(5, 3), (6, 4), (7, 6), (8, 8)]),
					&Some(crate::Constraint::AMO)
				)
			],
			Comparator::LessEq,
			usize::try_from(10).unwrap()
		)
		.is_ok());
	}
}
