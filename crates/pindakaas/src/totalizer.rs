#![allow(unused_variables, dead_code, unused_imports)]
use crate::helpers::encode_xor;
use crate::{
	ClauseDatabase, ClauseSink, Comparator, Literal, PositiveCoefficient, Result, Unsatisfiable,
};
// use itertools::Itertools;
use std::collections::HashMap;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≷ k using a totalizer
pub fn encode_bool_lin_totalizer<
	Lit: Literal,
	DB: ClauseDatabase<Lit = Lit> + ?Sized,
	PC: PositiveCoefficient,
>(
	db: &mut DB,
	pair: &HashMap<Lit, PC>,
	cmp: Comparator,
	k: PC,
) -> Result {
	debug_assert!(cmp == Comparator::LessEq);

	// Every layer of the totalizer (binary) tree has nodes containing literals associated with (unique) values (which equal to the sum so far)
	let mut layer: Vec<HashMap<PC, Lit>> = pair
		.iter()
		.map(|(lit, coef)| HashMap::from([(coef.clone(), lit.clone())]))
		.collect();

	while layer.len() > 1 {
		// merge two adjacent nodes of the current layer into one parent node
		layer = layer
			.chunks(2)
			.map(|children| {
				let mut parent = HashMap::new();

				// any child lit implies the parent lit with the same value
				for c in children[0].iter().chain(children[1].iter()) {
					let p = parent.entry(*c.0).or_insert(db.new_var());
					db.add_clause(&[c.1.negate(), p.clone()]).unwrap();
				}

				// two children lits imply the parent lit with the sum of their values
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
	// This lit is guarantueed to exists, since all node values are capped at k+1, and the constraint is non-trivial
	let root_gt_k = layer[0].get(&(k+PC::one()))
        .expect("If no lit exists with value k+1 in the root node of the totalizer, the constraint was trivially satisfiable");
	db.add_clause(&[root_gt_k.negate()])?;

	Ok(())
}
