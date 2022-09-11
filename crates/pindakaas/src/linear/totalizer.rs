use crate::{
	linear::LimitComp, linear::Part, ClauseDatabase, Encoder, Linear, Literal, PositiveCoefficient,
	Result,
};
use std::collections::HashMap;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a totalizer
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
		debug_assert!(self.lin.cmp == LimitComp::LessEq);

		// Every layer of the totalizer (binary) tree has nodes containing literals associated with (unique) values (which equal the sum so far)
		let root = build_totalizer(
			self.lin
				.terms
				.iter()
				.map(|part| {
					let terms: Vec<(PC, Lit)> = match part {
						Part::Amo(terms) => terms
							.iter()
							.map(|(lit, coef)| (*coef, lit.clone()))
							.collect(),
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
						Part::Dom(terms, k, _) => {
							// totalizer root has unique values, so just return
							return build_totalizer(
								terms
									.iter()
									.map(|(lit, coef)| HashMap::from_iter([(*coef, lit.clone())]))
									.collect(),
								db,
								*k,
							);
						}
					};

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
				})
				.collect(),
			db,
			self.lin.k,
		);

		// Set root node lit with value k+1 to false
		// The k+1 lit is guaranteed to exists, since all node values are capped at k+1, and the constraint is non-trivial
		let root_gt_k = root.get(&(self.lin.k+PC::one()))
                .expect("If no lit exists with value k+1 in the root node of the totalizer, the constraint was trivially satisfiable");
		db.add_clause(&[root_gt_k.negate()]).unwrap(); // TODO return result from this function?
		Ok(())
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
	k: PC,
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
				let mut parent = HashMap::new();
				let (left, right) = (&children[0], &children[1]);

				// any child lit implies the parent lit with the same value
				for c in left.iter().chain(right.iter()) {
					let w = std::cmp::min(*c.0, k + PC::one()); // not capped in literature, but should be slightly better
					let p = parent.entry(w).or_insert_with(|| db.new_var());
					db.add_clause(&[c.1.negate(), p.clone()]).unwrap();
				}

				// two lits together imply the parent lit with the sum of their values
				// TODO can be optimised if by sorting both children by value
				for l in left {
					for r in right {
						let w = std::cmp::min(*l.0 + *r.0, k + PC::one());
						let p = parent.entry(w).or_insert_with(|| db.new_var());
						db.add_clause(&[l.1.negate(), r.1.negate(), p.clone()])
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

#[cfg(test)]
mod tests {
	// use super::*;
	// use crate::{helpers::tests::assert_sol, Checker};

	#[test]
	fn test_totalizer_encode_amo() {
		// assert_sol!(
		// 	TotalizerEncoder,
		// 	8,
		// 	&Linear::<i32, u32> {
		// 		terms: vec![
		// 			Part::Amo(vec![(1, 2), (2, 3), (3, 4), (4, 5)],),
		// 			Part::Amo(vec![(5, 3), (6, 4), (7, 6), (8, 8)],)
		// 		],
		// 		cmp: LimitComp::LessEq,
		// 		k: 10
		// 	}
		// );
	}
	#[test]
	fn test_totalizer_encode_ic() {
		// assert_sol!(
		// 	TotalizerEncoder,
		// 	8,
		// 	&Linear::<i32, u32> {
		// 		terms: vec![
		// 			Part::Amo(vec![(1, 2), (2, 3), (3, 4), (4, 5)],),
		// 			Part::Amo(vec![(5, 3), (6, 4), (7, 6), (8, 8)],)
		// 		],
		// 		cmp: LimitComp::LessEq,
		// 		k: 10
		// 	}
		// );
	}
}
