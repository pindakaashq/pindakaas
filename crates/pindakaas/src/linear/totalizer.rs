use crate::{
	int::{ord_plus_ord_le_ord, ord_plus_ord_le_ord_sparse_dom, IntVar},
	linear::LimitComp,
	new_var, ClauseDatabase, Coefficient, Encoder, Linear, PosCoeff, Result,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
#[derive(Clone, Default)]
pub struct TotalizerEncoder {
	add_consistency: bool,
}

impl TotalizerEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
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
	let leaves = lin
		.terms
		.iter()
		.map(|part| IntVar::<DB::Lit, C>::from_part_using_le_ord(db, part, lin.k.clone()))
		.collect::<Vec<_>>();

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
						v_i.iter().map(|(_, c)| *c).collect(),
						x_i.iter().map(|(_, c)| *c).collect(),
						C::zero(),
						*lin.k,
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

fn build_totalizer<DB: ClauseDatabase + ?Sized, C: Coefficient>(
	mut layer: Vec<IntVar<DB::Lit, C>>,
	db: &mut DB,
	l: PosCoeff<C>,
	u: PosCoeff<C>,
	limit_root: bool,
	add_consistency: bool,
	level: u32,
) -> IntVar<DB::Lit, C> {
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
								left.iter().map(|(_, c)| *c).collect(),
								right.iter().map(|(_, c)| *c).collect(),
								*l,
								*u,
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
