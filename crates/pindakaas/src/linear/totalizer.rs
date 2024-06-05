use std::collections::HashMap;

// TODO rename to gt.rs
use itertools::Itertools;

pub(crate) use crate::int::IntVar;
use crate::{
	int::{Consistency, Decompose, Dom, GtSort, Lin, LinExp, Model, Term},
	ClauseDatabase, Coeff, Decomposer, Encoder, Linear, ModelConfig, Result, Unsatisfiable,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct TotalizerEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

impl TotalizerEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_propagation(&mut self, c: Consistency) -> &mut Self {
		self.add_propagation = c;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<Coeff>) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl Decompose for TotalizerEncoder {
	fn decompose(&self, mut model: Model) -> Result<Model, Unsatisfiable> {
		assert!(model.cons.len() == 1);
		let lin = model.cons.pop().unwrap();

		let mut lin = lin.clone();
		let sort = if let Decomposer::Gt(sort) = model.config.decomposer.clone() {
			sort
		} else {
			unreachable!()
		};

		let mut i = 0;
		while lin.exp.size() >= 2 {
			// TODO tie-breaker on coef size?
			// let ub = lin.exp.ub();
			// println!("lin = {}", lin);

			// lin.propagate(&Consistency::Bounds)?;

			lin = Lin {
				exp: LinExp {
					terms: match sort.clone() {
						GtSort::Coeff => lin
							.exp
							.terms
							.iter()
							.cloned()
							.sorted_by_key(Term::ub)
							.collect(),
						_ => {
							eprintln!("{}", lin);

							let sumset_sizes = lin
								.exp
								.terms
								.iter()
								.enumerate()
								.map(|(i, a)| {
									let sort = &sort;
									(
										i,
										(
											a,
											lin.exp
												.terms
												.iter()
												.enumerate()
												.filter(|(j, _)| i != *j)
												.map(move |(j, b)| {
													(
														j,
														(
															b,
															{
																let c = a
																	.dom2()
																	.iter()
																	.cartesian_product(
																		b.dom2().iter(),
																	)
																	.map(|(a, b)| a + b)
																	.filter(|d| d <= &lin.k)
																	.unique()
																	.count();
																if sort == &GtSort::SumsetCard {
																	c as i128
																} else {
																	let (lb, ub) = (
																		a.lb() + b.lb(),
																		a.ub() + b.ub(),
																	);
																	let dens = (c as f64)
																		/ ((ub - lb + 1) as f64);
																	(dens * 10000.0) as i128
																}
															},
															// .sumset(b.dom2())
															// .iter()
															// .filter(|d| d <= &lin.k)
															// .count(),
														),
													)
												})
												.collect::<HashMap<_, _>>(),
										),
									)
								})
								.collect::<HashMap<_, _>>();

							use rustworkx_core::max_weight_matching::max_weight_matching;
							use rustworkx_core::petgraph;

							let g = petgraph::graph::UnGraph::<u32, i128>::from_edges(
								&sumset_sizes
									.into_iter()
									.flat_map(|(i, (_, s))| {
										s.into_iter()
											.map(move |(j, (_, s_i_j))| (i as u32, j as u32, s_i_j))
									})
									.collect_vec(),
							);

							use hashbrown::HashSet;
							let maxc_res: HashSet<(usize, usize)> = max_weight_matching(
								&g,
								true,
								|e| Ok::<_, ()>(-(*e.weight())),
								true,
							)
							.unwrap();

							let maxc_matching =
								maxc_res.into_iter().flat_map(|(i, j)| [i, j]).collect_vec();

							maxc_matching
								.into_iter()
								.map(|i| lin.exp.terms[i].clone())
								.collect()
						}
					},
				},
				..lin
			};

			lin = Lin {
				exp: LinExp {
					terms: lin
						.exp
						.terms
						.chunks(2)
						.enumerate()
						.map(|(j, children)| {
							match children {
								[x] => Ok(x.clone()),
								[left, right] => {
									let dom = if lin.exp.size() == 2 {
										// at root
										vec![lin.k]
									} else {
										left.dom()
											.into_iter()
											.cartesian_product(right.dom().into_iter())
											.map(|(a, b)| a + b)
											.filter(|d| d <= &lin.k)
											.sorted()
											.dedup()
											.collect::<Vec<_>>()
									};
									let parent = model.new_aux_var(
										Dom::from_slice(&dom),
										model.config.add_consistency,
										None,
										Some(format!("gt_{}_{}", i, j)),
									)?;

									let con = Lin::tern(
										left.clone(),
										right.clone(),
										lin.cmp,
										parent.clone().into(),
										Some(format!("gt_{}_{}", i, j)),
									);

									model.add_constraint(con)?;
									Ok(Term::from(parent))
								}
								_ => panic!(),
							}
						})
						.try_collect()?,
				},
				..lin
			};

			let (layer_sizes, layer_densities): (Vec<_>, Vec<_>) = lin
				.exp
				.terms
				.iter()
				.map(|x| {
					let dom = &x.x.borrow().dom;
					(dom.size(), dom.density())
				})
				.unzip();
			println!(
				"{i}: layer_size = {}, layer_avg_dens = {:.2}: {:?}",
				layer_sizes.iter().sum::<i64>(),
				layer_densities.iter().sum::<f64>() / lin.exp.size() as f64,
				layer_sizes
					.iter()
					.zip(layer_densities.iter().map(|d| format!("{d:.2}")))
					.collect_vec()
			);

			i += 1;
		}

		Ok(model)
	}
}

impl<DB: ClauseDatabase> Encoder<DB, Linear> for TotalizerEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut DB, lin: &Linear) -> Result {
		// TODO move options from encoder to model config?
		let mut model = Model {
			config: ModelConfig {
				cutoff: self.cutoff,
				propagate: self.add_propagation,
				add_consistency: self.add_consistency,
				decomposer: Decomposer::Gt(GtSort::default()),
				..ModelConfig::default()
			},
			..Model::default()
		};

		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVar::from_part(db, &mut model, part, lin.k, format!("x_{i}")).map(Term::from)
			})
			.collect::<Result<Vec<_>>>()?;

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		let mut model = self.decompose(Model {
			cons: vec![Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None)],
			..model
		})?;

		model.encode_internal(db, false)?;
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	#![allow(unused_imports)]
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		// cardinality_one::tests::card1_test_suite, CardinalityOne,
		helpers::tests::{assert_sol, lits, TestDB},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, PosCoeff,
		},
		Comparator,
		Encoder,
		LinExp,
		LinearAggregator,
		LinearConstraint,
		Lit,
	};

	/*
	#[test]
	fn test_sort_same_coefficients_2() {
		use crate::{
			linear::{LinearEncoder, StaticLinEncoder},
			Checker, Encoder,
		};
		let mut db = TestDB::new(5);
		let mut agg = LinearAggregator::default();
		agg.sort_same_coefficients(SortedEncoder::default(), 3);
		let mut encoder = LinearEncoder::<StaticLinEncoder<TotalizerEncoder>>::default();
		encoder.add_linear_aggregater(agg);
		let con = LinearConstraint::new(
			LinExp::from_slices(&[3, 3, 1, 1, 3], &lits![1, 2, 3, 4, 5]),
			Comparator::GreaterEq,
			2,
		);
		assert!(encoder.encode(&mut db, &con).is_ok());
		db.with_check(|value| {
			LinearConstraint::new(
				LinExp::from_slices(&[3, 3, 1, 1, 3], &lits![1, 2, 3, 4, 5]),
				Comparator::GreaterEq,
				2,
			)
			.check(value)
			.is_ok()
		})
		.check_complete()
	}
	*/

	linear_test_suite!(TotalizerEncoder::default().add_propagation(Consistency::None));
	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
}
