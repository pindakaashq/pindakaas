use std::collections::HashMap;

// TODO rename to gt.rs
use itertools::Itertools;

pub(crate) use crate::int::IntVar;
use crate::{
	int::{
		helpers::partition_functions_approx, Consistency, Decompose, Dom, GtSort, Lin, LinExp,
		Model, Term,
	},
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
		let mut gt_card = lin
			.exp
			.terms
			.iter()
			.map(|t| t.dom2().size() as u64)
			.sum::<u64>();
		while lin.exp.size() >= 2 {
			// TODO tie-breaker on coef size?
			// println!("lin = {}", lin);

			// if i > 0 {
			// 	let ub = lin.exp.ub();
			// 	lin.exp.terms.iter_mut().for_each(|t| {
			// 		let t_ub = t.ub();
			// 		t.x.borrow_mut().ge(lin.k - (ub - t_ub));
			// 	});
			// }

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
							type EdgeWeight = i128;
							let n = lin.exp.terms.len();
							let big_m = (0..n)
								.flat_map(|i| {
									((i + 1)..n).map(move |j| {
										(i, j)
										// &lin.exp.terms[i].x.borrow().dom.size()
										// 	* &lin.exp.terms[j].x.borrow().dom.size()
									})
								})
								.map(|(i, j)| (&lin.exp.terms[i], &lin.exp.terms[j]))
								// .map(|(a,b)| (a.x.borrow().dom.size() * b.x.borrow().dom.size()))
								.map(|(a, b)| (a.ub() + b.ub()))
								.max()
								.unwrap();
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
														(b, {
															let c = Dom::from_slice(
																&get_parent_dom(a, b, 0, lin.k)
																	.sorted()
																	.dedup()
																	.collect_vec(),
															);

															match *sort {
																GtSort::SCard => {
																	// let c = c.unique().count();
																	let card = c.size();

																	let u = (a.ub() - b.ub()).abs();

																	let m = (if false {
																		card
																	} else {
																		// card * big_m + (big_m - u)
																		card * big_m + u
																	}) as EdgeWeight;

																	println!(
																		"{} + {} = ({}, {u}) = {m}",
																		a, b, c
																	);
																	m
																}
																GtSort::SumsetPart => {
																	// let sumset =
																	// 	c.unique().collect_vec();
																	let sumset = c;
																	// let card = sumset.size();
																	let partition_fs =
																		sumset
                                                                        .iter()
																			.map(partition_functions_approx)
																			.sum::<f64>();
																	let partition_fs = partition_fs
																		/ sumset.size() as f64;
																	// println!(
																	// 	" pf = {partition_fs}"
																	// );
																	-partition_fs.round()
																		as EdgeWeight
																}
																GtSort::SumsetDens => {
																	// let c = c.unique().count();
																	// let card = c.size();
																	// let (lb, ub) = (
																	// 	a.lb() + b.lb(),
																	// 	a.ub() + b.ub(),
																	// );
																	// let dens = (card as f64)
																	// 	/ ((ub - lb + 1) as f64);

																	let dens = c.density();
																	(dens * 10000.0) as EdgeWeight
																}
																_ => unreachable!(),
															}
														}),
													)
												})
												.collect::<HashMap<_, _>>(),
										),
									)
								})
								.collect::<HashMap<_, _>>();

							use rustworkx_core::max_weight_matching::max_weight_matching;
							use rustworkx_core::petgraph;

							let g = petgraph::graph::UnGraph::<u32, EdgeWeight>::from_edges(
								&sumset_sizes
									.into_iter()
									.flat_map(|(i, (_, s))| {
										s.into_iter()
											.map(move |(j, (_, s_i_j))| (i as u32, j as u32, s_i_j))
									})
									.collect_vec(),
							);

							let maxc_res: hashbrown::HashSet<(usize, usize)> = max_weight_matching(
								&g,
								true,
								|e| Ok::<_, ()>(-(*e.weight())),
								true,
							)
							.unwrap();

							maxc_res
								.into_iter()
								.map(|(i, j)| (lin.exp.terms[i].clone(), lin.exp.terms[j].clone()))
								.map(|(a, b)| if a.ub() <= b.ub() { (a, b) } else { (b, a) })
								.sorted_by_key(|(a, _)| a.ub()) // unnecessary, but better output
								.flat_map(|(a, b)| [a, b])
								.collect()
						}
					},
				},
				..lin
			};

			println!("{}", lin.exp.terms.iter().map(Term::dom2).join(" + "));
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
										get_parent_dom(&left, &right, 0, lin.k)
											.sorted()
											.dedup()
											.collect()
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

			let layer_size = layer_sizes.iter().sum::<i64>();
			gt_card += layer_size as u64;
			println!(
				"{i}: layer_size = {layer_size}, layer_avg_dens = {:.2}: {:?}",
				layer_densities.iter().sum::<f64>() / lin.exp.size() as f64,
				layer_sizes
					.iter()
					.zip(layer_densities.iter().map(|d| format!("{d:.2}")))
					.collect_vec()
			);

			i += 1;
		}
		println!("{:?}: gt_card = {}", sort, gt_card);

		Ok(model)
	}
}

fn get_parent_dom(a: &Term, b: &Term, lb: Coeff, ub: Coeff) -> impl Iterator<Item = Coeff> {
	a.dom()
		.into_iter()
		.cartesian_product(b.dom().into_iter())
		.map(|(a, b)| a + b)
		.filter(move |d| &lb <= d && d <= &ub)
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
