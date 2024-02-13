use crate::int::Consistency;
use crate::int::Decompose;
use crate::int::IntVar;
use crate::int::Lin;
use crate::int::Model;
use crate::int::Term;
use crate::Comparator;
use crate::Literal;
use crate::ModelConfig;
use crate::Unsatisfiable;

use itertools::Itertools;

use crate::{ClauseDatabase, Coefficient, Encoder, Linear, Result};

const EQUALIZE_INTERMEDIATES: bool = false;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized Totalizer (GT)
#[derive(Clone, Default)]
pub struct TotalizerEncoder<C: Coefficient> {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<C>,
}

impl<C: Coefficient> TotalizerEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_propagation(&mut self, c: Consistency) -> &mut Self {
		self.add_propagation = c;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<C>) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for TotalizerEncoder<C> {
	fn decompose(
		&mut self,
		lin: Lin<Lit, C>,
		num_var: usize,
		model_config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		let mut model = Model::<Lit, C>::new(num_var, model_config);

		let mut layer = lin.exp.terms.iter().cloned().collect_vec();

		let mut i = 0;

		while layer.len() > 1 {
			let mut next_layer = Vec::new();
			// let lin_ub = layer.iter().map(|x| x.ub()).reduce(C::add).unwrap();
			for (j, children) in layer.chunks(2).enumerate() {
				match children {
					[x] => {
						next_layer.push(x.clone());
					}
					[left, right] => {
						let at_root = layer.len() == 2;
						let dom = if at_root {
							vec![lin.k]
						} else {
							// let lb = lin.k - (lin_ub - left.ub() - right.ub()) - C::one();
							left.dom()
								.into_iter()
								.cartesian_product(right.dom().into_iter())
								.map(|(a, b)| a + b)
								// .filter(|d| {
								// 	lin.cmp.split().into_iter().all(|cmp| match cmp {
								// 		Comparator::LessEq => d <= &lin_ub,
								// 		Comparator::GreaterEq => d >= &lb,
								// 		_ => unreachable!(),
								// 	})
								// })
								.sorted()
								.dedup()
								.collect::<Vec<_>>()
						};
						let parent = model.new_var(
							&dom,
							model.config.add_consistency,
							None,
							Some(format!("gt_{}_{}", i, j)),
						)?;

						let con = Lin::tern(
							left.clone(),
							right.clone(),
							if !at_root && EQUALIZE_INTERMEDIATES {
								Comparator::Equal
							} else {
								lin.cmp
							},
							parent.clone().into(),
							Some(format!("gt_{}_{}", i, j)),
						);

						// con.propagate(&Consistency::Bounds)?;
						model.add_constraint(con)?;
						next_layer.push(parent.into());
					}
					_ => panic!(),
				}
			}
			layer = next_layer;
			i += 1;
		}

		Ok(model)
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for TotalizerEncoder<C> {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		// TODO move options from encoder to model config?
		let mut model = Model {
			config: ModelConfig {
				cutoff: self.cutoff,
				propagate: self.add_propagation.clone(),
				add_consistency: self.add_consistency,
				..ModelConfig::default()
			},
			..Model::default()
		};

		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				IntVar::from_part(db, &mut model, part, lin.k.clone(), format!("x_{i}"))
					.map(Term::from)
			})
			.collect::<Result<Vec<_>>>()?;

		let xs = xs.into_iter().sorted_by_key(Term::ub).collect_vec();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		let decomposition = self.decompose(
			Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None),
			model.num_var,
			&model.config,
		)?;
		model.extend(decomposition);
		model.encode(db, false)?;
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
		helpers::tests::{assert_sol, TestDB},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Comparator,
		Encoder,
		LinExp,
		LinearAggregator,
		LinearConstraint,
		SortedEncoder,
	};

	/*
	#[test]
	fn test_sort_same_coefficients_2() {
		use crate::linear::{LinearEncoder, StaticLinEncoder};
		use crate::{Checker, Encoder};
		let mut db = TestDB::new(5);
		let mut agg = LinearAggregator::default();
		agg.sort_same_coefficients(SortedEncoder::default(), 3);
		let mut encoder = LinearEncoder::<StaticLinEncoder<TotalizerEncoder<i32>>>::default();
		encoder.add_linear_aggregater(agg);
		let con = LinearConstraint::new(
			LinExp::new() + (1, 3) + (2, 3) + (3, 1) + (4, 1) + (5, 3),
			Comparator::GreaterEq,
			2,
		);
		assert!(encoder.encode(&mut db, &con).is_ok());
		db.with_check(|sol| {
			{
				let con = LinearConstraint::new(
					LinExp::new() + (1, 3) + (2, 3) + (3, 1) + (4, 1) + (5, 3),
					Comparator::GreaterEq,
					2,
				);
				con.check(sol)
			}
			.is_ok()
		})
		.check_complete()
	}
	*/

	linear_test_suite!(TotalizerEncoder::default().add_propagation(Consistency::None));
	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
}
