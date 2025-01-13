use crate::{
	bool_linear::{Comparator, LinMarker, NormalizedBoolLinear},
	integer::{
		Consistency, Decompose, Decomposer, Dom, IntVar, IntVarEncHeuristic, Lin, Model,
		ModelConfig, Term,
	},
	ClauseDatabase, Encoder, Result, Unsatisfiable,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized
/// Totalizer (GT)
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct TotalizerEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: IntVarEncHeuristic,
}

use itertools::Itertools;

impl TotalizerEncoder {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_propagation(&mut self, c: Consistency) -> &mut Self {
		self.add_propagation = c;
		self
	}
	pub fn add_cutoff(&mut self, c: IntVarEncHeuristic) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl Decompose for TotalizerEncoder {
	fn decompose(&self, mut model: Model) -> Result<Model, Unsatisfiable> {
		assert!(model.cons.len() == 1);
		let lin = model.cons.pop().unwrap();

		let mut layer = lin.exp.terms.clone();

		let mut i = 0;
		while layer.len() > 1 {
			let mut next_layer = Vec::new();
			for (j, children) in layer.chunks(2).enumerate() {
				match children {
					[x] => {
						next_layer.push(x.clone());
					}
					[left, right] => {
						let at_root = layer.len() == 2;
						let dom = if at_root {
							Dom::constant(lin.k)
						} else {
							Dom::new(
								left.dom()
									.into_iter()
									.cartesian_product(right.dom().into_iter())
									.map(|(a, b)| a + b)
									.filter(|&c| {
										if matches!(lin.cmp, Comparator::LessEq | Comparator::Equal)
											&& c > lin.k - lin.exp.lb()
										{
											false
										} else {
											!(matches!(
												lin.cmp,
												Comparator::GreaterEq | Comparator::Equal
											) && c < lin.k - lin.exp.ub())
										}
									}),
								// TODO more efficient version using map_while, but needs reverse on geq case
							)
						};
						let parent = model.new_aux_var(
							dom,
							model.config.add_consistency,
							None,
							format!("{}-gt_{}_{}", lin.lbl, i, j),
						)?;

						let con = Lin::tern(
							left.clone(),
							right.clone(),
							lin.cmp,
							parent.clone().into(),
							format!("{}-gt_{}_{}", lin.lbl, i, j),
						);

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

impl LinMarker for TotalizerEncoder {}
impl<DB: ClauseDatabase> Encoder<DB, NormalizedBoolLinear> for TotalizerEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut DB, lin: &NormalizedBoolLinear) -> Result {
		// TODO move options from encoder to model config?
		let mut model = Model {
			config: ModelConfig {
				cutoff: self.cutoff.clone(),
				propagate: self.add_propagation,
				add_consistency: self.add_consistency,
				decomposer: Decomposer::Gt,
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

		let xs = xs.into_iter().sorted_by_key(Term::ub).collect_vec();

		// The totalizer encoding constructs a binary tree starting from a layer of leaves
		let mut model = self.decompose(Model {
			cons: vec![Lin::new(
				&xs,
				lin.cmp.clone().into(),
				*lin.k,
				"TODO".to_owned(),
			)],
			..model
		})?;

		_ = model.encode(db, false)?;
		Ok(())
	}
}
