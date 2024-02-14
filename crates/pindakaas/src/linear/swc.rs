use crate::int::{Consistency, Decompose, Dom, IntVar, Lin, Model, Term};
use crate::{ClauseDatabase, Coefficient, Encoder, Linear, Result};
use crate::{Literal, ModelConfig, Unsatisfiable};
use itertools::Itertools;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
#[derive(Clone, Default)]
pub struct SwcEncoder<C: Coefficient> {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<C>,
}

impl<C: Coefficient> SwcEncoder<C> {
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

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for SwcEncoder<C> {
	fn decompose(
		&mut self,
		lin: Lin<Lit, C>,
		num_var: usize,
		model_config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		let mut model = Model::<Lit, C>::new(num_var, model_config);
		let xs = lin.exp.terms.clone();

		let n = xs.len();

		let ys = [(C::zero(), C::zero())]
			.into_iter()
			.chain(
				lin.exp
					.terms
					.iter()
					.map(|term| (term.lb(), term.ub()))
					.take(n - 1)
					.scan((C::zero(), C::zero()), |state, (lb, ub)| {
						*state = (state.0 - ub, state.1 - lb);
						Some(*state)
					}),
			)
			.chain([(-lin.k, -lin.k)])
			.enumerate()
			.map(|(i, (lb, ub))| {
				model
					.new_var_from_dom(
						Dom::from_bounds(lb, ub),
						model.config.add_consistency,
						None,
						Some(format!("swc_{}", i)),
					)
					.unwrap()
			})
			.map(Term::from)
			.collect::<Vec<_>>();

		ys.into_iter()
			.tuple_windows()
			.zip(xs)
			.for_each(|((y_curr, y_next), x)| {
				model.cons.push(Lin::tern(x, y_next, lin.cmp, y_curr, None));
			});

		// TODO !!
		// model.propagate(&Consistency::Bounds)?;

		Ok(model)
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for SwcEncoder<C> {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
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
	#[cfg(feature = "trace")]
	use traced_test::test;

	use super::*;
	use crate::{
		helpers::tests::assert_sol,
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp,
		},
		Encoder,
	};

	linear_test_suite!(SwcEncoder::default().add_propagation(Consistency::None));
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
