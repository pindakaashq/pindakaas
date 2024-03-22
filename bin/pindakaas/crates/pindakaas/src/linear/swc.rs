use crate::int::{Consistency, Decompose, Lin, Model, Term};
use crate::{int::IntVarEnc, ClauseDatabase, Coefficient, Encoder, Linear, Result};
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

		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)] // TODO no idea how to avoid collect
		let ys = std::iter::once(model.new_constant(C::zero()))
			.chain(
				(1..n)
					.flat_map(|i| {
						let dom = num::iter::range_inclusive(-lin.k, C::zero()).collect::<Vec<_>>();
						model.new_var(&dom, self.add_consistency, None, Some(format!("swc_{}", i)))
					})
					.take(n),
			)
			.collect::<Vec<_>>()
			.into_iter()
			.chain(std::iter::once(model.new_constant(-lin.k)))
			.map(Term::from)
			.collect::<Vec<_>>();

		ys.into_iter()
			.tuple_windows()
			.zip(xs)
			.for_each(|((y_curr, y_next), x)| {
				model.cons.push(Lin::tern(x, y_next, lin.cmp, y_curr, None));
			});

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
			.flat_map(|(i, part)| IntVarEnc::from_part(db, part, lin.k.clone(), format!("x_{i}")))
			.map(|x| (model.add_int_var_enc(x).map(Term::from)))
			.collect::<Result<Vec<_>>>()?;

		let decomposition = self.decompose(
			Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None),
			model.num_var,
			&model.config,
		)?;
		model.extend(decomposition);
		model.encode(db)?;
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
