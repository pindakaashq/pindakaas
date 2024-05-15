use itertools::Itertools;

use crate::{
	int::{Consistency, Dom, Lin, Model},
	ClauseDatabase, Coeff, Decompose, Decomposer, Encoder, IntVar, Linear, ModelConfig, Result,
	Term, Unsatisfiable,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SwcEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

impl SwcEncoder {
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

impl Decompose for SwcEncoder {
	fn decompose(&self, mut model: Model) -> Result<Model, Unsatisfiable> {
		assert!(model.cons.len() == 1);
		let lin = model.cons.pop().unwrap();
		let xs = lin.exp.terms.clone();

		let n = xs.len();

		let ys = [(0, 0)]
			.into_iter()
			.chain(
				lin.exp
					.terms
					.iter()
					.map(|term| (term.lb(), term.ub()))
					.take(n - 1)
					.scan((0, 0), |state, (lb, ub)| {
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

impl<DB: ClauseDatabase> Encoder<DB, Linear> for SwcEncoder {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut DB, lin: &Linear) -> Result {
		let mut model = Model {
			config: ModelConfig {
				cutoff: self.cutoff,
				propagate: self.add_propagation,
				add_consistency: self.add_consistency,
				decomposer: Decomposer::Swc,
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

		let mut model = self.decompose(Model {
			cons: vec![Lin::new(&xs, lin.cmp.clone().into(), *lin.k, None)],
			..model
		})?;
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
		helpers::tests::{assert_sol, lits},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, PosCoeff,
		},
		Encoder, Lit,
	};

	linear_test_suite!(SwcEncoder::default().add_propagation(Consistency::None));
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
