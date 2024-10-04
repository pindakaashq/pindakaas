use std::{cell::RefCell, rc::Rc};

use itertools::Itertools;

use crate::{
	int::{Consistency, IntVarEnc, Lin, Model},
	ClauseDatabase, Coeff, Encoder, Linear, Result,
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

impl<DB: ClauseDatabase> Encoder<DB, Linear> for SwcEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut DB, lin: &Linear) -> Result {
		// self.cutoff = -1;
		// self.add_consistency = true;
		let mut model = Model::default();
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.flat_map(|(i, part)| IntVarEnc::from_part(db, part, lin.k, format!("x_{i}")))
			.map(|x| Rc::new(RefCell::new(model.add_int_var_enc(x))))
			.collect_vec();
		let n = xs.len();

		let ys = std::iter::once(model.new_constant(0))
			.chain(
				(1..n)
					.map(|_| model.new_var((-(*lin.k)..=0).collect(), self.add_consistency))
					.take(n),
			)
			.collect_vec()
			.into_iter()
			.chain(std::iter::once(model.new_constant(-*lin.k)))
			.map(|y| Rc::new(RefCell::new(y)))
			.collect_vec();

		ys.into_iter()
			.tuple_windows()
			.zip(xs)
			.for_each(|((y_curr, y_next), x)| {
				model
					.cons
					.push(Lin::tern(x, y_next, lin.cmp.clone(), y_curr));
			});

		model.propagate(&self.add_propagation, vec![model.cons.len() - 1]);
		model.encode(db, self.cutoff)
	}
}

#[cfg(test)]
mod tests {

	use traced_test::test;

	use super::*;
	use crate::{
		helpers::tests::{assert_solutions, expect_file},
		linear::{
			tests::{construct_terms, linear_test_suite},
			LimitComp, PosCoeff,
		},
		Cnf, Encoder,
	};

	linear_test_suite!(SwcEncoder::default());
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
