use crate::int::{Consistency, Lin};
use crate::{
	int::{IntVarOrd, Model},
	ClauseDatabase, Coefficient, Encoder, Linear, Result,
};
use itertools::Itertools;
use std::cell::RefCell;
use std::rc::Rc;

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight Counter (SWC)
#[derive(Clone, Default)]
pub struct SwcEncoder<C: Coefficient> {
	add_consistency: bool,
	cutoff: Option<C>,
}

impl<C: Coefficient> SwcEncoder<C> {
	pub fn add_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}
	pub fn add_cutoff(&mut self, c: Option<C>) -> &mut Self {
		self.cutoff = c;
		self
	}
}

impl<DB: ClauseDatabase, C: Coefficient> Encoder<DB, Linear<DB::Lit, C>> for SwcEncoder<C> {
	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&mut self, db: &mut DB, lin: &Linear<DB::Lit, C>) -> Result {
		// self.cutoff = -C::one();
		// self.add_consistency = true;
		let mut model = Model::new();
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.map(|(i, part)| {
				Rc::new(RefCell::new(
					model.add_int_var_enc(
						IntVarOrd::from_part_using_le_ord(
							db,
							part,
							lin.k.clone(),
							format!("x_{i}"),
						)
						.into(),
					),
				))
			})
			.collect::<Vec<_>>();
		let n = xs.len();

		// TODO not possible to fix since both closures use db?
		#[allow(clippy::needless_collect)] // TODO no idea how to avoid collect
		let ys = std::iter::once(model.new_constant(C::zero()))
			.chain(
				(1..n)
					.map(|_| {
						model.new_var(
							num::iter::range_inclusive(-*lin.k, C::zero()).collect(),
							self.add_consistency,
						)
					})
					.take(n),
			)
			.collect::<Vec<_>>()
			.into_iter()
			.chain(std::iter::once(model.new_constant(-*lin.k)))
			.map(|y| Rc::new(RefCell::new(y)))
			.collect::<Vec<_>>();

		ys.into_iter()
			.tuple_windows()
			.zip(xs.into_iter())
			.for_each(|((y_curr, y_next), x)| {
				model
					.cons
					.push(Lin::tern(x, y_next, lin.cmp.clone(), y_curr));
			});

		model.propagate(Consistency::Bounds, vec![model.cons.len() - 1]);
		model.encode(db)
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

	linear_test_suite!(SwcEncoder::default());
	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
}
