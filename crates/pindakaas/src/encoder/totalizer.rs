//! Encoding a linear constraint as a balanced tree of partial sums.
//!
//! Each internal node holds the sums its two children can reach between them,
//! with anything past the bound dropped.

use itertools::Itertools;
use rangelist::RangeList;

use crate::{
	constraint::{
		bool_linear::Comparator,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		int_linear::{
			term_max, term_min, term_values, Decompose, IntLinConfig, IntLinEncoder,
			NormalizedIntLinear, TernaryIntLinear,
		},
	},
	decision::integer::{Consistency, IntVar},
	ClauseDatabase, Coeff, Encoder, Result, Unsatisfiable,
};

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized
/// Totalizer (GT)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TotalizerEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

impl Default for TotalizerEncoder {
	/// Narrowing the domains before encoding is worth doing: it is what keeps
	/// the intermediate sums of a decomposition small, and turning it off can
	/// cost several times the clauses.
	fn default() -> Self {
		Self {
			add_consistency: false,
			add_propagation: Consistency::Bounds,
			cutoff: None,
		}
	}
}

impl TotalizerEncoder {
	/// The encoder of the pieces this one decomposes a constraint into.
	fn encoder(&self) -> IntLinEncoder {
		IntLinEncoder::with_config(IntLinConfig {
			propagate: self.add_propagation != Consistency::None,
			cutoff: self.cutoff,
		})
	}

	/// Set whether to add consistency constraints on the intermediate integer
	/// variables.
	pub fn with_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	/// Set the largest domain size for which the intermediate integer variables
	/// are encoded using order encoding.
	pub fn with_cutoff(&mut self, c: Option<Coeff>) -> &mut Self {
		self.cutoff = c;
		self
	}

	/// Set whether to perform additional propagation of the linear constraint
	/// before encoding the constraint into CNF.
	pub fn with_propagation(&mut self, c: Consistency) -> &mut Self {
		self.add_propagation = c;
		self
	}
}

impl Decompose for TotalizerEncoder {
	/// Sum the terms up a balanced binary tree, so that no intermediate holds
	/// more than half of them and none is wider than the terms beneath it can
	/// reach.
	fn decompose<Db: ClauseDatabase + ?Sized>(
		&self,
		_db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<Vec<TernaryIntLinear>, Unsatisfiable> {
		// Two terms or fewer are already as small as the tree would make them.
		if let Some(addition) = con.as_ternary() {
			return Ok(vec![addition]);
		}
		let (cmp, k) = (Comparator::from(con.cmp()), con.k());
		let mut cons = Vec::new();
		// Start from the narrowest, so that the wide terms meet late and the
		// intermediates below them stay small.
		let mut layer = con
			.terms()
			.iter()
			.map(|(c, x)| (**c, x.clone()))
			.sorted_by_key(|t| term_max(t) - term_min(t))
			.collect_vec();

		while layer.len() > 1 {
			let at_root = layer.len() == 2;
			let mut next = Vec::with_capacity(layer.len().div_ceil(2));
			for (i, pair) in layer.chunks(2).enumerate() {
				match pair {
					// An odd one out waits for the next layer.
					[t] => next.push(t.clone()),
					[left, right] => {
						// The root is what the constraint compares; below it an
						// intermediate reaches what its two terms reach
						// together, less anything already past the bound.
						let domain: RangeList<Coeff> = if at_root {
							RangeList::from(k..=k)
						} else {
							term_values(left)
								.into_iter()
								.cartesian_product(term_values(right))
								.map(|(a, b)| a + b)
								.filter(|&d| d <= k)
								.map(|d| d..=d)
								.collect()
						};
						if domain.is_empty() {
							return Err(Unsatisfiable);
						}
						let parent = IntVar::new(domain)
							.enforce_consistency(self.add_consistency)
							.with_label(format!("t{i}"));
						cons.push(TernaryIntLinear::new(
							left.clone(),
							right.clone(),
							cmp,
							(1, parent.clone()),
						));
						next.push((1, parent));
					}
					_ => unreachable!("terms are taken two at a time"),
				}
			}
			layer = next;
		}
		Ok(cons)
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for TotalizerEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		self.encoder().encode_decomposed(db, con, self)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for TotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for TotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

#[cfg(test)]
mod tests {
	use crate::helpers::tests::{linear_test_suite, prelude::*};

	card1_test_suite! {
		totalizer_encoder_card1, TotalizerEncoder::default()
	}
	linear_test_suite!(totalizer_encoder, TotalizerEncoder::default());

	// Test propagation feature
	linear_test_suite!(
		totalizer_encoder_prop_bounds,
		TotalizerEncoder::default().with_propagation(crate::decision::integer::Consistency::Bounds)
	);

	linear_test_suite!(
		totalizer_encoder_prop_doms,
		TotalizerEncoder::default().with_propagation(crate::decision::integer::Consistency::Domain)
	);
}
