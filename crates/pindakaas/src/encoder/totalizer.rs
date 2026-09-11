//! Encoding a linear constraint as a balanced tree of partial sums.
//!
//! Each internal node holds the sums its two children can reach between them,
//! with anything past the bound dropped.
//!
//! With unit coefficients this is the totalizer of Bailleux and Boufkhad [^1];
//! weighted, it is the generalized totalizer, GTE [^2]; and where a term
//! stands for a group of mutually exclusive literals rather than one literal,
//! it is GGT [^3]. It is *not* RGT or RGGT: the reduction that merges values a
//! parent cannot tell apart is not performed, and the tree is built by a
//! balanced heuristic rather than by minRatio. Domain consistent [^3].
//!
//! [^1]: O. Bailleux, Y. Boufkhad, "Efficient CNF Encoding of Boolean
//! Cardinality Constraints", CP 2003, LNCS 2833, 108–122.
//!
//! [^2]: S. Joshi, R. Martins, V. Manquinho, "Generalized Totalizer Encoding
//! for Pseudo-Boolean Constraints", CP 2015, LNCS 9255, 200–209.
//!
//! [^3]: M. Bofill, J. Coll, P. Nightingale, J. Suy, F. Ulrich-Oltean, M.
//! Villaret, "SAT encodings for pseudo-Boolean constraints together with
//! at-most-one constraints", Artificial Intelligence 302 (2022) 103604.

use itertools::Itertools;
use rangelist::RangeList;

use crate::{
	constraint::{
		linear::Comparator,
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		count::Count,
		cardinality_one::CardinalityOne,
		int_linear::{sum_values, term_max, term_min, Decompose, NormalizedIntLinear},
		int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
	},
	decision::integer::{Consistency, IntVar},
	ClauseDatabase, Coeff, Encoder, Result, Unsatisfiable,
};

/// Encoder for a linear constraint, decomposing it into a balanced tree of
/// partial sums; also known as the totalizer, and as the generalized totalizer
/// or GTE once the terms are weighted.
///
/// Each node holds what its two children reach between them, with anything
/// past the bound dropped. The tree keeps the intermediates narrower than the
/// chain does, at the cost of more of them.
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear}, int_linear::TotalizerEncoder,
/// #                  linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// # let mut f = Cnf::default();
/// # let (x, y) = (IntVar::new(0..=5), IntVar::new(0..=5));
/// let con = Linear::new(x * 2 + y * 3, Comparator::LessEq, 10);
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a sum of integer terms is a linear constraint");
/// };
/// TotalizerEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
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
	fn encoder(&self) -> IntTernaryEncoder {
		IntTernaryEncoder::with_config(IntTernaryConfig {
			propagate: self.add_propagation != Consistency::None,
			cutoff: self.cutoff,
		})
	}

	/// Configures whether intermediate variables are constrained independently of their use.
	pub fn with_consistency(&mut self, b: bool) -> &mut Self {
		self.add_consistency = b;
		self
	}

	/// Sets the largest intermediate domain forced into order encoding.
	///
	/// `None`, the default, leaves the choice to [`IntTernaryEncoder`].
	pub fn with_cutoff(&mut self, c: Option<Coeff>) -> &mut Self {
		self.cutoff = c;
		self
	}

	/// Selects domain consistency applied before decomposition; bounds is the default.
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
	) -> Result<Vec<IntTernary>, Unsatisfiable> {
		// Two terms or fewer are already as small as the tree would make them.
		if let Some(addition) = con.as_ternary() {
			return Ok(vec![addition]);
		}
		let (cmp, k) = (Comparator::from(con.cmp()), con.k());
		let mut cons = Vec::new();
		// Heuristic: start from the narrowest, so the wide terms meet late and
		// the intermediates below them stay small.
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
							sum_values(left, right, k)
						};
						if domain.is_empty() {
							return Err(Unsatisfiable);
						}
						let parent = IntVar::new(domain)
							.enforce_consistency(self.add_consistency)
							.with_label(format!("t{i}"));
						cons.push(IntTernary::new(
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

impl<Db> Encoder<Db, NormalizedBoolLinear> for TotalizerEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		// Decomposing works in integers, so the literals become them first.
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
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

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for TotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &Count) -> Result {
		// Counting into a variable is a linear constraint whose bound is not a
		// constant, which this encoder takes once the bound is a term.
		let con = con.as_int_linear(db)?;
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
