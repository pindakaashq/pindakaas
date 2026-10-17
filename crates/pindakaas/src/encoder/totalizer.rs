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
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		count::Count,
		int_linear::{
			decompose_setters, lit_terms, sum_values, term_max, term_min, Decompose,
			DecomposeConfig, NormalizedIntLinear, Term,
		},
		int_ternary::IntTernary,
		linear::{Comparator, PosCoeff},
	},
	helpers::fold_pairwise,
	ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

/// A balanced tree of partial sums (totalizer, GTE, or GGT).
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
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct TotalizerEncoder {
	config: DecomposeConfig,
}

impl TotalizerEncoder {
	/// Sum `leaves` up a balanced binary tree whose top is `root`, with no
	/// intermediate reaching past `most`.
	fn tree(
		&self,
		leaves: Vec<Term>,
		cmp: Comparator,
		most: Coeff,
		root: &Term,
	) -> Result<Vec<IntTernary>, Unsatisfiable> {
		let mut cons = Vec::new();
		let _ = fold_pairwise(leaves, |i, at_root, left, right| {
			if at_root {
				cons.push(IntTernary::new(left, right, cmp, root.clone()));
				return Ok(root.clone());
			}
			let domain = sum_values(&left, &right, most);
			if domain.is_empty() {
				return Err(Unsatisfiable);
			}
			let parent = self
				.config
				.intermediate(domain)
				.with_label(format_args!("t{i}"));
			cons.push(IntTernary::new(left, right, cmp, (1, parent.clone())));
			Ok((1, parent))
		})?;
		Ok(cons)
	}

	decompose_setters!();
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
		let k = con.k();
		// Heuristic: start from the narrowest, so the wide terms meet late and
		// the intermediates below them stay small.
		let leaves = con
			.signed_terms()
			.sorted_by_key(|t| term_max(t) - term_min(t))
			.collect_vec();
		let root = self
			.config
			.intermediate(RangeList::from(k..=k))
			.with_label("t0");
		self.tree(leaves, con.cmp().into(), k, &(1, root))
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

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for TotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &Count) -> Result {
		if con.lits.len() < 2 {
			// A tree needs two leaves to put the count on top of.
			let con = con.as_int_linear(db)?;
			return self.encode(db, &con);
		}
		// The count is the top of the tree rather than one more term in it,
		// which would widen every intermediate above where it joins.
		let leaves = lit_terms(db, con.lits.iter().map(|&l| (l, PosCoeff::new(1))))?
			.into_iter()
			.map(|(c, x)| (*c, x))
			.collect_vec();
		let Ok(cons) = self.tree(leaves, con.cmp.into(), con.y.max(), &(1, con.y.clone())) else {
			return db.contradiction();
		};
		let encoder = self.config.encoder();
		cons.iter().try_for_each(|con| encoder.encode(db, con))
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, NormalizedBoolLinear> for TotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
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
		self.config.encoder().encode_decomposed(db, con, self)
	}
}

#[cfg(test)]
mod tests {
	use itertools::iproduct;
	use rangelist::RangeList;

	use crate::{
		constraint::count::Count,
		decision::integer::IntVar,
		helpers::tests::{assert_count_admits, linear_test_suite, prelude::*},
	};

	#[test]
	fn a_count_is_the_top_of_its_tree() {
		// As one more term the count joined at the bottom of the tree for an
		// odd number of literals, and 15 of them cost more than 16.
		let mut vars = Vec::new();
		for n in [15, 16] {
			let mut cnf = Cnf::default();
			let lits = (0..n).map(|_| cnf.new_lit()).collect_vec();
			let con = Count::new(lits, LimitComp::Equal, IntVar::new(0..=n));
			TotalizerEncoder::default().encode(&mut cnf, &con).unwrap();
			vars.push(cnf.num_vars());
		}
		assert!(vars[0] < vars[1], "{vars:?}");
	}

	#[test]
	fn a_count_on_top_admits_what_the_constraint_does() {
		let domains = [
			RangeList::from(0..=5),
			RangeList::from(2..=3),
			RangeList::from(-1..=9),
			RangeList::from_elements([0, 2, 5]),
		];
		for (n, domain, cmp) in
			iproduct!([2, 3, 4, 5], domains, [LimitComp::LessEq, LimitComp::Equal])
		{
			assert_count_admits(n, domain, cmp, |cnf, con| {
				TotalizerEncoder::default().encode(cnf, con)
			});
		}
	}

	card1_test_suite! {
		totalizer_encoder_card1, TotalizerEncoder::default()
	}
	linear_test_suite!(totalizer_encoder, TotalizerEncoder::default());

	linear_test_suite!(
		totalizer_encoder_no_prop,
		TotalizerEncoder::default().with_propagation(false)
	);
}
