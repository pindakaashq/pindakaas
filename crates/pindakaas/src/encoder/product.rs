//! At-most-one over a two-dimensional selector grid [^1].
//!
//! Rows and columns are recursively constrained, using roughly `2·√n` auxiliary
//! literals per level. Groups of at most six use pairwise clauses; the cutoff
//! cannot be below two, where a split would stop shrinking.
//!
//! [^1]: J. Chen, "A New SAT Encoding of the At-Most-One Constraint", ModRef
//! 2010.

use std::{borrow::Cow, cmp::max, iter::once};

use itertools::Itertools;

use crate::{
	constraint::cardinality_one::CardinalityOne, encoder::pairwise::PairwiseEncoder,
	ClauseDatabase, ClauseDatabaseTools, Encoder, Lit, Result,
};

/// Recursive product at-most-one encoding.
///
/// # Examples
///
/// ```rust
/// use pindakaas::{
///     constraint::{cardinality_one::CardinalityOne, linear::LimitComp},
///     encoder::product::ProductEncoder, ClauseDatabase, Cnf, Encoder,
/// };
/// let mut cnf = Cnf::default();
/// let lits = cnf.new_var_range(20).map(Into::into).collect();
/// let constraint = CardinalityOne::new(lits, LimitComp::LessEq);
/// ProductEncoder::default().encode(&mut cnf, &constraint)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProductEncoder {
	pairwise_cutoff: usize,
}

impl ProductEncoder {
	/// The default pairwise cutoff.
	const DEFAULT_PAIRWISE_CUTOFF: usize = 6;

	/// The minimum cutoff for recursive progress.
	const MINIMUM_PAIRWISE_CUTOFF: usize = 2;

	/// Set the largest group encoded pairwise.
	///
	/// Raising the cutoff trades more clauses for fewer auxiliary literals.
	///
	/// # Panics
	///
	/// `cutoff` is less than two.
	pub fn with_pairwise_cutoff(&mut self, cutoff: usize) -> &mut Self {
		assert!(
			cutoff >= Self::MINIMUM_PAIRWISE_CUTOFF,
			"a pairwise cutoff of {cutoff} would leave the encoder unable to \
			 make progress on a group of two literals"
		);
		self.pairwise_cutoff = max(cutoff, Self::MINIMUM_PAIRWISE_CUTOFF);
		self
	}
}

impl Default for ProductEncoder {
	fn default() -> Self {
		Self {
			pairwise_cutoff: Self::DEFAULT_PAIRWISE_CUTOFF,
		}
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for ProductEncoder {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "product_encoder", skip_all, fields(constraint = card1.trace_print()))
	)]
	fn encode(&self, db: &mut Db, card1: &CardinalityOne) -> Result {
		let mut to_constain: Vec<Cow<[Lit]>> = vec![(&card1.lits).into()];
		while let Some(lits) = to_constain.pop() {
			// Heuristic: pairwise is `n·(n-1)/2` clauses and no new literals,
			// which wins up to about seven of them.
			if lits.len() <= self.pairwise_cutoff {
				PairwiseEncoder::default().encode(
					db,
					&CardinalityOne {
						lits: lits.to_vec(),
						cmp: card1.cmp.clone(),
					},
				)?;
				continue;
			}

			let cols = {
				let root = lits.len().isqrt();
				if root * root < lits.len() {
					root + 1
				} else {
					root
				}
			};
			let rows = lits.len().div_ceil(cols);

			let row_lits = (0..rows).map(|_| db.new_lit()).collect_vec();
			let col_lits = (0..cols).map(|_| db.new_lit()).collect_vec();

			for (i, &lit) in lits.iter().enumerate() {
				db.add_clause([!lit, row_lits[i / cols]])?;
				db.add_clause([!lit, col_lits[i % cols]])?;
			}
			for (&row, row_lits) in row_lits.iter().zip(lits.chunks(cols)) {
				db.add_clause(once(!row).chain(row_lits.iter().copied()))?;
			}
			for (c, &col) in col_lits.iter().enumerate() {
				db.add_clause(once(!col).chain(lits.iter().skip(c).step_by(cols).copied()))?;
			}

			// Two distinct literals differ in their row or in their column, so
			// constraining both dimensions constrains the literals themselves.
			to_constain.push(row_lits.into());
			to_constain.push(col_lits.into());
		}
		Ok(())
	}
}
