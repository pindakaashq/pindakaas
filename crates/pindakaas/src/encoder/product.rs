//! At-most-one over a two-dimensional grid, so that a literal is picked out
//! by its row and its column, each of which is an at-most-one in turn.

use std::{borrow::Cow, cmp::max, iter::once};

use itertools::Itertools;

use crate::{
	constraint::cardinality_one::CardinalityOne, encoder::pairwise::PairwiseEncoder,
	ClauseDatabase, ClauseDatabaseTools, Encoder, Lit, Result,
};

/// An encoder for an At Most One constraint that arranges the literals in a
/// grid, giving every row and every column a selector literal.
///
/// Since a literal can only be `true` when both its row and its column are
/// selected, two `true` literals would always select two rows or two columns.
/// The constraint is therefore reduced to an At Most One constraint over the
/// row selectors and one over the column selectors, which are encoded the same
/// way. This uses roughly `2·√n` additional literals, sitting between the
/// quadratic number of clauses of the [`PairwiseEncoder`] and the weaker
/// propagation of the
/// [`BitwiseEncoder`](crate::encoder::bitwise::BitwiseEncoder).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ProductEncoder {
	pairwise_cutoff: usize,
}

impl ProductEncoder {
	/// The number of literals up to which the pairwise encoding is used when no
	/// other cutoff is set.
	///
	/// The pairwise encoding takes `n·(n-1)/2` clauses and no additional
	/// literals, which remains the cheaper of the two until around seven
	/// literals.
	const DEFAULT_PAIRWISE_CUTOFF: usize = 6;

	/// The smallest cutoff at which the encoder still makes progress.
	///
	/// Two literals are laid out as a single row of two columns, so the column
	/// dimension would be just as large as the group it came from. The pairwise
	/// encoding has to take over at or below that size.
	const MINIMUM_PAIRWISE_CUTOFF: usize = 2;

	/// Set the number of literals up to which the pairwise encoding is used
	/// instead of splitting the literals over a grid.
	///
	/// Raising the cutoff trades additional clauses for fewer additional
	/// literals.
	///
	/// The cutoff must be at least two, since a group of two literals is laid
	/// out as a single row of two columns and would not get any smaller. Lower
	/// values are a mistake on the part of the caller, and are raised to two so
	/// that the encoder still terminates.
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

			// Lay the literals out in a grid that is as square as possible, filling
			// it row by row. The final row is allowed to be partially filled.
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

			// A literal implies the selection of both the row and the column it was
			// placed in, and a selected row or column has to hold one of its
			// literals.
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
