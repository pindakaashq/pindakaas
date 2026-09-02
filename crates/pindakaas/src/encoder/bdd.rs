//! Encoding a linear constraint as the layers of a decision diagram.
//!
//! One layer per term, holding the partial sums still reachable, merged where
//! they cannot be told apart. Each layer becomes an integer variable and each
//! step between two of them a ternary constraint.

use std::{
	cmp::{max, min, Ordering},
	iter::once,
	ops::Range,
};

use itertools::Itertools;

use crate::{
	constraint::{
		bool_linear::Comparator,
		cardinality::Cardinality,
		cardinality_one::CardinalityOne,
		int_linear::{Decompose, NormalizedIntLinear, Term, term_max, term_min, term_values},
		int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
	},
	decision::integer::IntVar,
	helpers::new_named_lit,
	BoolVal, ClauseDatabase, Coeff, Encoder, Result, Unsatisfiable,
};

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// Encode the constraint that ∑ coeffᵢ·litᵢ ≦ k using a Binary
/// Decision Diagram (BDD)
pub struct BddEncoder {
	add_consistency: bool,
	cutoff: Option<Coeff>,
}

#[derive(Debug, Clone, PartialEq)]
/// The representation of a Binary Decision Diagram (BDD) node for the
/// [`BddEncoder`].
enum BddNode {
	Val,
	Gap,
	View(Coeff),
}

impl BddEncoder {
	fn bdd(
		i: usize,
		xs: &[Term],
		sum: Coeff,
		ws: &mut Vec<Vec<(Range<Coeff>, BddNode)>>,
	) -> (Range<Coeff>, BddNode) {
		// See if the node for `sum` is already available
		if let Ok(pos) = ws[i].binary_search_by(|(r, _)| {
			if r.contains(&sum) {
				Ordering::Equal
			} else if r.end <= sum {
				Ordering::Less
			} else {
				Ordering::Greater
			}
		}) {
			return ws[i][pos].clone();
		}

		let views = term_values(&xs[i])
			.into_iter()
			.map(|v| (v, Self::bdd(i + 1, xs, sum + v, ws)))
			.collect_vec();

		// TODO could we check whether a domain value of x always leads to gaps?
		let is_gap = views.iter().all(|(_, (_, v))| v == &BddNode::Gap);
		// TODO without checking actual Val identity, could we miss when the
		// next layer has two adjacent nodes that are both views on the same
		// node at the layer below?
		let view = (views.iter().map(|(_, (iv, _))| iv).all_equal())
			.then(|| views.first().unwrap().1 .0.end - 1);

		let interval = views
			.into_iter()
			.map(|(v, (interval, _))| (interval.start - v)..(interval.end - v))
			.reduce(|a, b| max(a.start, b.start)..min(a.end, b.end))
			.unwrap();

		let node = if is_gap {
			BddNode::Gap
		} else if let Some(view) = view {
			BddNode::View(view)
		} else {
			BddNode::Val
		};

		let pos = match ws[i].binary_search_by_key(&interval.start, |(r, _)| r.start) {
			Ok(i) | Err(i) => i,
		};
		ws[i].insert(pos, (interval.clone(), node.clone()));
		debug_assert!(
			pos == 0 || ws[i][pos - 1].0.end <= ws[i][pos].0.start,
			"Overlapping interval {interval:?} (overlapping with {:?}) inserted into {:?}",
			ws[i][pos - 1].0,
			ws[i]
		);
		debug_assert!(
			pos + 1 == ws[i].len() || ws[i][pos].0.end <= ws[i][pos + 1].0.start,
			"Overlapping interval {interval:?} (overlapping with {:?}) inserted into {:?}",
			ws[i][pos + 1].1,
			ws[i]
		);
		(interval, node)
	}

	fn construct_bdd(xs: &[Term], cmp: Comparator, k: Coeff) -> Vec<Vec<(Range<Coeff>, BddNode)>> {
		let bounds = xs
			.iter()
			.scan((0, 0), |state, x| {
				*state = (state.0 + term_min(x), state.1 + term_max(x));
				Some(*state)
			})
			.chain(once((0, k)))
			.collect_vec();

		let margins = xs
			.iter()
			.rev()
			.scan((k, k), |state, x| {
				*state = (state.0 - term_max(x), state.1 - term_min(x));
				Some(*state)
			})
			.collect_vec();

		let inf = xs.iter().fold(0, |a, x| a + term_max(x)) + 1;

		let mut ws: Vec<Vec<(Range<Coeff>, BddNode)>> = margins
			.into_iter()
			.rev()
			.chain(once((k, k)))
			.zip(bounds)
			.map(|((lb_margin, ub_margin), (lb, ub))| {
				match cmp {
					Comparator::LessEq => vec![
						(lb_margin > lb).then_some((0..(lb_margin + 1), BddNode::Val)),
						(ub_margin <= ub).then_some(((ub_margin + 1)..inf, BddNode::Gap)),
					],
					_ => vec![
						(lb_margin > lb).then_some((0..lb_margin, BddNode::Gap)),
						(lb_margin == ub_margin).then_some((k..(k + 1), BddNode::Val)),
						(ub_margin <= ub).then_some(((ub_margin + 1)..inf, BddNode::Gap)),
					],
				}
				.into_iter()
				.flatten()
				.collect()
			})
			.collect();
		debug_assert!(
			ws.iter().all(|layer| layer
				.iter()
				.tuple_windows()
				.all(|((a, _), (b, _))| a.end <= b.end)),
			"layers must be sorted and non-overlapping"
		);

		let _ = Self::bdd(0, xs, 0, &mut ws);
		ws
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
}

impl BddEncoder {
	/// The encoder of the pieces this one decomposes a constraint into.
	fn encoder(&self) -> IntTernaryEncoder {
		IntTernaryEncoder::with_config(IntTernaryConfig {
			cutoff: self.cutoff,
			..IntTernaryConfig::default()
		})
	}
}

impl Decompose for BddEncoder {
	/// Follow the terms one at a time, keeping a layer of the totals still
	/// worth telling apart.
	///
	/// Totals that lead to the same outcome whatever the remaining terms do are
	/// one node, so a layer holds intervals rather than values and the diagram
	/// stays narrow. Where a layer agrees with the next one from some total
	/// upwards, its literal for that total is the next layer's, which is what
	/// keeps the layers from each paying for their own.
	fn decompose<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<Vec<IntTernary>, Unsatisfiable> {
		// The narrowest terms first, which is the order the diagram is reduced
		// under in the literature. A layer then tends to agree with the one
		// after it from some total upwards, and where it does it shares that
		// literal rather than paying for one of its own. Taking the widest
		// first narrows the layers sooner but leaves nothing to share.
		let terms = con
			.terms()
			.iter()
			.map(|(c, x)| (**c, x.clone()))
			.sorted_by(|a: &Term, b: &Term| term_max(a).cmp(&term_max(b)))
			.collect_vec();
		let (cmp, k) = (Comparator::from(con.cmp()), con.k());

		// The nodes of every layer, before any of them is a variable: a total,
		// and the total of the next layer it shares its literal with.
		let nodes = Self::construct_bdd(&terms, cmp, k)
			.into_iter()
			.map(|layer| {
				layer
					.into_iter()
					.filter_map(|(interval, node)| {
						// A node stands for the largest total in its interval.
						let val = interval.end - 1;
						match node {
							BddNode::Gap => None,
							BddNode::Val => Some((val, None)),
							BddNode::View(of) => Some((val, Some(of))),
						}
					})
					.collect_vec()
			})
			.collect_vec();
		if nodes.iter().any(Vec::is_empty) {
			return Err(Unsatisfiable);
		}

		// Back to front, so that a layer has the literals it shares with the
		// next one by the time it is built. A total the next layer already
		// tells apart is read on its literal; any other gets one of its own.
		let mut layers: Vec<IntVar> = Vec::with_capacity(nodes.len());
		for (i, layer) in nodes.iter().enumerate().rev() {
			let walk = layer
				.iter()
				.enumerate()
				.map(|(j, &(val, of))| {
					Ok((
						val,
						match (j, of) {
							// The least total is always reached.
							(0, _) => BoolVal::Const(true),
							(_, Some(of)) => layers
								.last()
								.expect("only a layer with one after it shares")
								.lit_at_least(db, of)?,
							(_, None) => BoolVal::Lit(new_named_lit!(db, format!("y{i}≥{val}"))),
						},
					))
				})
				.collect::<Result<Vec<_>, Unsatisfiable>>()?;
			let y = IntVar::from_order_walk(db, walk)?
				.enforce_consistency(self.add_consistency)
				.with_label(format!("y{i}"));
			// A total that only this layer tells apart gets a literal of its
			// own, which nothing else orders against the rest.
			y.constrain(db)?;
			layers.push(y);
		}
		layers.reverse();

		Ok(terms
			.into_iter()
			.enumerate()
			.map(|(i, x)| {
				IntTernary::new((1, layers[i].clone()), x, cmp, (1, layers[i + 1].clone()))
			})
			.collect())
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for BddEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "bdd_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		self.encoder().encode_decomposed(db, con, self)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for BddEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for BddEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::helpers::tests::{linear_test_suite, prelude::*};

	#[test]
	fn bdd_layers_share_the_literals_they_agree_on() {
		// Abió, Nieuwenhuis, Oliveras and Rodríguez-Carbonell, "BDDs for
		// Pseudo-Boolean Constraints — Revisited" (SAT 2011), Examples 3 and 5.
		// Reducing this diagram skips a level: at a running total of 2, whether
		// the second term is taken makes no difference to what the third can
		// do, so that node is the one below it and reads on its literal.
		//
		// Nothing else notices — the solutions are the same either way — so the
		// saving is what has to be measured.
		let mut cnf = Cnf::default();
		let lits = cnf.new_var_range(3).iter_lits().collect_vec();
		let con = Linear::new(
			LinExp::from_slices(&[2, 3, 5], &lits),
			Comparator::LessEq,
			6,
		);
		let LinVariant::Linear(con) = BoolLinAggregator::default()
			.aggregate(&mut cnf, &con)
			.unwrap()
		else {
			panic!("three distinct coefficients aggregate to a linear constraint");
		};
		cnf.encode(&con, &crate::constraint::bool_linear::BddEncoder::default())
			.unwrap();

		assert_eq!(
			cnf.num_vars(),
			4,
			"the three terms and the one total the layers still tell apart"
		);
	}

	card1_test_suite! {
		bdd_encoder_card1, BddEncoder::default()
	}
	linear_test_suite! {bdd_encoder, BddEncoder::default()}
}
