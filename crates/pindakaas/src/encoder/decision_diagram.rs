//! Encoding a linear constraint as the layers of a decision diagram.
//!
//! One layer per term, holding the partial sums still reachable, merged where
//! they cannot be told apart. Each layer becomes an integer variable and each
//! step between two of them a ternary constraint.
//!
//! A term is an integer variable rather than a literal, so a layer has an edge
//! per value it can take: the diagram is multi-valued, an MDD [^1], and the
//! BDD encoding of the pseudo-Boolean literature [^2] is the case where every
//! term has two values. Both are domain consistent [^1]. A search for "the BDD
//! encoding" or "the MDD encoding" belongs here.
//!
//! [^1]: I. Abío, R. Nieuwenhuis, A. Oliveras, E. Rodríguez-Carbonell, V.
//! Mayer-Eichberger, "A New Look at BDDs for Pseudo-Boolean Constraints",
//! Journal of Artificial Intelligence Research 45 (2012) 443–480.
//!
//! [^2]: I. Abío, R. Nieuwenhuis, A. Oliveras, E. Rodríguez-Carbonell, "BDDs
//! for Pseudo-Boolean Constraints — Revisited", SAT 2011, LNCS 6695, 61–75.

use std::{
	cmp::{max, min, Ordering},
	iter::once,
	ops::Range,
};

use itertools::Itertools;

use crate::{
	constraint::{
		linear::Comparator,
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		count::Count,
		cardinality_one::CardinalityOne,
		int_linear::{term_max, term_min, term_values, Decompose, NormalizedIntLinear, Term},
		int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
	},
	decision::integer::IntVar,
	helpers::new_named_lit,
	BoolVal, ClauseDatabase, Coeff, Encoder, Result, Unsatisfiable,
};

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// Encoder for a linear constraint, decomposing it through the layers of a
/// decision diagram; also known as the MDD encoding, or the BDD encoding where
/// every term is a single literal.
///
/// One layer per term, holding the partial sums still reachable. Layers that
/// cannot be told apart are shared, so a constraint whose terms interfere
/// little decomposes into fewer pieces than the chain or the tree would give.
/// Domain consistent, whatever reaches it.
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear}, int_linear::DecisionDiagramEncoder,
/// #                  linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// # let mut f = Cnf::default();
/// # let (x, y) = (IntVar::new(0..=5), IntVar::new(0..=5));
/// let con = Linear::new(x * 2 + y * 3, Comparator::LessEq, 10);
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a sum of integer terms is a linear constraint");
/// };
/// DecisionDiagramEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
pub struct DecisionDiagramEncoder {
	add_consistency: bool,
	cutoff: Option<Coeff>,
}

#[derive(Debug, Clone, PartialEq)]
/// What a layer holds at one interval of partial sums: a node of its own, a
/// sum no solution passes through, or a read on the layer after it.
enum DiagramNode {
	Val,
	Gap,
	View(Coeff),
}

impl DecisionDiagramEncoder {
	fn diagram(
		i: usize,
		xs: &[Term],
		sum: Coeff,
		ws: &mut Vec<Vec<(Range<Coeff>, DiagramNode)>>,
	) -> (Range<Coeff>, DiagramNode) {
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
			.map(|v| (v, Self::diagram(i + 1, xs, sum + v, ws)))
			.collect_vec();

		// TODO could we check whether a domain value of x always leads to gaps?
		let is_gap = views.iter().all(|(_, (_, v))| v == &DiagramNode::Gap);
		// A layer is a partition into disjoint intervals, so equal intervals
		// are the same node: children that share a literal some other way
		// would already have been merged into one interval.
		let view = (views.iter().map(|(_, (iv, _))| iv).all_equal())
			.then(|| views.first().unwrap().1 .0.end - 1);

		let interval = views
			.into_iter()
			.map(|(v, (interval, _))| (interval.start - v)..(interval.end - v))
			.reduce(|a, b| max(a.start, b.start)..min(a.end, b.end))
			.unwrap();

		let node = if is_gap {
			DiagramNode::Gap
		} else if let Some(view) = view {
			DiagramNode::View(view)
		} else {
			DiagramNode::Val
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

	fn construct_diagram(xs: &[Term], cmp: Comparator, k: Coeff) -> Vec<Vec<(Range<Coeff>, DiagramNode)>> {
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

		let mut ws: Vec<Vec<(Range<Coeff>, DiagramNode)>> = margins
			.into_iter()
			.rev()
			.chain(once((k, k)))
			.zip(bounds)
			.map(|((lb_margin, ub_margin), (lb, ub))| {
				match cmp {
					Comparator::LessEq => vec![
						(lb_margin > lb).then_some((0..(lb_margin + 1), DiagramNode::Val)),
						(ub_margin <= ub).then_some(((ub_margin + 1)..inf, DiagramNode::Gap)),
					],
					_ => vec![
						(lb_margin > lb).then_some((0..lb_margin, DiagramNode::Gap)),
						(lb_margin == ub_margin).then_some((k..(k + 1), DiagramNode::Val)),
						(ub_margin <= ub).then_some(((ub_margin + 1)..inf, DiagramNode::Gap)),
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

		let _ = Self::diagram(0, xs, 0, &mut ws);
		ws
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
}

impl DecisionDiagramEncoder {
	/// The encoder of the pieces this one decomposes a constraint into.
	fn encoder(&self) -> IntTernaryEncoder {
		IntTernaryEncoder::with_config(IntTernaryConfig {
			cutoff: self.cutoff,
			..IntTernaryConfig::default()
		})
	}
}

impl Decompose for DecisionDiagramEncoder {
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
		// Heuristic: narrowest first, so a layer tends to agree with the next
		// from some total upwards and can share its literal.
		let terms = con
			.terms()
			.iter()
			.map(|(c, x)| (**c, x.clone()))
			.sorted_by(|a: &Term, b: &Term| term_max(a).cmp(&term_max(b)))
			.collect_vec();
		let (cmp, k) = (Comparator::from(con.cmp()), con.k());

		// The nodes of every layer, before any of them is a variable: a total,
		// and the total of the next layer it shares its literal with.
		let nodes = Self::construct_diagram(&terms, cmp, k)
			.into_iter()
			.map(|layer| {
				layer
					.into_iter()
					.filter_map(|(interval, node)| {
						// A node stands for the largest total in its interval.
						let val = interval.end - 1;
						match node {
							DiagramNode::Gap => None,
							DiagramNode::Val => Some((val, None)),
							DiagramNode::View(of) => Some((val, Some(of))),
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

impl<Db> Encoder<Db, NormalizedBoolLinear> for DecisionDiagramEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		// Decomposing works in integers, so the literals become them first.
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for DecisionDiagramEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "decision_diagram_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		self.encoder().encode_decomposed(db, con, self)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for DecisionDiagramEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for DecisionDiagramEncoder {
	fn encode(&self, db: &mut Db, con: &Count) -> Result {
		// Counting into a variable is a linear constraint whose bound is not a
		// constant, which this encoder takes once the bound is a term.
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for DecisionDiagramEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::helpers::tests::{linear_test_suite, prelude::*};

	#[test]
	fn diagram_layers_share_the_literals_they_agree_on() {
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
		let LinVariant::BoolLinear(con) = LinAggregator::default()
			.aggregate(&mut cnf, &con)
			.unwrap()
		else {
			panic!("weighted literals aggregate to a Boolean linear constraint");
		};
		// The diagram is built over integers, so the literals become them here.
		let con = con.as_int_linear(&mut cnf).unwrap();
		cnf.encode(&con, &crate::constraint::linear::DecisionDiagramEncoder::default())
			.unwrap();

		assert_eq!(
			cnf.num_vars(),
			4,
			"the three terms and the one total the layers still tell apart"
		);
	}

	card1_test_suite! {
		decision_diagram_encoder_card1, DecisionDiagramEncoder::default()
	}
	linear_test_suite! {decision_diagram_encoder, DecisionDiagramEncoder::default()}
}
