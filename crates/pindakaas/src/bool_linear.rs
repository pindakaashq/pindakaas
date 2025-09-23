//! This module contains representations and encoding algorithms for general
//! Boolean linear constraints.
//!
//! Boolean linear constraints can be modelled using [`BoolLinExp`] and
//! subsequently [`BoolLinear`]. These representations can then be normalized
//! and simplified using [`BoolLinAggregator`]. Resulting
//! [`NormalizedBoolLinear`] can be encoded using a variety of [`Encoder`]s such
//! as the [`AdderEncoder`], [`BddEncoder`], [`SwcEncoder`], and
//! [`TotalizerEncoder`].
//!
//! This module contains some additional helper types that can be used to
//! simplify this encoding process. [`StaticLinEncoder`] can help choose an
//! encoder based on the [`BoolLinVariant`] produced by [`BoolLinAggregator`].
//! [`LinearEncoder`] can be used to pipeline [`BoolLinAggregator`] and a
//! [`BoolLinVariant`] [`Encoder`].

use std::{
	cell::RefCell,
	cmp::{max, min, Ordering},
	collections::VecDeque,
	fmt::{self, Display},
	iter::once,
	ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Neg, Range, Sub, SubAssign},
	rc::Rc,
};

use itertools::Itertools;
use rustc_hash::{FxBuildHasher, FxHashMap};

use crate::{
	cardinality::Cardinality,
	cardinality_one::{CardinalityOne, PairwiseEncoder},
	helpers::{as_binary, is_powers_of_two, new_named_lit},
	integer::{
		lex_leq_const, Consistency, IntVar, IntVarEnc, IntVarOrd, Lin, Model, GROUND_BINARY_AT_LB,
	},
	propositional_logic::{Formula, TseitinEncoder},
	sorted::{Sorted, SortedEncoder},
	AsDynClauseDatabase, BoolVal, Checker, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder,
	IntEncoding, Lit, Result, Unsatisfiable, Valuation, Var,
};

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// Encoder for the linear constraints that ∑ coeffᵢ·litᵢ ≷ k using a binary
/// adders circuits
pub struct AdderEncoder {}

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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// A transformation of a general [`BoolLinear`] constraint into a aggregated
/// and normalized variant.
pub struct BoolLinAggregator {
	sorted_encoder: SortedEncoder,
	sort_same_coefficients: usize,
}

#[derive(Clone, Debug)]
/// A linear combination of boolean variables, where Boolean literals are
/// multiplied by constant coefficients and added together.
pub struct BoolLinExp {
	/// All terms of the pseudo-Boolean linear expression
	terms: VecDeque<(Lit, Coeff)>,
	/// Number of unconstrained terms (located at the front of `terms`)
	num_free: usize,
	/// Constraints placed on different terms, and the number of terms involved
	/// in the constraint
	constraints: Vec<(Constraint, usize)>,
	/// Additive constant
	add: Coeff,
	/// Multiplicative contant
	mult: Coeff,
}

#[derive(Debug)]
/// Type used to distinguish between different variants of Boolean linear
/// constraints for which specialized encoding algorithms exist.
///
/// This type is used as the result of the aggregation/normalization process
/// ([`BoolLinAggregator::aggregate`]), which will simplify a constraint to its
/// most simplified form.
pub enum BoolLinVariant {
	/// Most general form of Boolean linear expression: a sum of Boolean
	/// literals multiplied by positive coefficients that must be
	/// (smaller-or-)equal to a positive constant.
	Linear(NormalizedBoolLinear),
	/// Cardinality constraint (also known as a counting constraint): a sum of
	/// Boolean literals that must be (smaller-or-)equal to a positive constant.
	Cardinality(Cardinality),
	/// Cardinality constraint with the constant 1 (i.e. at-least or exactly 1
	/// literal must be true).
	CardinalityOne(CardinalityOne),
	/// Constraint was trivially encoded into clauses.
	Trivial,
}

#[derive(Debug, Clone)]
/// A Boolean linear constraint that can be used to constrain a linear
/// combination of boolean variables.
///
/// Note that this type of constraint is often referred to in literature under
/// the more general term of pseudo-Boolean constraints.
///
/// The constraint compares a [`BoolLinExp`] to a constant using a
/// [`Comparator`], where the expression takes the left hand side of the
/// comparison and the constant takes the right hand side.
pub struct BoolLinear {
	/// Expression being constrained
	exp: BoolLinExp,
	/// Comparator when exp is on the left hand side and k is on the right hand
	/// side
	cmp: Comparator,
	/// Coefficient providing the upper bound or lower bound to exp, or both
	k: Coeff,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
/// A comparator type used in linear and cardinality constraints.
pub enum Comparator {
	/// Force the left hand side of the constraint to be less than or equal to
	/// the right hand side, i.e. `exp ≤ k`.
	LessEq,
	/// Force the left hand side of the constraint to be equal to the right hand
	/// side, i.e. `exp = k`.
	Equal,
	/// Force the left hand side of the constraint to be greater than or equal
	/// to the right hand side, i.e. `exp ≥ k`.
	GreaterEq,
}

#[derive(Debug, Clone)]
/// Consistency constraint that can be captured by a Boolean linear expression
/// to improve the encoding of constraints using the expression.
pub(crate) enum Constraint {
	AtMostOne,
	ImplicationChain,
	Domain { lb: Coeff, ub: Coeff },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
/// A comparator that has been limited to a either `Equal` or `LessEq`.
///
/// This type is used to ensure that the comparator of [`NormalizedBoolLinear`],
/// [`Cardinality`], and [`CardinalityOne`] constraints are limited to a
/// specific set of values.
pub(crate) enum LimitComp {
	Equal,
	LessEq,
}

/// Internal marker trait to ensure the other trait implementations only applies
/// to encoders implemented by this crate.
pub(crate) trait LinMarker {}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// An encoder for Boolean linear constraints that performs aggregation using a
/// [`BoolLinAggregator`] and then encodes the aggregated constraints using a
/// [`Encoder`] for [`BoolLinVariant`].
pub struct LinearEncoder<Enc = StaticLinEncoder, Agg = BoolLinAggregator> {
	enc: Enc,
	agg: Agg,
}

#[derive(Debug, Clone)]
/// An [`BoolLinear`] expression that has been aggregated and normalized.
///
/// The constraint captured by this struct contains only positive coefficients,
/// contains at most one term with the same variable, and its comparator has
/// been limited to `≤` or `=`. Objects of this type are generally the result of
/// using the [`BoolLinAggregator`], and are generally the required input type
/// for encoders of boolean linear constraints.
pub struct NormalizedBoolLinear {
	terms: Vec<Part>,
	cmp: LimitComp,
	k: PosCoeff,
}

// TODO how can we support both Part(itions) of "terms" ( <Lit, C> for pb
// constraints) and just lits (<Lit>) for AMK/AMO's?
//
// TODO add EO, and probably something for Unconstrained
// TODO this can probably follow the same structure as LinExp
#[derive(Debug, Clone)]
/// Representation of Boolean linear terms under the (possible) influence of a
/// consistency constraint.
///
/// Note that terms that are not influenced by a consistency constraint can be
/// represented by an Amo or Ic variant containing a singular term.
pub(crate) enum Part {
	Amo(Vec<(Lit, PosCoeff)>),
	Ic(Vec<(Lit, PosCoeff)>),
	Dom(Vec<(Lit, PosCoeff)>, PosCoeff, PosCoeff),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// PosCoeff is a type for coefficients that are guaranteed by the programmer to
/// be 0 or greater.
pub(crate) struct PosCoeff(Coeff);

/// An encoder for general boolean linear constraints that dispatches to a
/// different choice of sub-encoder for cardinality and cardinality-one
/// constraints.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct StaticLinEncoder<
	LinEnc = AdderEncoder,
	CardEnc = AdderEncoder, // TODO: Actual Cardinality encoding
	Card1Enc = PairwiseEncoder,
> {
	lin_enc: LinEnc,
	card_enc: CardEnc,
	amo_enc: Card1Enc,
}

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight
/// Counter (SWC)
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct SwcEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized
/// Totalizer (GT)
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct TotalizerEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

impl AdderEncoder {
	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "carry_circuit", skip_all, fields(constraint = Self::trace_print_carry(input, &output))))]
	/// Encode the adder carry circuit
	///
	/// This function accepts either 2 literals as `input` (half adder) or 3
	/// literals (full adder).
	///
	/// `output` can be either a literal, or a constant Boolean value.
	fn carry_circuit<Db>(db: &mut Db, input: &[Lit], output: BoolVal) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		match output {
			BoolVal::Lit(carry) => match *input {
				[a, b] => {
					db.add_clause([!a, !b, carry])?;
					db.add_clause([a, !carry])?;
					db.add_clause([b, !carry])
				}
				[a, b, c] => {
					db.add_clause([a, b, !carry])?;
					db.add_clause([a, c, !carry])?;
					db.add_clause([b, c, !carry])?;

					db.add_clause([!a, !b, carry])?;
					db.add_clause([!a, !c, carry])?;
					db.add_clause([!b, !c, carry])
				}
				_ => unreachable!(),
			},
			BoolVal::Const(k) => match *input {
				[a, b] => {
					if k {
						// TODO: Can we avoid this?
						db.add_clause([a])?;
						db.add_clause([b])
					} else {
						db.add_clause([!a, !b])
					}
				}
				[a, b, c] => {
					let neg = |x: Lit| if k { x } else { !x };
					db.add_clause([neg(a), neg(b)])?;
					db.add_clause([neg(a), neg(c)])?;
					db.add_clause([neg(b), neg(c)])
				}
				_ => unreachable!(),
			},
		}
	}

	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "sum_circuit", skip_all, fields(constraint = Self::trace_print_sum(input, &output))))]
	/// Encode the adder sum circuit
	///
	/// This function accepts either 2 literals as `input` (half adder) or 3
	/// literals (full adder).
	///
	/// `output` can be either a literal, or a constant Boolean value.
	fn sum_circuit<Db>(db: &mut Db, input: &[Lit], output: BoolVal) -> Result
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		match output {
			BoolVal::Lit(sum) => match *input {
				[a, b] => {
					db.add_clause([!a, !b, !sum])?;
					db.add_clause([!a, b, sum])?;
					db.add_clause([a, !b, sum])?;
					db.add_clause([a, b, !sum])
				}
				[a, b, c] => {
					db.add_clause([a, b, c, !sum])?;
					db.add_clause([a, !b, !c, !sum])?;
					db.add_clause([!a, b, !c, !sum])?;
					db.add_clause([!a, !b, c, !sum])?;

					db.add_clause([!a, !b, !c, sum])?;
					db.add_clause([!a, b, c, sum])?;
					db.add_clause([a, !b, c, sum])?;
					db.add_clause([a, b, !c, sum])
				}
				_ => unreachable!(),
			},
			BoolVal::Const(true) => {
				let xor = Formula::Xor(input.iter().map(|&l| Formula::Atom(l)).collect_vec());
				TseitinEncoder.encode(db, &xor)
			}
			BoolVal::Const(false) => match *input {
				[a, b] => {
					db.add_clause([a, !b])?;
					db.add_clause([!a, b])
				}
				[a, b, c] => {
					db.add_clause([!a, !b, !c])?;
					db.add_clause([!a, b, c])?;
					db.add_clause([a, !b, c])?;
					db.add_clause([a, b, !c])
				}
				_ => unreachable!(),
			},
		}
	}

	#[cfg(any(feature = "tracing", test))]
	fn trace_print_carry(input: &[Lit], output: &BoolVal) -> String {
		use crate::trace::trace_print_lit;
		let inner = itertools::join(input.iter().map(trace_print_lit), " + ");
		match output {
			BoolVal::Lit(r) => format!("{} ≡ ({} > 1)", trace_print_lit(r), inner),
			BoolVal::Const(true) => format!("{inner} > 1"),
			BoolVal::Const(false) => format!("{inner} ≤ 1"),
		}
	}

	#[cfg(any(feature = "tracing", test))]
	fn trace_print_sum(input: &[Lit], output: &BoolVal) -> String {
		use crate::trace::trace_print_lit;
		let inner = itertools::join(input.iter().map(trace_print_lit), " ⊻ ");
		match output {
			BoolVal::Lit(r) => format!("{} ≡ {}", trace_print_lit(r), inner),
			BoolVal::Const(true) => inner,
			BoolVal::Const(false) => format!("¬({inner})"),
		}
	}
}

impl<Db> Encoder<Db, NormalizedBoolLinear> for AdderEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "adder_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut Db, lin: &NormalizedBoolLinear) -> Result {
		debug_assert!(lin.cmp == LimitComp::LessEq || lin.cmp == LimitComp::Equal);
		// The number of relevant bits in k
		const ZERO: Coeff = 0;
		let bits = ZERO.leading_zeros() - lin.k.leading_zeros();
		let mut k = as_binary(lin.k, Some(bits));

		let first_zero = lin.k.trailing_ones() as usize;
		let bits = bits as usize;
		debug_assert!(k[bits - 1]);

		// Closure that provides an iterator over all terms independent of the
		// partitioning
		let all_terms = || {
			lin.terms
				.iter()
				.flat_map(|part| part.iter().map(|&(lit, coef)| (lit, coef)))
		};

		// Create structure with which coefficients use which bits
		let mut bucket = vec![Vec::new(); bits];
		for (i, bucket) in bucket.iter_mut().enumerate().take(bits) {
			for (lit, coef) in all_terms() {
				if *coef & (1 << i) != 0 {
					bucket.push(lit);
				}
			}
		}

		// Compute the sums and carries for each bit layer
		// if comp == Equal, then this is directly enforced (to avoid creating
		// additional literals) otherwise, sum literals are left in the buckets for
		// further processing
		let mut sum = vec![None; bits];
		for b in 0..bits {
			match bucket[b].len() {
				0 => {
					if k[b] && lin.cmp == LimitComp::Equal {
						return Err(Unsatisfiable);
					}
				}
				1 => {
					let x = bucket[b].pop().unwrap();
					if lin.cmp == LimitComp::Equal {
						db.add_clause([if k[b] { x } else { !x }])?;
					} else {
						sum[b] = Some(x);
					}
				}
				_ => {
					while bucket[b].len() >= 2 {
						let last = bucket[b].len() <= 3;
						let lits = if last {
							bucket[b].split_off(0)
						} else {
							let i = bucket[b].len() - 3;
							bucket[b].split_off(i)
						};
						debug_assert!(lits.len() == 3 || lits.len() == 2);

						// Compute sum
						if last && lin.cmp == LimitComp::Equal {
							// No need to create a new literal, force the sum to equal the result
							Self::sum_circuit(db, lits.as_slice(), BoolVal::Const(k[b]))?;
						} else if lin.cmp != LimitComp::LessEq || !last || b >= first_zero {
							// Literal is not used for the less-than constraint unless a zero has
							// been seen first
							let sum = new_named_lit!(
								db,
								if last {
									crate::trace::subscripted_name("∑", b)
								} else {
									crate::trace::subscripted_name(
										&format!("iS{b}"),
										(bucket[b].len() / 3) + 1,
									)
								}
							);
							Self::sum_circuit(db, lits.as_slice(), BoolVal::Lit(sum))?;
							bucket[b].push(sum);
						}

						// Compute carry
						if b + 1 >= bits {
							// Carry will bring the sum to be greater than k, force to be false
							if lits.len() == 2 && lin.cmp == LimitComp::Equal {
								// Already encoded by the XOR to compute the sum
							} else {
								Self::carry_circuit(db, &lits[..], BoolVal::Const(false))?;
							}
						} else if last && lin.cmp == LimitComp::Equal && bucket[b + 1].is_empty() {
							// No need to create a new literal, force the carry to equal the result
							Self::carry_circuit(db, &lits[..], BoolVal::Const(k[b + 1]))?;
							// Mark k[b + 1] as false (otherwise next step will fail)
							k[b + 1] = false;
						} else {
							let carry = new_named_lit!(
								db,
								if last {
									crate::trace::subscripted_name("c", b)
								} else {
									crate::trace::subscripted_name(
										&format!("iC{b}"),
										(bucket[b].len() / 3) + 1,
									)
								}
							);
							Self::carry_circuit(db, lits.as_slice(), BoolVal::Lit(carry))?;
							bucket[b + 1].push(carry);
						}
					}
					debug_assert!(
						(lin.cmp == LimitComp::Equal && bucket[b].is_empty())
							|| (lin.cmp == LimitComp::LessEq
								&& (bucket[b].len() == 1 || b < first_zero))
					);
					sum[b] = bucket[b].pop();
				}
			}
		}
		// In case of equality this has been enforced
		debug_assert!(lin.cmp != LimitComp::Equal || sum.iter().all(|x| x.is_none()));

		// Enforce less-than constraint
		if lin.cmp == LimitComp::LessEq {
			lex_leq_const(db, sum.as_slice(), lin.k, bits)?;
		}
		Ok(())
	}
}

impl LinMarker for AdderEncoder {}

impl BddEncoder {
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

	fn bdd(
		i: usize,
		xs: &Vec<IntVarEnc>,
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

		let views = xs[i]
			.dom()
			.iter()
			.flatten()
			.map(|v| (v, Self::bdd(i + 1, xs, sum + v, ws)))
			.collect_vec();

		// TODO could we check whether a domain value of x always leads to gaps?
		let is_gap = views.iter().all(|(_, (_, v))| v == &BddNode::Gap);
		// TODO without checking actual Val identity, could we miss when the next layer
		// has two adjacent nodes that are both views on the same node at the layer
		// below?
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

	fn construct_bdd(
		xs: &Vec<IntVarEnc>,
		cmp: &LimitComp,
		k: PosCoeff,
	) -> Vec<Vec<(Range<Coeff>, BddNode)>> {
		let k = *k;

		let bounds = xs
			.iter()
			.scan((0, 0), |state, x| {
				*state = (state.0 + x.lb(), state.1 + x.ub());
				Some(*state)
			})
			.chain(once((0, k)))
			.collect_vec();

		let margins = xs
			.iter()
			.rev()
			.scan((k, k), |state, x| {
				*state = (state.0 - x.ub(), state.1 - x.lb());
				Some(*state)
			})
			.collect_vec();

		let inf = xs.iter().fold(0, |a, x| a + x.ub()) + 1;

		let mut ws: Vec<Vec<(Range<Coeff>, BddNode)>> = margins
			.into_iter()
			.rev()
			.chain(once((k, k)))
			.zip(bounds)
			.map(|((lb_margin, ub_margin), (lb, ub))| {
				match cmp {
					LimitComp::LessEq => vec![
						(lb_margin > lb).then_some((0..(lb_margin + 1), BddNode::Val)),
						(ub_margin <= ub).then_some(((ub_margin + 1)..inf, BddNode::Gap)),
					],
					LimitComp::Equal => vec![
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
}

impl<Db> Encoder<Db, NormalizedBoolLinear> for BddEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "bdd_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut Db, lin: &NormalizedBoolLinear) -> Result {
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.flat_map(|(i, part)| IntVarEnc::from_part(db, part, lin.k, format!("x_{i}")))
			.sorted_by(|a: &IntVarEnc, b: &IntVarEnc| b.ub().cmp(&a.ub())) // sort by *decreasing* ub
			.collect_vec();

		let mut model = Model::default();

		let ys = Self::construct_bdd(&xs, &lin.cmp, lin.k);
		let xs = xs
			.into_iter()
			.map(|x| Rc::new(RefCell::new(model.add_int_var_enc(x))))
			.collect_vec();

		let ys = ys
			.into_iter()
			.map(|nodes| {
				let mut views = FxHashMap::default();
				Rc::new(RefCell::new({
					let mut y = model.new_var(
						nodes
							.into_iter()
							.filter_map(|(iv, node)| match node {
								BddNode::Gap => None,
								BddNode::Val => Some(iv.end - 1),
								BddNode::View(view) => {
									let val = iv.end - 1;
									let _ = views.insert(val, view);
									Some(val)
								}
							})
							.map(|v| v..=v)
							.collect(),
						self.add_consistency,
					);
					y.views = views
						.into_iter()
						.map(|(val, view)| (val, (y.id + 1, view)))
						.collect();
					y
				}))
			})
			.collect_vec();

		let mut ys = ys.into_iter();
		let first = ys.next().unwrap();
		assert_eq!(first.as_ref().borrow().size(), 1);
		let _ = xs.iter().zip(ys).fold(first, |curr, (x_i, next)| {
			model.cons.push(Lin::tern(
				curr,
				Rc::clone(x_i),
				lin.cmp.clone(),
				Rc::clone(&next),
			));
			next
		});

		model.encode(db, self.cutoff)?;
		Ok(())
	}
}

impl LinMarker for BddEncoder {}

impl BoolLinAggregator {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "aggregator", skip_all, fields(constraint = lin.trace_print()))
	)]
	/// Perform (internal) aggregation of [`BoolLinear`] constraints,
	/// normalizing them and simplify them into specialized forms for which
	/// different encoding algorithms exist.
	pub fn aggregate<Db>(&self, db: &mut Db, lin: &BoolLinear) -> Result<BoolLinVariant>
	where
		Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	{
		let mut k = lin.k;
		// Aggregate multiple occurrences of the same
		// variable.
		let mut agg = FxHashMap::with_capacity_and_hasher(lin.exp.terms.len(), FxBuildHasher);
		for term in &lin.exp.terms {
			let var = term.0.var();
			let entry = agg.entry(var).or_insert(0);
			let mut coef = term.1 * lin.exp.mult;
			if term.0.is_negated() {
				k -= coef;
				coef = -coef;
			}
			*entry += coef;
		}

		// Convert ≥ to ≤
		if lin.cmp == Comparator::GreaterEq {
			agg = agg.into_iter().map(|(var, coef)| (var, -coef)).collect();
			k = -k;
		}

		let mut partition: Vec<(Constraint, Vec<(Lit, Coeff)>)> =
			Vec::with_capacity(lin.exp.constraints.len());
		// Adjust side constraints when literals are combined (and currently transform
		// to partition structure)
		let mut iter = lin.exp.terms.iter().skip(lin.exp.num_free);
		for con in &lin.exp.constraints {
			let mut terms = Vec::with_capacity(con.1);
			for _ in 0..con.1 {
				let term = iter.next().unwrap();
				if let Some((var, i)) = agg.remove_entry(&term.0.var()) {
					terms.push((var.into(), i));
				}
			}
			if !terms.is_empty() {
				match con.0 {
					Constraint::Domain { lb, ub } => {
						// Domain constraint can only be enforced when PB is coef*(x1 + 2x2 + 4x3 +
						// ...), where l <= x1 + 2*x2 + 4*x3 + ... <= u
						if terms.len() == con.1 && is_powers_of_two(terms.iter().map(|(_, c)| *c)) {
							// Adjust the bounds to account for coef
							let (lb, ub) = if lin.cmp == Comparator::GreaterEq {
								// 0..range can be encoded by the bits multiplied by coef
								let range = -terms.iter().fold(0, |acc, (_, coef)| acc + *coef);
								// this range is inverted if we have flipped the comparator
								(range - ub, range - lb)
							} else {
								// in both cases, l and u now represent the true constraint
								(terms[0].1 * lb, terms[0].1 * ub)
							};
							partition.push((Constraint::Domain { lb, ub }, terms));
						} else {
							for term in terms {
								partition.push((Constraint::AtMostOne, vec![term]));
							}
						}
					}
					_ => partition.push((con.0.clone(), terms)),
				}
			}
		}

		// Add remaining (unconstrained) terms
		debug_assert!(agg.len() <= lin.exp.num_free);
		let agg_keys: Vec<Var> = agg.keys().copied().sorted().collect();
		for var in agg_keys {
			partition.push((Constraint::AtMostOne, vec![(var.into(), agg[&var])]));
		}

		k -= lin.exp.add;
		let cmp = match lin.cmp {
			Comparator::LessEq | Comparator::GreaterEq => LimitComp::LessEq,
			Comparator::Equal => LimitComp::Equal,
		};

		let convert_term_if_negative = |term: (Lit, Coeff), k: &mut Coeff| -> (Lit, PosCoeff) {
			let (mut lit, mut coef) = term;
			if coef.is_negative() {
				coef = -coef;
				lit = !lit;
				*k += coef;
			};
			(lit, PosCoeff::new(coef))
		};

		let partition: Vec<Part> = partition
			.into_iter()
			.filter(|(_, t)| !t.is_empty()) // filter out empty groups
			.flat_map(|part| -> Vec<Part> {
				// convert terms with negative coefficients
				match part {
					(Constraint::AtMostOne, mut terms) => {
						if terms.len() == 1 {
							return vec![Part::Amo(
								terms
									.into_iter()
									.filter(|&(_, coef)| coef != 0)
									.map(|(lit, coef)| {
										convert_term_if_negative((lit, coef), &mut k)
									})
									.collect(),
							)];
						}

						// Find most negative coefficient
						let (min_index, (_, min_coef)) = terms
							.iter()
							.enumerate()
							.min_by(|(_, (_, a)), (_, (_, b))| a.cmp(b))
							.expect("Partition should not contain constraint on zero terms");

						// If negative, normalize without breaking AMO constraint
						if min_coef.is_negative() {
							let q = -*min_coef;

							// add aux var y and constrain y <-> ( ~x1 /\ ~x2 /\ .. )
							let y = db.new_lit();

							// ~x1 /\ ~x2 /\ .. -> y == x1 \/ x2 \/ .. \/ y
							db.add_clause(
								terms
									.iter()
									.map(|(lit, _)| *lit)
									.chain(once(y))
							)
							.unwrap();

														// y -> ( ~x1 /\ ~x2 /\ .. ) == ~y \/ ~x1, ~y \/ ~x2, ..
							for lit in terms.iter().map(|tup| tup.0) {
								db.add_clause( [!y, !lit]).unwrap();
							}

							// this term will cancel out later when we add q*min_lit to the LHS
							let _ =terms.remove(min_index);

							// since y + x1 + x2 + ... = 1 (exactly-one), we have q*y + q*x1 + q*x2 + ... = q
							// after adding term 0*y, we can add q*y + q*x1 + q*x2 + ... on the LHS, and q on the RHS
							terms.push((y, 0)); // note: it's fine to add y into the same AMO group
							terms = terms
								.iter()
								.map(|(lit, coef)| (*lit, *coef + q))
								.collect();
							k += q;
						}

						// all coefficients should be positive (since we subtracted the most negative coefficient)
						vec![Part::Amo(
							terms
								.into_iter()
								.map(|(lit, coef)| (lit, PosCoeff::new(coef)))
								.collect(),
						)]
					}

					(Constraint::ImplicationChain, terms) => {
						// normalize by splitting up the chain into two chains by coef polarity, inverting the coefs of the neg
						let (pos_chain, neg_chain): (_, Vec<_>) =
							terms.into_iter().partition(|(_, coef)| coef.is_positive());
						vec![
							Part::Ic(
								pos_chain
									.into_iter()
									.map(|(lit, coef)| (lit, PosCoeff::new(coef)))
									.collect(),
							),
							Part::Ic(
								neg_chain
									.into_iter()
									.map(|(lit, coef)| {
										convert_term_if_negative((lit, coef), &mut k)
									})
									.rev() // x1 <- x2 <- x3 <- ... becomes ~x1 -> ~x2 -> ~x3 -> ...
									.collect(),
							),
						]
					}
					(Constraint::Domain { lb: l, ub: u },  terms) => {
						assert!(
							terms.iter().all(|(_,coef)| coef.is_positive())
								|| terms.iter().all(|(_,coef)| coef.is_negative()),
																"Normalizing mixed positive/negative coefficients not yet supported for Dom constraint on {terms:?}"
						);
						vec![Part::Dom(
							terms
								.into_iter()
								.map(|(lit, coef)| convert_term_if_negative((lit, coef), &mut k))
								.collect(),
							PosCoeff::new(l),
							PosCoeff::new(u),
						)]
					}
				}
			})
			.map(|part| {
				// This step has to come *after* Amo normalization
				let filter_zero_coefficients = |terms: Vec<(Lit, PosCoeff)>| -> Vec<(Lit, PosCoeff)> {
					terms
						.into_iter()
						.filter(|&(_, coef)| *coef != 0)
						.collect()
				};

				match part {
					Part::Amo(terms) => Part::Amo(filter_zero_coefficients(terms)),
					Part::Ic(terms) => Part::Ic(filter_zero_coefficients(terms)),
					Part::Dom(terms, l, u) => Part::Dom(filter_zero_coefficients(terms), l, u),
				}
			})
			.filter(|part| part.iter().next().is_some()) // filter out empty groups
			.collect();

		// trivial case: constraint is unsatisfiable
		if k < 0 {
			return Err(Unsatisfiable);
		}
		// trivial case: no literals can be activated
		if k == 0 {
			for part in partition {
				for (lit, _) in part.iter() {
					db.add_clause([!*lit])?;
				}
			}
			return Ok(BoolLinVariant::Trivial);
		}
		let mut k = PosCoeff::new(k);

		// Remove terms with coefs higher than k
		let partition = partition
			.into_iter()
			.map(|part| match part {
				Part::Amo(terms) => Part::Amo(
					terms
						.into_iter()
						.filter(|(lit, coef)| {
							if coef > &k {
								db.add_clause([!*lit]).unwrap();
								false
							} else {
								true
							}
						})
						.collect(),
				),
				Part::Ic(terms) => {
					// for IC, we can compare the running sum to k
					let mut acc = 0;
					Part::Ic(
						terms
							.into_iter()
							.filter(|&(lit, coef)| {
								acc += *coef;
								if acc > *k {
									db.add_clause([!lit]).unwrap();
									false
								} else {
									true
								}
							})
							.collect(),
					)
				}
				Part::Dom(terms, l, u) => {
					// remove terms exceeding k
					let terms = terms
						.into_iter()
						.filter(|(lit, coef)| {
							if coef > &k {
								db.add_clause([!*lit]).unwrap();
								false
							} else {
								true
							}
						})
						.collect_vec();
					// the one or more of the most significant bits have been removed, the upper
					// bound could have dropped to a power of 2 (but not beyond)
					let u = PosCoeff::new(min(*u, terms.iter().map(|&(_, coef)| *coef).sum()));
					Part::Dom(terms, l, u)
				}
			})
			.filter(|part| part.iter().next().is_some()) // filter out empty groups
			.collect_vec();

		// Check whether some literals can violate / satisfy the constraint
		let lhs_ub = PosCoeff::new(
			partition
				.iter()
				.map(|part| match part {
					Part::Amo(terms) => terms.iter().map(|&(_, i)| *i).max().unwrap_or(0),
					Part::Ic(terms) | Part::Dom(terms, _, _) => {
						terms.iter().map(|&(_, coef)| *coef).sum()
						// TODO max(k, acc + ..)
					}
				})
				.sum(),
		);

		match cmp {
			LimitComp::LessEq => {
				if lhs_ub <= k {
					return Ok(BoolLinVariant::Trivial);
				}

				// If we have only 2 (unassigned) lits, which together (but not individually)
				// exceed k, then -x1\/-x2
				if partition.iter().flat_map(|part| part.iter()).count() == 2 {
					db.add_clause(
						partition
							.iter()
							.flat_map(|part| part.iter())
							.map(|(lit, _)| !*lit)
							.collect_vec(),
					)?;
					return Ok(BoolLinVariant::Trivial);
				}
			}
			LimitComp::Equal => {
				if lhs_ub < k {
					return Err(Unsatisfiable);
				}
				if lhs_ub == k {
					for part in partition {
						match part {
							Part::Amo(terms) => {
								db.add_clause([terms
									.iter()
									.max_by(|(_, a), (_, b)| a.cmp(b))
									.unwrap()
									.0])?;
							}
							Part::Ic(terms) | Part::Dom(terms, _, _) => {
								for (lit, _) in terms {
									db.add_clause([lit])?;
								}
							}
						};
					}
					return Ok(BoolLinVariant::Trivial);
				}
			}
		}

		// debug_assert!(!partition.flat().is_empty());

		// TODO any smart way to implement len() method?
		// TODO assert all groups are non-empty / discard empty groups?
		debug_assert!(partition
			.iter()
			.flat_map(|part| part.iter())
			.next()
			.is_some());

		// special case: all coefficients are equal (and can be made one)
		let val = partition
			.iter()
			.flat_map(|part| part.iter().map(|&(_, coef)| coef))
			.next()
			.unwrap();

		if partition
			.iter()
			.flat_map(|part| part.iter())
			.all(|&(_, coef)| coef == val)
		{
			// trivial case: k cannot be made from the coefficients
			if cmp == LimitComp::Equal && *k % *val != 0 {
				return Err(Unsatisfiable);
			}

			k = PosCoeff::new(*k / *val);
			let partition = partition
				.iter()
				.flat_map(|part| part.iter())
				.map(|&(lit, _)| lit)
				.collect_vec();
			if *k == 1 {
				// Cardinality One constraint
				return Ok(BoolLinVariant::CardinalityOne(CardinalityOne {
					lits: partition,
					cmp,
				}));
			}

			// At most n-1 out of n is equivalent to at least *not* one
			// Ex. at most 2 out of 3 true = at least 1 out of 3 false
			if partition.len() == (*k + 1) as usize {
				let neg = partition.iter().map(|&l| !l);
				db.add_clause(neg.clone())?;

				if cmp == LimitComp::LessEq {
					return Ok(BoolLinVariant::Trivial);
				} else {
					// we still need to constrain x1 + x2 .. >= n-1
					//   == (1 - ~x1) + (1 - ~x2) + .. >= n-1
					//   == - ~x1 - ~x2 - .. <= n-1-n ( == .. <= -1)
					//   == ~x1 + ~x2 + .. <= 1
					return Ok(BoolLinVariant::CardinalityOne(CardinalityOne {
						lits: neg.collect_vec(),
						cmp: LimitComp::LessEq,
					}));
				}
			}

			// Encode count constraint
			return Ok(BoolLinVariant::Cardinality(Cardinality {
				lits: partition,
				cmp,
				k,
			}));
		}

		let partition = if self.sort_same_coefficients >= 2 {
			let (free_lits, mut partition): (Vec<_>, Vec<_>) = partition.into_iter().partition(
				|part| matches!(part, Part::Amo(x) | Part::Ic(x) | Part::Dom(x, _, _) if x.len() == 1),
			);

			for (coef, lits) in free_lits
				.into_iter()
				.map(|part| match part {
					Part::Amo(x) | Part::Ic(x) | Part::Dom(x, _, _) if x.len() == 1 => x[0],
					_ => unreachable!(),
				})
				.map(|(lit, coef)| (coef, lit))
				.into_group_map()
				.into_iter()
			{
				if self.sort_same_coefficients >= 2 && lits.len() >= self.sort_same_coefficients {
					let c = *k / *coef;

					let y = IntVarOrd::from_bounds(db, 0, c, String::from("s")).into();
					self.sorted_encoder
						.encode(db, &Sorted::new(&lits, cmp.clone(), &y))
						.unwrap();

					let lin_exp = BoolLinExp::from(&y);
					partition.push(Part::Ic(
						lin_exp
							.terms
							.into_iter()
							.map(|(lit, _)| (lit, coef))
							.collect(),
					));
				} else {
					for x in lits {
						partition.push(Part::Amo(vec![(x, coef)]));
					}
				}
			}

			partition
		} else {
			partition
		};

		// Default case: encode pseudo-Boolean linear constraint
		Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
			terms: partition,
			cmp,
			k,
		}))
	}
	/// For non-zero `n`, detect groups of minimum size `n` with free literals
	/// and same coefficients, sort them (using provided SortedEncoder) and add
	/// them as a single implication chain group
	pub fn sort_same_coefficients(&mut self, sorted_encoder: SortedEncoder, n: usize) -> &mut Self {
		self.sorted_encoder = sorted_encoder;
		self.sort_same_coefficients = n;
		self
	}
}

impl BoolLinExp {
	// TODO I'm not really happy with this interface yet...
	// Probably makes more sense to use something like int encodings
	/// Add a log encoding to the linear expression, where it is given that the
	/// log encoding is known to be within `lb..=ub`.
	pub fn add_bounded_log_encoding(
		mut self,
		terms: &[(Lit, Coeff)],
		lb: Coeff,
		ub: Coeff,
	) -> Self {
		self.constraints
			.push((Constraint::Domain { lb, ub }, terms.len()));
		self.terms.extend(terms.iter().cloned());
		self
	}

	/// Add multiple terms to the linear expression where the literal
	/// in each term is implied by the literal in the consecutive term
	pub fn add_chain(mut self, chain: &[(Lit, Coeff)]) -> Self {
		if let [term] = chain {
			self.terms.push_front(*term);
			self.num_free += 1;
		} else {
			self.terms.extend(chain.iter().cloned());
			self.constraints
				.push((Constraint::ImplicationChain, chain.len()));
		}
		self
	}

	/// Add multiple terms to the linear expression of which at most one
	/// can be chosen
	pub fn add_choice(mut self, choice: &[(Lit, Coeff)]) -> Self {
		if let [term] = choice {
			self.terms.push_front(*term);
			self.num_free += 1;
		} else {
			self.terms.extend(choice.iter().cloned());
			self.constraints.push((Constraint::AtMostOne, choice.len()));
		}
		self
	}

	/// Add a constant to the linear expression
	///
	/// Note that this is a more explicit version of the `+` or `+=` operator.
	pub fn add_constant(mut self, k: Coeff) -> Self {
		self.add += k;
		self
	}

	/// Add a literal to the linear expression, taking the value `0` if `false`
	/// and `1` if `true`.
	///
	/// Note that this is a more explicit version of the `+` or `+=` operator.
	pub fn add_lit(mut self, lit: Lit) -> Self {
		self.terms.push_front((lit, 1));
		self.num_free += 1;
		self
	}

	/// Create a linear expression from a slice of coefficients and literals,
	/// where each literal is multiplied by the coefficient in the
	/// corresponding position.
	///
	/// Note that the number of coefficients and literals must be equal.
	pub fn from_slices(coeffs: &[Coeff], lits: &[Lit]) -> Self {
		assert_eq!(
			coeffs.len(),
			lits.len(),
			"the number of weights and literals must be equal"
		);
		Self {
			terms: lits.iter().cloned().zip(coeffs.iter().cloned()).collect(),
			num_free: lits.len(),
			..Default::default()
		}
	}

	/// Create a linear expression from a slice of terms, where each term
	/// consist of a literal and coefficient and the former will be multiplied
	/// by the latter.
	pub fn from_terms(terms: &[(Lit, Coeff)]) -> Self {
		Self {
			terms: terms.iter().cloned().collect(),
			num_free: terms.len(),
			..Default::default()
		}
	}

	pub(crate) fn iter(&self) -> impl Iterator<Item = (Option<Constraint>, Vec<&(Lit, Coeff)>)> {
		let mut it = self.terms.iter();
		once((
			None,
			Vec::from_iter((0..self.num_free).map(|_| it.next().unwrap())),
		))
		.chain(self.constraints.iter().map(move |constraint| {
			let mut terms = Vec::with_capacity(constraint.1);
			for _ in 0..constraint.1 {
				if let Some(term) = it.next() {
					terms.push(term);
				}
			}
			(Some(constraint.0.clone()), terms)
		}))
	}

	/// Iterate over the terms of the linear expression, consisting of a literal
	/// and the coefficient by which it is multiplied.
	pub fn terms(&self) -> impl Iterator<Item = (Lit, Coeff)> + '_ {
		self.terms.iter().copied()
	}

	pub(crate) fn value<F: Valuation + ?Sized>(&self, sol: &F) -> Result<Coeff> {
		let mut total = self.add;
		for (constraint, terms) in self.iter() {
			// Calculate sum for constraint
			let sum = terms
				.iter()
				.filter(|(lit, _)| sol.value(*lit))
				.map(|(_, i)| i)
				.sum();
			match constraint {
				Some(Constraint::AtMostOne) => {
					if sum != 0 && terms.iter().filter(|&(l, _)| sol.value(*l)).count() > 1 {
						return Err(Unsatisfiable);
					}
				}
				Some(Constraint::ImplicationChain) => {
					if terms
						.iter()
						.map(|(l, _)| *l)
						.tuple_windows()
						.any(|(a, b)| !sol.value(a) & sol.value(b))
					{
						return Err(Unsatisfiable);
					}
				}
				Some(Constraint::Domain { lb, ub }) => {
					// divide by first coeff to get int assignment
					if GROUND_BINARY_AT_LB {
						if sum > ub - lb {
							return Err(Unsatisfiable);
						}
					} else if lb > sum || sum > ub {
						return Err(Unsatisfiable);
					}
				}
				None => {}
			};
			total += sum;
		}
		Ok(total * self.mult)
	}
}

impl Add for BoolLinExp {
	type Output = BoolLinExp;

	fn add(mut self, rhs: Self) -> Self::Output {
		self += rhs;
		self
	}
}

impl Add<Coeff> for BoolLinExp {
	type Output = BoolLinExp;

	fn add(mut self, rhs: Coeff) -> Self::Output {
		self += rhs;
		self
	}
}

impl<'a> Add<IntEncoding<'a>> for BoolLinExp {
	type Output = BoolLinExp;

	fn add(mut self, rhs: IntEncoding<'a>) -> Self::Output {
		self += rhs;
		self
	}
}

impl AddAssign for BoolLinExp {
	fn add_assign(&mut self, rhs: Self) {
		// Multiply the current expression
		if self.mult != 1 {
			self.add *= self.mult;
			for term in &mut self.terms {
				term.1 *= self.mult;
			}
		}
		self.mult = 1;
		// Add other LinExp
		self.add += rhs.add * rhs.mult;
		let mut rh_terms = rhs.terms;
		self.terms.extend(
			rh_terms
				.drain(rhs.num_free..)
				.map(|(l, c)| (l, c * rhs.mult)),
		);
		debug_assert!(rh_terms.len() == rhs.num_free);
		self.terms
			.extend(rh_terms.into_iter().map(|(l, c)| (l, c * rhs.mult)));
		self.terms.rotate_right(rhs.num_free);
		self.num_free += rhs.num_free;
		self.constraints.extend(rhs.constraints);
	}
}

impl AddAssign<Coeff> for BoolLinExp {
	fn add_assign(&mut self, rhs: Coeff) {
		self.add += rhs;
	}
}

impl<'a> AddAssign<IntEncoding<'a>> for BoolLinExp {
	fn add_assign(&mut self, rhs: IntEncoding<'a>) {
		match rhs {
			IntEncoding::Direct { first, vals } => {
				let mut k = first;
				for lit in vals {
					self.terms.push_back((*lit, k));
					k += 1;
				}
				self.constraints.push((Constraint::AtMostOne, vals.len()));
			}
			IntEncoding::Order { first, vals } => {
				for lit in vals {
					self.terms.push_back((*lit, 1));
				}
				self.add += first;
				self.constraints
					.push((Constraint::ImplicationChain, vals.len()));
			}
			IntEncoding::Log { signed, bits } => {
				let two = 1 + 1;
				let mut k = 1;
				for lit in bits {
					self.terms.push_front((*lit, k));
					k *= two;
				}
				// TODO!
				if signed {
					self.terms.front_mut().unwrap().1 *= -1;
				}
				self.num_free += bits.len();
			}
		}
	}
}

impl Default for BoolLinExp {
	fn default() -> Self {
		Self {
			terms: Default::default(),
			num_free: 0,
			constraints: Default::default(),
			add: 0,
			mult: 1,
		}
	}
}

impl Display for BoolLinExp {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}",
			self.terms
				.iter()
				.map(|(lit, c)| (lit, c * self.mult))
				.format_with(" + ", |elt, f| match elt.1 {
					1 => f(&format_args!("{}", elt.0)),
					-1 => f(&format_args!("-{}", elt.0)),
					_ => f(&format_args!("{}*{}", elt.1, elt.0)),
				})
		)?;
		if self.add != 0 {
			if !self.terms.is_empty() {
				write!(f, " + ")?;
			}
			write!(f, "{}", self.add)?;
		}
		Ok(())
	}
}

impl From<Coeff> for BoolLinExp {
	fn from(value: Coeff) -> Self {
		Self {
			add: value,
			..Default::default()
		}
	}
}

impl<'a> From<IntEncoding<'a>> for BoolLinExp {
	fn from(var: IntEncoding<'a>) -> Self {
		match var {
			IntEncoding::Direct { first, vals } => {
				let mut terms = VecDeque::with_capacity(vals.len());
				let mut k = first;
				for lit in vals {
					terms.push_back((*lit, k));
					k += 1;
				}
				Self {
					terms,
					constraints: vec![(Constraint::AtMostOne, vals.len())],
					..Default::default()
				}
			}
			IntEncoding::Order { first, vals } => Self {
				terms: vals.iter().map(|lit| (*lit, 1)).collect(),
				constraints: vec![(Constraint::ImplicationChain, vals.len())],
				add: first,
				..Default::default()
			},
			IntEncoding::Log { signed, bits } => {
				let mut terms = VecDeque::with_capacity(bits.len());
				let two = 1 + 1;
				let mut k = 1;
				for lit in bits {
					terms.push_back((*lit, k));
					k *= two;
				}
				if signed {
					terms.back_mut().unwrap().1 *= -1;
				}
				Self {
					terms,
					num_free: bits.len(),
					..Default::default()
				}
			}
		}
	}
}

impl From<Lit> for BoolLinExp {
	fn from(lit: Lit) -> Self {
		Self {
			terms: VecDeque::from([(lit, 1)]),
			num_free: 1,
			..Default::default()
		}
	}
}

impl From<bool> for BoolLinExp {
	fn from(b: bool) -> Self {
		Self {
			add: b.into(),
			..Default::default()
		}
	}
}

impl Mul<Coeff> for BoolLinExp {
	type Output = BoolLinExp;

	fn mul(mut self, rhs: Coeff) -> Self::Output {
		self *= rhs;
		self
	}
}

impl MulAssign<Coeff> for BoolLinExp {
	fn mul_assign(&mut self, rhs: Coeff) {
		self.mult *= rhs;
	}
}

impl Neg for BoolLinExp {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		self.mult = -self.mult;
		self
	}
}

impl Sub for BoolLinExp {
	type Output = Self;

	fn sub(self, rhs: Self) -> Self::Output {
		let mut res = self.clone();
		res -= rhs;
		res
	}
}

impl SubAssign for BoolLinExp {
	fn sub_assign(&mut self, rhs: Self) {
		self.add_assign(-rhs);
	}
}

impl BoolLinear {
	/// Create a new Boolean linear constraint from a left hand side Boolean
	/// linear expression, a comparator, and a right hand side coefficient.
	pub fn new(exp: BoolLinExp, cmp: Comparator, k: Coeff) -> Self {
		Self { exp, cmp, k }
	}

	/// Change the comparator of the Boolean linear constraint.
	pub fn set_cmp(&mut self, cmp: Comparator) {
		self.cmp = cmp;
	}

	#[cfg(any(feature = "tracing", test))]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(
			self.exp
				.terms
				.iter()
				.map(|(l, c)| format!("{c:?}·{}", trace_print_lit(l))),
			" + ",
		);
		let op = match self.cmp {
			Comparator::LessEq => "≤",
			Comparator::Equal => "=",
			Comparator::GreaterEq => "≥",
		};
		format!("{x} {op} {:?}", self.k)
	}
}

impl Checker for BoolLinear {
	fn check<F: Valuation + ?Sized>(&self, value: &F) -> Result<()> {
		let lhs = self.exp.value(value)?;
		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}
}

impl Display for BoolLinear {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{} {} {}",
			self.exp,
			match self.cmp {
				Comparator::Equal => "==",
				Comparator::LessEq => "<=",
				Comparator::GreaterEq => ">=",
			},
			self.k
		)
	}
}

impl From<NormalizedBoolLinear> for BoolLinear {
	fn from(lin: NormalizedBoolLinear) -> Self {
		BoolLinear {
			exp: BoolLinExp::from_terms(
				lin.terms
					.iter()
					.flat_map(|part| part.into_iter().map(|&(l, c)| (l, *c)))
					.collect_vec()
					.as_slice(),
			),
			cmp: lin.cmp.into(),
			k: *lin.k,
		}
	}
}

impl From<PosCoeff> for Coeff {
	fn from(val: PosCoeff) -> Self {
		val.0
	}
}

impl From<LimitComp> for Comparator {
	fn from(value: LimitComp) -> Self {
		match value {
			LimitComp::Equal => Comparator::Equal,
			LimitComp::LessEq => Comparator::LessEq,
		}
	}
}

// Automatically implement Cardinality encoding when you can encode Linear
// constraints
impl<Db, Enc> Encoder<Db, Cardinality> for Enc
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	Enc: Encoder<Db, NormalizedBoolLinear> + LinMarker,
{
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		self.encode(db, &NormalizedBoolLinear::from(con.clone()))
	}
}

impl Display for LimitComp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LimitComp::Equal => write!(f, "=="),
			LimitComp::LessEq => write!(f, "<="),
		}
	}
}

impl<Enc, Agg> LinearEncoder<Enc, Agg> {
	/// Change the [`BoolLinAggregator`] used by this encoder.
	pub fn with_linear_aggregator(&mut self, agg: Agg) -> &mut Self {
		self.agg = agg;
		self
	}

	/// Change the [`Encoder`] for [`BoolLinVariant`]s used by this encoder.
	pub fn with_variant_encoder(&mut self, enc: Enc) -> &mut Self {
		self.enc = enc;
		self
	}

	/// Create a new [`LinearEncoder`] with the given [`Encoder`] for
	/// [`BoolLinVariant`]s and [`BoolLinAggregator`].
	pub fn new(enc: Enc, agg: Agg) -> Self {
		Self { enc, agg }
	}
}

impl<Db, Enc> Encoder<Db, BoolLinear> for LinearEncoder<Enc>
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
	Enc: Encoder<Db, BoolLinVariant>,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "linear_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut Db, lin: &BoolLinear) -> Result {
		let variant = self.agg.aggregate(db, lin)?;
		self.enc.encode(db, &variant)
	}
}

impl NormalizedBoolLinear {
	/// Get the comparator of the linear constraint.
	pub fn comparator(&self) -> Comparator {
		self.cmp.clone().into()
	}

	/// Test whether the linear constraint has any terms.
	pub fn is_empty(&self) -> bool {
		self.terms.is_empty()
	}

	/// Iterate over the terms of the linear constraint, consisting of literals
	/// and the coefficients by which they are multiplied.
	pub fn iter_terms(&self) -> impl Iterator<Item = (Lit, Coeff)> + '_ {
		self.terms
			.iter()
			.flat_map(|part| part.iter().map(|&(lit, coef)| (lit, coef.into())))
	}

	/// Get the number of terms in the linear constraint.
	pub fn len(&self) -> usize {
		self.terms.len()
	}

	/// Get the right-hand side constant against which the linear constraint
	/// compares its left-hand side terms.
	pub fn rhs(&self) -> Coeff {
		self.k.into()
	}

	/// Set the right-hand side constant against which the linear constraint
	/// compares its left-hand side terms.
	pub fn set_rhs(&mut self, k: Coeff) {
		self.k = PosCoeff::new(k);
	}

	#[cfg(any(feature = "tracing", test))]
	pub(crate) fn trace_print(&self) -> String {
		use crate::trace::trace_print_lit;

		let x = itertools::join(
			self.terms
				.iter()
				.flat_map(|part| part.iter().map(|(lit, coef)| (lit, **coef)))
				.map(|(l, c)| format!("{c:?}·{}", trace_print_lit(l))),
			" + ",
		);
		let op = if self.cmp == LimitComp::LessEq {
			"≤"
		} else {
			"="
		};
		format!("{x} {op} {:?}", *self.k)
	}
}

impl Checker for NormalizedBoolLinear {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<()> {
		let sum: Coeff = self
			.terms
			.iter()
			.flat_map(|p| p.iter().copied())
			.filter_map(|(l, c)| {
				if sol.value(l) {
					Some(Coeff::from(c))
				} else {
					None
				}
			})
			.sum();
		if match self.cmp {
			LimitComp::LessEq => sum <= *self.k,
			LimitComp::Equal => sum == *self.k,
		} {
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}
}

impl From<Cardinality> for NormalizedBoolLinear {
	fn from(card: Cardinality) -> Self {
		Self {
			terms: card
				.lits
				.into_iter()
				.map(|l| Part::Amo(vec![(l, PosCoeff::new(1))]))
				.collect(),
			cmp: card.cmp,
			k: card.k,
		}
	}
}

impl From<CardinalityOne> for NormalizedBoolLinear {
	fn from(amo: CardinalityOne) -> Self {
		Self::from(Cardinality::from(amo))
	}
}

impl Part {
	pub(crate) fn iter(&self) -> impl Iterator<Item = &(Lit, PosCoeff)> {
		self.into_iter()
	}
}

impl<'a> IntoIterator for &'a Part {
	type IntoIter = std::slice::Iter<'a, (Lit, PosCoeff)>;
	type Item = &'a (Lit, PosCoeff);

	fn into_iter(self) -> Self::IntoIter {
		match self {
			Part::Amo(terms) => terms.iter(),
			Part::Ic(terms) => terms.iter(),
			Part::Dom(terms, _lb, _ub) => terms.iter(),
		}
	}
}

impl PosCoeff {
	pub(crate) fn new(c: Coeff) -> Self {
		if c < 0 {
			panic!("cannot create a PosCoeff with a negative value")
		}
		Self(c)
	}
}

impl Deref for PosCoeff {
	type Target = Coeff;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl DerefMut for PosCoeff {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl Display for PosCoeff {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl<LinEnc, CardEnc, AmoEnc> StaticLinEncoder<LinEnc, CardEnc, AmoEnc> {
	/// Get mutable access to the encoder that is used to encode
	/// [`BoolLinVariant::CardinalityOne`] variants.
	pub fn amo_encoder(&mut self) -> &mut AmoEnc {
		&mut self.amo_enc
	}

	/// Get mutable access to the encoder that is used to encode
	/// [`BoolLinVariant::Cardinality`] variants.
	pub fn card_encoder(&mut self) -> &mut CardEnc {
		&mut self.card_enc
	}

	/// Get mutable access to the encoder that is used to encode
	/// [`BoolLinVariant::Linear`] variants.
	pub fn lin_encoder(&mut self) -> &mut LinEnc {
		&mut self.lin_enc
	}

	/// Create a new [`StaticLinEncoder`] with the given encoders to encode
	/// [`BoolLinVariant::Linear`], [`BoolLinVariant::Cardinality`], and
	/// [`BoolLinVariant::CardinalityOne`] variants respectively.
	pub fn new(lin_enc: LinEnc, card_enc: CardEnc, amo_enc: AmoEnc) -> Self {
		Self {
			lin_enc,
			card_enc,
			amo_enc,
		}
	}
}

impl<Db, LinEnc, CardEnc, AmoEnc> Encoder<Db, BoolLinVariant>
	for StaticLinEncoder<LinEnc, CardEnc, AmoEnc>
where
	Db: ClauseDatabase + ?Sized,
	LinEnc: Encoder<Db, NormalizedBoolLinear>,
	CardEnc: Encoder<Db, Cardinality>,
	AmoEnc: Encoder<Db, CardinalityOne>,
{
	fn encode(&self, db: &mut Db, lin: &BoolLinVariant) -> Result {
		match &lin {
			BoolLinVariant::Linear(lin) => self.lin_enc.encode(db, lin),
			BoolLinVariant::Cardinality(card) => self.card_enc.encode(db, card),
			BoolLinVariant::CardinalityOne(amo) => self.amo_enc.encode(db, amo),
			BoolLinVariant::Trivial => Ok(()),
		}
	}
}

impl SwcEncoder {
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

impl<Db> Encoder<Db, NormalizedBoolLinear> for SwcEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut Db, lin: &NormalizedBoolLinear) -> Result {
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

		let ys = once(model.new_constant(0))
			.chain(
				(1..n)
					.map(|_| model.new_var((-(*lin.k)..=0).into(), self.add_consistency))
					.take(n),
			)
			.collect_vec()
			.into_iter()
			.chain(once(model.new_constant(-*lin.k)))
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

impl LinMarker for SwcEncoder {}

impl TotalizerEncoder {
	const EQUALIZE_INTERMEDIATES: bool = false;

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

impl TotalizerEncoder {
	fn build_totalizer(&self, xs: Vec<IntVarEnc>, cmp: &LimitComp, k: Coeff) -> Model {
		let mut model = Model::default();
		let mut layer = xs
			.into_iter()
			.map(|x| Rc::new(RefCell::new(model.add_int_var_enc(x))))
			.collect_vec();

		while layer.len() > 1 {
			let mut next_layer = Vec::<Rc<RefCell<IntVar>>>::new();
			for children in layer.chunks(2) {
				match children {
					[x] => {
						next_layer.push(Rc::clone(x));
					}
					[left, right] => {
						let at_root = layer.len() == 2;
						let dom = if at_root {
							(k..=k).into()
						} else {
							left.borrow()
								.dom
								.iter()
								.flatten()
								.cartesian_product(right.borrow().dom.iter().flatten())
								.map(|(a, b)| a + b)
								.filter(|&d| d <= k)
								.map(|v| v..=v)
								.collect()
						};
						let parent =
							Rc::new(RefCell::new(model.new_var(dom, self.add_consistency)));

						model.cons.push(Lin::tern(
							Rc::clone(left),
							Rc::clone(right),
							if !at_root && Self::EQUALIZE_INTERMEDIATES {
								LimitComp::Equal
							} else {
								cmp.clone()
							},
							Rc::clone(&parent),
						));
						next_layer.push(parent);
					}
					_ => panic!(),
				}
			}
			layer = next_layer;
		}

		model
	}
}

impl<Db> Encoder<Db, NormalizedBoolLinear> for TotalizerEncoder
where
	Db: ClauseDatabase + AsDynClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "totalizer_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut Db, lin: &NormalizedBoolLinear) -> Result {
		let xs = lin
			.terms
			.iter()
			.enumerate()
			.flat_map(|(i, part)| IntVarEnc::from_part(db, part, lin.k, format!("x_{i}")))
			.sorted_by_key(|x| x.ub())
			.collect_vec();

		// The totalizer encoding constructs a binary tree starting from a layer of
		// leaves
		let mut model = self.build_totalizer(xs, &lin.cmp, *lin.k);
		model.propagate(&self.add_propagation, vec![model.cons.len() - 1]);
		model.encode(db, self.cutoff)
	}
}

impl LinMarker for TotalizerEncoder {}

#[cfg(test)]
mod tests {
	macro_rules! linear_test_suite {
		($module:ident, $encoder:expr) => {
			mod $module {
				use traced_test::test;

				use crate::{
					bool_linear::{
						tests::construct_terms, LimitComp, NormalizedBoolLinear, PosCoeff,
					},
					helpers::tests::{assert_solutions, expect_file},
					ClauseDatabaseTools, Cnf, Encoder,
				};

				#[test]
				fn small_le_1() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[(a, 2), (b, 3), (c, 5)]),
								cmp: LimitComp::LessEq,
								k: PosCoeff::new(6),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_le_1.sol"],
					);
				}

				#[test]
				fn small_le_2() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let d = cnf.new_lit();
					let e = cnf.new_lit();
					let f = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[
									(!a, 3),
									(!b, 6),
									(!c, 1),
									(!d, 2),
									(!e, 3),
									(!f, 6),
								]),
								cmp: LimitComp::LessEq,
								k: PosCoeff::new(19),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d, e, f],
						&expect_file!["linear/test_small_le_2.sol"],
					);
				}

				#[test]
				fn small_le_3() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[(a, 1), (b, 2), (c, 4)]),
								cmp: LimitComp::LessEq,
								k: PosCoeff::new(5),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_le_3.sol"],
					);
				}

				#[test]
				fn small_le_4() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[(a, 4), (b, 6), (c, 7)]),
								cmp: LimitComp::LessEq,
								k: PosCoeff::new(10),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_le_4.sol"],
					);
				}

				#[test]
				fn small_eq_1() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[(a, 1), (b, 2), (c, 4)]),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(5),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_eq_1.sol"],
					);
				}

				#[test]
				fn small_eq_2() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[(a, 1), (b, 2), (c, 3)]),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(3),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c],
						&expect_file!["linear/test_small_eq_2.sol"],
					);
				}

				#[test]
				fn small_eq_3() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let d = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[(a, 2), (b, 3), (c, 5), (d, 7)]),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(10),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_small_eq_3.sol"],
					);
				}

				#[test]
				fn small_eq_4() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let d = cnf.new_lit();
					$encoder
						.encode(
							&mut cnf,
							&NormalizedBoolLinear {
								terms: construct_terms(&[(a, 2), (b, 1), (c, 2), (d, 2)]),
								cmp: LimitComp::Equal,
								k: PosCoeff::new(4),
							},
						)
						.unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_small_eq_4.sol"],
					);
				}
			}
		};
	}

	use std::{cmp::Ordering, num::NonZeroI32};

	use itertools::Itertools;
	pub(crate) use linear_test_suite;
	use traced_test::test;

	use crate::{
		bool_linear::{
			AdderEncoder, BoolLinAggregator, BoolLinExp, BoolLinVariant, BoolLinear, Comparator,
			LimitComp, LinearEncoder, NormalizedBoolLinear, Part, PosCoeff, StaticLinEncoder,
			TotalizerEncoder,
		},
		cardinality::{tests::card_test_suite, Cardinality},
		cardinality_one::{tests::card1_test_suite, CardinalityOne, PairwiseEncoder},
		helpers::tests::{assert_checker, assert_encoding, assert_solutions, expect_file},
		sorted::SortedEncoder,
		ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Encoder, Lit, Unsatisfiable,
	};

	#[test]
	fn aggregator_at_least_one_negated() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		// Correctly detect that all but one literal can be set to true
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::LessEq,
					3
				)
			),
			Ok(BoolLinVariant::Trivial)
		);
		assert_encoding(
			&cnf,
			&expect_file!["linear/aggregator/test_at_least_one_negated.cnf"],
		);

		// Correctly detect equal k
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1], &[a, b, c]),
					Comparator::Equal,
					2
				)
			),
			// actually leaves over a CardinalityOne constraint
			Ok(BoolLinVariant::CardinalityOne(CardinalityOne {
				lits: vec![!a, !b, !c],
				cmp: LimitComp::LessEq,
			}))
		);
	}

	#[test]
	fn aggregator_combine() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		// Simple aggregation of multiple occurrences of the same literal
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[(1, 3), (2, 1), (3, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(3)
			}))
		);

		// Aggregation of positive and negative occurrences of the same literal
		// x1 +2*~x1 + ... <= 3
		// x1 +2 -2*x1 + ... <= 3
		// x1 -2*x1 + ... <= 1
		// -1*x1 + ... <= 1
		// +1*~x1 + ... <= 2
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 1, 2], &[a, !a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[(!a, 1), (b, 1), (c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2)
			}))
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, -2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					2,
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[(!a, 1), (b, 1), (c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(3)
			}))
		);

		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_detection() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();

		// Correctly detect at most one
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1], &[a, b, c]),
					Comparator::LessEq,
					1
				)
			),
			Ok(BoolLinVariant::CardinalityOne(CardinalityOne {
				lits: vec![a, b, c],
				cmp: LimitComp::LessEq
			}))
		);
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[2, 2, 2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(BoolLinVariant::CardinalityOne(CardinalityOne {
				lits: vec![a, b, c],
				cmp: LimitComp::LessEq
			}))
		);

		// Correctly detect at most k
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::LessEq,
					2
				)
			),
			Ok(BoolLinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2),
			}))
		);
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[3, 3, 3, 3], &[a, b, c, d]),
					Comparator::LessEq,
					7
				)
			),
			Ok(BoolLinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2),
			}))
		);

		// Correctly detect equal k
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::Equal,
					2
				)
			),
			Ok(BoolLinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::Equal,
				k: PosCoeff::new(2),
			}))
		);
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[3, 3, 3, 3], &[a, b, c, d]),
					Comparator::Equal,
					6
				)
			),
			Ok(BoolLinVariant::Cardinality(Cardinality {
				lits: vec![a, b, c, d],
				cmp: LimitComp::Equal,
				k: PosCoeff::new(2),
			}))
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[(a, 1), (b, 2), (c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(2),
			}))
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &[a, b, c]),
					Comparator::Equal,
					2
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[(a, 1), (b, 2), (c, 2)]),
				cmp: LimitComp::Equal,
				k: PosCoeff::new(2),
			}))
		);

		// Correctly identify that the AMO is limiting the LHS ub
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_terms(&[(c, -1)]).add_choice(&[(a, -1), (b, -1)]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(BoolLinVariant::Trivial)
		);
	}

	#[test]
	fn aggregator_equal_one() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(3).iter_lits().collect_vec();
		// An exactly one constraint adds an exactly one constraint
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1], &vars),
					Comparator::Equal,
					1
				)
			),
			Ok(BoolLinVariant::CardinalityOne(CardinalityOne {
				lits: vars,
				cmp: LimitComp::Equal
			}))
		);
		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_false_trivial_unsat() {
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f, g) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 1, 1, 4, 1, 1], &[a, !b, c, d, !e, f, !g]),
					Comparator::GreaterEq,
					7
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[
					(e, 4),
					(b, 2),
					(g, 1),
					(!d, 1),
					(!a, 1),
					(!f, 1),
					(!c, 1)
				]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);
		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_neg_coeff() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();

		// Correctly convert a negative coefficient
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[2, 3, -2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[(a, 2), (b, 3), (!c, 2)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[-1, -1, -1], &[a, b, c]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(BoolLinVariant::CardinalityOne(CardinalityOne {
				lits: vec![!a, !b, !c],
				cmp: LimitComp::LessEq
			}))
		);
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[-1, -2, -3], &[a, b, c]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: construct_terms(&[(!a, 1), (!b, 2), (!c, 3)]),
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);

		// Correctly convert multiple negative coefficients with AMO constraints
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::default()
						.add_choice(&[(a, -1), (b, -3), (c, -4)])
						.add_choice(&[(d, -2), (e, -3), (f, -5)]),
					Comparator::LessEq,
					-4,
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![
					Part::Amo(vec![
						(a, PosCoeff::new(3)),
						(b, PosCoeff::new(1)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(4))
					]),
					Part::Amo(vec![
						(d, PosCoeff::new(3)),
						(e, PosCoeff::new(2)),
						(Lit(NonZeroI32::new(8).unwrap()), PosCoeff::new(5))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(5),
			}))
		);

		// Correctly convert multiple negative coefficients with side constraints
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::default().add_chain(&[
						(a, 1),
						(b, -3),
						(c, -2),
						(d, 2),
						(e, 5),
						(f, -3)
					]),
					Comparator::LessEq,
					3
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![
					Part::Ic(vec![
						(a, PosCoeff::new(1)),
						(d, PosCoeff::new(2)),
						(e, PosCoeff::new(5))
					]),
					Part::Ic(vec![
						(!f, PosCoeff::new(3)),
						(!c, PosCoeff::new(2)),
						(!b, PosCoeff::new(3))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(11),
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::default()
						.add_choice(&[(a, 1), (b, 2), (c, 3), (d, 4)])
						.add_choice(&[(e, 1), (f, 3)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![
					Part::Amo(vec![
						(a, PosCoeff::new(3)),
						(b, PosCoeff::new(2)),
						(c, PosCoeff::new(1)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(4))
					]),
					Part::Amo(vec![
						(e, PosCoeff::new(2)),
						(Lit(NonZeroI32::new(8).unwrap()), PosCoeff::new(3))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4), // -3 + 4 + 3
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::default()
						.add_chain(&[(a, 1), (b, 1), (c, 1), (d, 1)])
						.add_chain(&[(e, 1), (f, 2)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![
					Part::Ic(vec![
						(!d, PosCoeff::new(1)),
						(!c, PosCoeff::new(1)),
						(!b, PosCoeff::new(1)),
						(!a, PosCoeff::new(1)),
					]),
					Part::Ic(vec![(!f, PosCoeff::new(2)), (!e, PosCoeff::new(1))]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(4),
			}))
		);

		// Correctly account for the coefficient in the Dom bounds
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::default().add_bounded_log_encoding(&[(a, 1), (b, 2), (c, 4)], 0, 3),
					Comparator::LessEq,
					5,
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![Part::Dom(
					vec![
						(a, PosCoeff::new(1)),
						(b, PosCoeff::new(2)),
						(c, PosCoeff::new(4))
					],
					PosCoeff::new(0),
					PosCoeff::new(7)
				),],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(5),
			}))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e) = cnf.new_lits();
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::default()
						.add_bounded_log_encoding(&[(a, 1), (b, 2), (c, 4)], 0, 5)
						.add_bounded_log_encoding(&[(d, 3), (e, 6)], 0, 2),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![
					Part::Dom(
						vec![
							(!a, PosCoeff::new(1)),
							(!b, PosCoeff::new(2)),
							(!c, PosCoeff::new(4))
						],
						PosCoeff::new(2),
						PosCoeff::new(7),
					),
					Part::Dom(
						vec![(!d, PosCoeff::new(3)), (!e, PosCoeff::new(6))],
						PosCoeff::new(7),
						PosCoeff::new(9),
					),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(13),
			}))
		);
	}

	#[test]
	fn aggregator_sort_same_coefficients() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();

		assert_eq!(
			BoolLinAggregator::default()
				.sort_same_coefficients(SortedEncoder::default(), 2)
				.aggregate(
					&mut cnf,
					&BoolLinear::new(
						BoolLinExp::from_slices(&[3, 3, 5, 3], &[a, b, d, c]),
						Comparator::LessEq,
						10
					)
				),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![
					Part::Ic(vec![
						(Lit(NonZeroI32::new(5).unwrap()), PosCoeff::new(3)),
						(Lit(NonZeroI32::new(6).unwrap()), PosCoeff::new(3)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(3))
					]),
					Part::Amo(vec![(d, PosCoeff::new(5))]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(10),
			}))
		);
	}

	#[test]
	fn aggregator_sort_same_coefficients_using_minimal_chain() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(5).iter_lits().collect_vec();
		assert_eq!(
			BoolLinAggregator::default()
				.sort_same_coefficients(SortedEncoder::default(), 2)
				.aggregate(
					&mut cnf,
					&BoolLinear::new(
						BoolLinExp::from_slices(&[5, 5, 5, 5, 4], &vars),
						Comparator::LessEq,
						12 // only need 2 to sort
					)
				),
			Ok(BoolLinVariant::Linear(NormalizedBoolLinear {
				terms: vec![
					Part::Amo(vec![(*vars.last().unwrap(), PosCoeff::new(4))]),
					Part::Ic(vec![
						(Lit(NonZeroI32::new(6).unwrap()), PosCoeff::new(5)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(5))
					]),
				],
				cmp: LimitComp::LessEq,
				k: PosCoeff::new(12),
			}))
		);
	}

	#[test]
	fn aggregator_unsat() {
		let mut db = Cnf::default();
		let vars = db.new_var_range(3).iter_lits().collect_vec();

		// Constant cannot be reached
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut db,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::Equal,
					6
				)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut db,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::GreaterEq,
					6,
				)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut db,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::LessEq,
					-1
				)
			),
			Err(Unsatisfiable)
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			BoolLinAggregator::default().aggregate(
				&mut db,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[4, 4, 4], &vars),
					Comparator::Equal,
					6
				)
			),
			Err(Unsatisfiable)
		);
	}

	pub(crate) fn construct_terms<L: Into<Lit> + Clone>(terms: &[(L, Coeff)]) -> Vec<Part> {
		terms
			.iter()
			.map(|(lit, coef)| Part::Amo(vec![(lit.clone().into(), PosCoeff::new(*coef))]))
			.collect()
	}

	#[test]
	fn encoders() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		// TODO encode this if encoder does not support constraint
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		PairwiseEncoder::default()
			.encode(
				&mut cnf,
				&CardinalityOne {
					lits: vec![c, d],
					cmp: LimitComp::LessEq,
				},
			)
			.unwrap();
		// +7*x1 +10*x2 +4*x3 +4*x4 <= 9
		LinearEncoder::<StaticLinEncoder<AdderEncoder>>::default()
			.encode(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::default()
						.add_choice(&[(a, 7), (b, 10)])
						.add_choice(&[(c, 4), (d, 4)]),
					Comparator::LessEq,
					9,
				),
			)
			.unwrap();

		assert_solutions(
			&cnf,
			vec![a, b, c, d],
			&expect_file!["linear/adder/test_encoders.sol"],
		);
	}

	#[test]
	fn pb_encode() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(4).iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder>::default()
			.encode(
				&mut cnf,
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1, 2], &vars),
					Comparator::LessEq,
					1,
				),
			)
			.unwrap();

		assert_encoding(&cnf, &expect_file!["linear/adder/test_pb_encode.cnf"]);
		assert_solutions(&cnf, vars, &expect_file!["linear/adder/test_pb_encode.sol"]);
	}

	#[test]
	fn sort_same_coefficients_2() {
		let mut db = Cnf::default();
		let vars = db.new_var_range(5).iter_lits().collect_vec();
		let mut agg = BoolLinAggregator::default();
		let _ = agg.sort_same_coefficients(SortedEncoder::default(), 3);
		let mut encoder = LinearEncoder::<StaticLinEncoder<TotalizerEncoder>>::default();
		let _ = encoder.with_linear_aggregator(agg);
		let con = BoolLinear::new(
			BoolLinExp::from_slices(&[3, 3, 1, 1, 3], &vars),
			Comparator::GreaterEq,
			2,
		);
		encoder.encode(&mut db, &con).unwrap();
		assert_checker(&db, &con);
	}

	impl PartialEq for BoolLinVariant {
		fn eq(&self, other: &Self) -> bool {
			let liteq =
				|a: &Vec<Lit>, b: &Vec<Lit>| itertools::equal(a.iter().sorted(), b.iter().sorted());
			let parteq = |a: &Vec<Part>, b: &Vec<Part>| {
				itertools::equal(
					a.iter().map(|p| p.iter().sorted().collect_vec()).sorted(),
					b.iter().map(|p| p.iter().sorted().collect_vec()).sorted(),
				)
			};
			match self {
				BoolLinVariant::Linear(NormalizedBoolLinear { terms, cmp, k }) => {
					if let BoolLinVariant::Linear(NormalizedBoolLinear {
						terms: oterms,
						cmp: oc,
						k: l,
					}) = other
					{
						cmp == oc && k == l && parteq(terms, oterms)
					} else {
						false
					}
				}
				BoolLinVariant::Cardinality(Cardinality { lits, cmp, k }) => {
					if let BoolLinVariant::Cardinality(Cardinality {
						lits: olits,
						cmp: oc,
						k: l,
					}) = other
					{
						cmp == oc && k == l && liteq(lits, olits)
					} else {
						false
					}
				}
				BoolLinVariant::CardinalityOne(amo) => {
					if let BoolLinVariant::CardinalityOne(oamo) = other {
						liteq(&amo.lits, &oamo.lits)
					} else {
						false
					}
				}
				BoolLinVariant::Trivial => {
					matches!(other, BoolLinVariant::Trivial)
				}
			}
		}
	}

	impl PartialEq for Part {
		fn eq(&self, other: &Self) -> bool {
			let term_eq = |a: &Vec<(_, _)>, b: &Vec<(_, _)>| {
				itertools::equal(a.iter().sorted(), b.iter().sorted())
			};
			match self {
				Part::Amo(terms) => {
					if let Part::Amo(oterms) = other {
						term_eq(terms, oterms)
					} else {
						false
					}
				}
				Part::Ic(terms) => {
					if let Part::Ic(oterms) = other {
						term_eq(terms, oterms)
					} else {
						false
					}
				}
				Part::Dom(terms, l, u) => {
					if let Part::Dom(oterms, ol, ou) = other {
						term_eq(terms, oterms) && l == ol && u == ou
					} else {
						false
					}
				}
			}
		}
	}

	impl PartialOrd for Part {
		fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
			let termcmp = |a: &Vec<(Lit, PosCoeff)>, b: &Vec<(Lit, PosCoeff)>| {
				let cmp = a.len().cmp(&b.len());
				if cmp != Ordering::Equal {
					cmp
				} else {
					for (a, b) in a.iter().sorted().zip_eq(other.iter().sorted()) {
						let cmp = a.0.cmp(&b.0);
						if cmp != Ordering::Equal {
							return cmp;
						}
						let cmp = a.1.cmp(&b.1);
						if cmp != Ordering::Equal {
							return cmp;
						}
					}
					Ordering::Equal
				}
			};
			Some(match self {
				Part::Amo(terms) => {
					if let Part::Amo(oterms) = other {
						termcmp(terms, oterms)
					} else {
						Ordering::Less
					}
				}
				Part::Ic(terms) => {
					if let Part::Ic(oterms) = other {
						termcmp(terms, oterms)
					} else {
						Ordering::Greater
					}
				}
				Part::Dom(terms, _, _) => {
					if let Part::Dom(oterms, _, _) = other {
						termcmp(terms, oterms)
					} else {
						Ordering::Less
					}
				}
			})
		}
	}

	card_test_suite!(AdderEncoder::default());
	card1_test_suite! {
		adder_encoder_card1, crate::bool_linear::AdderEncoder::default()
	}
	linear_test_suite! {adder_encoder, crate::bool_linear::AdderEncoder::default()}

	// FIXME: BDD does not support LimitComp::Equal
	// card1_test_suite!(BddEncoder::default());
	linear_test_suite! {bdd_encoder, crate::bool_linear::BddEncoder::default()}

	// FIXME: SWC does not support LimitComp::Equal
	// card1_test_suite!(SwcEncoder::default());
	linear_test_suite! {swc_encoder, crate::bool_linear::SwcEncoder::default()}

	// FIXME: Totalizer does not support LimitComp::Equal
	// card1_test_suite!(TotalizerEncoder::default());
	linear_test_suite!(
		totalizer_encoder,
		crate::bool_linear::TotalizerEncoder::default()
	);
}
