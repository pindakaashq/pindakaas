//! This module contains representations and encoding algorithms for general
//! Boolean linear constraints.
//!
//! Boolean linear constraints can be modelled using [`LinExp`] and
//! subsequently [`Linear`]. These representations can then be normalized
//! and simplified using
//! [`BoolLinAggregator`](crate::aggregator::BoolLinAggregator), which reads the
//! integers a group of literals stands for and yields a
//! [`NormalizedIntLinear`](crate::int_linear::NormalizedIntLinear). That is
//! what the [`AdderEncoder`], [`BddEncoder`], [`SwcEncoder`] and
//! [`TotalizerEncoder`] encode.
//!
//! This module contains some additional helper types that can be used to
//! simplify this encoding process.
//! [`StaticLinEncoder`](crate::aggregator::StaticLinEncoder) can help choose an
//! encoder based on the [`LinVariant`](crate::aggregator::LinVariant) produced
//! by [`BoolLinAggregator`](crate::aggregator::BoolLinAggregator).
//! [`LinearEncoder`](crate::aggregator::LinearEncoder) can be used to pipeline
//! [`BoolLinAggregator`](crate::aggregator::BoolLinAggregator) and a
//! [`LinVariant`](crate::aggregator::LinVariant) [`Encoder`].

use std::{
	cmp::{max, min, Ordering},
	fmt::{self, Display},
	iter::once,
	ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Neg, Range, Sub, SubAssign},
};

use itertools::Itertools;
use rangelist::RangeList;

use crate::{
	cardinality::Cardinality,
	cardinality_one::CardinalityOne,
	decision::integer::{lex_leq_const, Consistency, IntVar},
	helpers::{as_binary, bit, new_named_lit},
	int_linear::{
		Decompose, IntLinConfig, IntLinEncoder, NormalizedIntLinear, Term, TernaryIntLinear,
	},
	propositional_logic::{Formula, TseitinEncoder},
	BoolVal, Checker, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Lit, Result,
	Unsatisfiable, Valuation,
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

#[derive(Clone, Debug)]
/// A linear combination of boolean variables, where Boolean literals are
/// multiplied by constant coefficients and added together.
pub struct LinExp {
	/// The terms of the expression, in the order they were written.
	pub(crate) terms: Vec<LinTerm>,
	/// Additive constant
	pub(crate) add: Coeff,
	/// Multiplicative contant
	pub(crate) mult: Coeff,
}

/// A term of a linear expression, and what it is worth.
///
/// A literal counts for its coefficient when it holds and nothing when it does
/// not; an integer variable counts for its coefficient times whichever of its
/// values it takes.
#[derive(Clone, Debug)]
pub enum LinTerm {
	/// A Boolean literal.
	Bool(Lit, Coeff),
	/// An integer variable.
	Int(IntVar, Coeff),
}

impl LinTerm {
	/// What the term is multiplied by.
	pub fn coefficient(&self) -> Coeff {
		match self {
			LinTerm::Bool(_, c) | LinTerm::Int(_, c) => *c,
		}
	}

	/// The term with its coefficient multiplied by `c`.
	fn scaled(self, c: Coeff) -> Self {
		match self {
			LinTerm::Bool(l, w) => LinTerm::Bool(l, w * c),
			LinTerm::Int(x, w) => LinTerm::Int(x, w * c),
		}
	}
}

#[derive(Debug, Clone)]
/// A Boolean linear constraint that can be used to constrain a linear
/// combination of boolean variables.
///
/// Note that this type of constraint is often referred to in literature under
/// the more general term of pseudo-Boolean constraints.
///
/// The constraint compares a [`LinExp`] to a constant using a
/// [`Comparator`], where the expression takes the left hand side of the
/// comparison and the constant takes the right hand side.
pub struct Linear {
	/// Expression being constrained
	pub(crate) exp: LinExp,
	/// Comparator when exp is on the left hand side and k is on the right hand
	/// side
	pub(crate) cmp: Comparator,
	/// Coefficient providing the upper bound or lower bound to exp, or both
	pub(crate) k: Coeff,
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

impl Comparator {
	/// The comparator that holds when the sides are swapped.
	pub(crate) fn reverse(self) -> Self {
		match self {
			Comparator::LessEq => Comparator::GreaterEq,
			Comparator::Equal => Comparator::Equal,
			Comparator::GreaterEq => Comparator::LessEq,
		}
	}

	/// The inequalities that together mean the same as this comparator.
	pub(crate) fn split(self) -> Vec<Self> {
		match self {
			Comparator::Equal => vec![Comparator::LessEq, Comparator::GreaterEq],
			cmp => vec![cmp],
		}
	}
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
/// A comparator that has been limited to a either `Equal` or `LessEq`.
///
/// This type is used to ensure that the comparator of [`Cardinality`] and
/// [`CardinalityOne`] constraints, and of a normalized linear constraint, are
/// limited to a specific set of values.
pub(crate) enum LimitComp {
	Equal,
	LessEq,
}

// TODO add EO, and probably something for Unconstrained
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// PosCoeff is a type for coefficients that are guaranteed by the programmer to
/// be 0 or greater.
pub struct PosCoeff(pub(crate) Coeff);

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Sorted Weight
/// Counter (SWC)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SwcEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

/// Encode the constraint that ∑ coeffᵢ·litsᵢ ≦ k using a Generalized
/// Totalizer (GT)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TotalizerEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	cutoff: Option<Coeff>,
}

/// Above this many literals, enumerating the assignments of the wrong parity
/// costs more clauses than a Tseitin transformation costs auxiliary variables.
const DIRECT_PARITY_LITS: usize = 4;

impl AdderEncoder {
	/// Encode the adder carry circuit, i.e. whether at least two of `xs` are
	/// true.
	///
	/// The carry is constrained to equal `out` when given, and otherwise
	/// created, or returned directly when the fixed bits already determine it.
	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "carry_circuit", skip_all, fields(constraint = Self::trace_print_carry(xs, &out))))]
	pub(crate) fn carry_circuit<Db>(
		db: &mut Db,
		xs: &[BoolVal],
		out: Option<BoolVal>,
		_label: String,
	) -> Result<BoolVal>
	where
		Db: ClauseDatabase + ?Sized,
	{
		let (lits, trues) = Self::filter_fixed_sum(xs);
		// With fewer than two free literals the fixed bits settle the carry.
		let determined = match lits[..] {
			[] => Some(BoolVal::Const(trues >= 2)),
			[x] => Some(match trues {
				0 => BoolVal::Const(false),
				1 => x,
				_ => BoolVal::Const(true),
			}),
			_ => None,
		};
		if let Some(c) = determined {
			return match out {
				None => Ok(c),
				Some(out) => {
					db.add_clause([!c, out])?;
					db.add_clause([c, !out])?;
					Ok(out)
				}
			};
		}

		let carry = out.unwrap_or_else(|| BoolVal::Lit(new_named_lit!(db, _label)));
		match lits[..] {
			[x, y] if trues == 0 => {
				// carry = x ∧ y
				db.add_clause([!x, !y, carry])?;
				db.add_clause([x, !carry])?;
				db.add_clause([y, !carry])?;
			}
			[x, y] => {
				debug_assert_eq!(trues, 1);
				// carry = x ∨ y
				db.add_clause([x, y, !carry])?;
				db.add_clause([!x, carry])?;
				db.add_clause([!y, carry])?;
			}
			[x, y, z] => {
				debug_assert_eq!(trues, 0);
				// Two false inputs force no carry, two true inputs force one.
				db.add_clause([x, y, !carry])?;
				db.add_clause([x, z, !carry])?;
				db.add_clause([y, z, !carry])?;
				db.add_clause([!x, !y, carry])?;
				db.add_clause([!x, !z, carry])?;
				db.add_clause([!y, !z, carry])?;
			}
			_ => unreachable!("a full adder has at most three inputs"),
		}
		Ok(carry)
	}

	/// Split `xs` into its literals and the number of its bits fixed to one.
	fn filter_fixed_sum(xs: &[BoolVal]) -> (Vec<BoolVal>, usize) {
		let mut trues = 0;
		let lits = xs
			.iter()
			.filter(|x| match x {
				BoolVal::Lit(_) => true,
				BoolVal::Const(b) => {
					trues += usize::from(*b);
					false
				}
			})
			.copied()
			.collect();
		(lits, trues)
	}

	/// Ripple-carry adder over the binary encodings `xs` and `ys`.
	///
	/// When `zs` is given the sum is *constrained* to equal it; otherwise the
	/// sum bits are created and returned, truncated to `bits` (defaulting to
	/// the width needed to hold any sum, so that no overflow is possible).
	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "ripple_carry_adder", skip_all, fields(constraint = format!("{xs:?} + {ys:?} = {zs:?}"))))]
	pub(crate) fn ripple_carry_adder<Db>(
		db: &mut Db,
		xs: &[BoolVal],
		ys: &[BoolVal],
		bits: Option<usize>,
		zs: Option<&[BoolVal]>,
	) -> Result<Vec<BoolVal>>
	where
		Db: ClauseDatabase + ?Sized,
	{
		// A given sum may be wider than the inputs can reach, and its top bits
		// still have to be driven to zero rather than left free.
		let max_bits = max(max(xs.len(), ys.len()) + 1, zs.map_or(0, <[_]>::len));
		let bits = bits.unwrap_or(max_bits);
		let mut c = BoolVal::Const(false);
		(0..max_bits)
			.map(|i| {
				let (x, y) = (bit(xs, i), bit(ys, i));
				let z = match zs {
					// Relational: the sum bit is given, so constrain it.
					Some(zs) => Some(bit(zs, i)),
					// Functional: create a bit, unless it is past the requested
					// width and therefore has to be zero.
					None if i < bits => None,
					None => Some(BoolVal::Const(false)),
				};
				let z = Self::sum_circuit(db, &[x, y, c], z, format!("z_{i}"))?;
				c = Self::carry_circuit(db, &[x, y, c], None, format!("c_{}", i + 1))?;
				Ok(z)
			})
			.collect()
	}

	/// Encode the adder sum circuit, i.e. `out ≡ xs[0] ⊕ .. ⊕ xs[n]`.
	///
	/// The sum is constrained to equal `out` when given, and otherwise created.
	#[cfg_attr(any(feature = "tracing", test), tracing::instrument(name = "sum_circuit", skip_all, fields(constraint = Self::trace_print_sum(xs, &out))))]
	pub(crate) fn sum_circuit<Db>(
		db: &mut Db,
		xs: &[BoolVal],
		out: Option<BoolVal>,
		_label: String,
	) -> Result<BoolVal>
	where
		Db: ClauseDatabase + ?Sized,
	{
		let out = out.unwrap_or_else(|| BoolVal::Lit(new_named_lit!(db, _label)));
		// `out = ⊕xs` is exactly `⊕xs ⊕ out = 0`, and each bit fixed to one
		// flips the parity the remaining literals have to add up to.
		let (lits, trues) = Self::filter_fixed_sum(&[xs, &[out]].concat());
		let target = (trues % 2) as u32;
		if lits.is_empty() {
			return if target == 0 {
				Ok(out)
			} else {
				Err(Unsatisfiable)
			};
		}
		if lits.len() > DIRECT_PARITY_LITS {
			let xor = Formula::Xor(lits.into_iter().map(Formula::Atom).collect_vec());
			TseitinEncoder.encode(
				db,
				&if target == 1 {
					xor
				} else {
					Formula::Not(Box::new(xor))
				},
			)?;
			return Ok(out);
		}
		// Forbid every assignment of the wrong parity. That is `2ⁿ⁻¹` clauses
		// and no auxiliary variables, which beats Tseitin at adder widths.
		for assign in 0..(1_u32 << lits.len()) {
			if assign.count_ones() % 2 != target {
				db.add_clause(lits.iter().enumerate().map(|(i, &x)| {
					if assign & (1 << i) == 0 {
						x
					} else {
						!x
					}
				}))?;
			}
		}
		Ok(out)
	}

	#[cfg(any(feature = "tracing", test))]
	fn trace_print_carry(input: &[BoolVal], output: &Option<BoolVal>) -> String {
		let inner = itertools::join(input.iter().map(|l| format!("{l}")), " + ");
		match output {
			None => format!("_ ≡ ({inner} > 1)"),
			Some(BoolVal::Lit(r)) => {
				format!("{} ≡ ({} > 1)", crate::trace::trace_print_lit(r), inner)
			}
			Some(BoolVal::Const(true)) => format!("{inner} > 1"),
			Some(BoolVal::Const(false)) => format!("{inner} ≤ 1"),
		}
	}

	#[cfg(any(feature = "tracing", test))]
	fn trace_print_sum(input: &[BoolVal], output: &Option<BoolVal>) -> String {
		let inner = itertools::join(input.iter().map(|l| format!("{l}")), " ⊻ ");
		match output {
			None => format!("_ ≡ {inner}"),
			Some(BoolVal::Lit(r)) => format!("{} ≡ {}", crate::trace::trace_print_lit(r), inner),
			Some(BoolVal::Const(true)) => inner,
			Some(BoolVal::Const(false)) => format!("¬({inner})"),
		}
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for AdderEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "adder_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		let cmp = con.cmp();
		// Adding bit by bit has no use for how the terms are grouped, so the
		// constraint is weighed back out into the literals standing for it.
		let (weighed, constant) = con.as_weighted(db)?;
		let rhs = con.k() - constant;
		if rhs < 0 {
			return db.contradiction();
		}
		if rhs == 0 {
			// Every coefficient is positive, so a sum of zero is every literal
			// being false, whichever way it is compared.
			return weighed
				.into_iter()
				.try_for_each(|(lit, _)| db.add_clause([!lit]));
		}
		let rhs = PosCoeff::new(rhs);

		// The number of relevant bits in k
		const ZERO: Coeff = 0;
		let bits = ZERO.leading_zeros() - rhs.leading_zeros();
		let mut k = as_binary(rhs, Some(bits));

		let first_zero = rhs.trailing_ones() as usize;
		let bits = bits as usize;
		debug_assert!(k[bits - 1]);

		let all_terms = || {
			weighed
				.iter()
				.map(|&(lit, coef)| (lit, PosCoeff::new(coef)))
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
					if k[b] && cmp == LimitComp::Equal {
						return db.contradiction();
					}
				}
				1 => {
					let x = bucket[b].pop().unwrap();
					if cmp == LimitComp::Equal {
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
						let lits = lits.into_iter().map(BoolVal::Lit).collect_vec();

						// Compute sum
						if last && cmp == LimitComp::Equal {
							// No need to create a new literal, force the sum to equal the result
							let _ = Self::sum_circuit(
								db,
								&lits,
								Some(BoolVal::Const(k[b])),
								String::new(),
							)?;
						} else if cmp != LimitComp::LessEq || !last || b >= first_zero {
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
							let _ = Self::sum_circuit(
								db,
								&lits,
								Some(BoolVal::Lit(sum)),
								String::new(),
							)?;
							bucket[b].push(sum);
						}

						// Compute carry
						if b + 1 >= bits {
							// Carry will bring the sum to be greater than k, force to be false
							if lits.len() == 2 && cmp == LimitComp::Equal {
								// Already encoded by the XOR to compute the sum
							} else {
								let _ = Self::carry_circuit(
									db,
									&lits,
									Some(BoolVal::Const(false)),
									String::new(),
								)?;
							}
						} else if last && cmp == LimitComp::Equal && bucket[b + 1].is_empty() {
							// No need to create a new literal, force the carry to equal the result
							let _ = Self::carry_circuit(
								db,
								&lits,
								Some(BoolVal::Const(k[b + 1])),
								String::new(),
							)?;
							// Mark k[b + 1] as false (otherwise next step will fail)
							k[b + 1] = false;
						} else {
							let carry_lit = new_named_lit!(
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
							let _ = Self::carry_circuit(
								db,
								&lits,
								Some(BoolVal::Lit(carry_lit)),
								String::new(),
							)?;
							bucket[b + 1].push(carry_lit);
						}
					}
					debug_assert!(
						(cmp == LimitComp::Equal && bucket[b].is_empty())
							|| (cmp == LimitComp::LessEq
								&& (bucket[b].len() == 1 || b < first_zero))
					);
					sum[b] = bucket[b].pop();
				}
			}
		}
		// In case of equality this has been enforced
		debug_assert!(cmp != LimitComp::Equal || sum.iter().all(|x| x.is_none()));

		// Enforce less-than constraint
		if cmp == LimitComp::LessEq {
			// A bucket that stayed empty means that bit of the sum is zero.
			let sum = sum
				.iter()
				.map(|&l| l.map_or(BoolVal::Const(false), BoolVal::Lit))
				.collect_vec();
			lex_leq_const(db, &sum, rhs, bits)?;
		}
		Ok(())
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for AdderEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for AdderEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
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

		let views = xs[i]
			.values()
			.into_iter()
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

	fn construct_bdd(xs: &[Term], cmp: Comparator, k: Coeff) -> Vec<Vec<(Range<Coeff>, BddNode)>> {
		let bounds = xs
			.iter()
			.scan((0, 0), |state, x| {
				*state = (state.0 + x.min(), state.1 + x.max());
				Some(*state)
			})
			.chain(once((0, k)))
			.collect_vec();

		let margins = xs
			.iter()
			.rev()
			.scan((k, k), |state, x| {
				*state = (state.0 - x.max(), state.1 - x.min());
				Some(*state)
			})
			.collect_vec();

		let inf = xs.iter().fold(0, |a, x| a + x.max()) + 1;

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
	fn encoder(&self) -> IntLinEncoder {
		IntLinEncoder::with_config(IntLinConfig {
			cutoff: self.cutoff,
			..IntLinConfig::default()
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
	) -> Result<Vec<TernaryIntLinear>, Unsatisfiable> {
		// The narrowest terms first, which is the order the diagram is reduced
		// under in the literature. A layer then tends to agree with the one
		// after it from some total upwards, and where it does it shares that
		// literal rather than paying for one of its own. Taking the widest
		// first narrows the layers sooner but leaves nothing to share.
		let terms = con
			.terms()
			.iter()
			.cloned()
			.sorted_by(|a: &Term, b: &Term| a.max().cmp(&b.max()))
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
				TernaryIntLinear::new(
					Term::new(1, layers[i].clone()),
					x,
					cmp,
					Term::new(1, layers[i + 1].clone()),
				)
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

impl LinExp {
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
		self.terms.push(LinTerm::Bool(lit, 1));
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
			terms: lits
				.iter()
				.zip(coeffs)
				.map(|(&l, &c)| LinTerm::Bool(l, c))
				.collect(),
			..Default::default()
		}
	}

	/// Create a linear expression from a slice of terms, where each term
	/// consist of a literal and coefficient and the former will be multiplied
	/// by the latter.
	pub fn from_terms(terms: &[(Lit, Coeff)]) -> Self {
		Self {
			terms: terms.iter().map(|&(l, c)| LinTerm::Bool(l, c)).collect(),
			..Default::default()
		}
	}

	/// Iterate over the terms of the linear expression, consisting of a literal
	/// and the coefficient by which it is multiplied.
	pub fn terms(&self) -> impl Iterator<Item = (Lit, Coeff)> + '_ {
		self.terms.iter().filter_map(|t| match t {
			LinTerm::Bool(l, c) => Some((*l, *c)),
			LinTerm::Int(..) => None,
		})
	}

	/// Iterate over the terms of the expression that are integer variables,
	/// each with the coefficient by which it is multiplied.
	pub fn int_terms(&self) -> impl Iterator<Item = (&IntVar, Coeff)> + '_ {
		self.terms.iter().filter_map(|t| match t {
			LinTerm::Int(x, c) => Some((x, *c)),
			LinTerm::Bool(..) => None,
		})
	}

	pub(crate) fn value<F: Valuation + ?Sized>(&self, sol: &F) -> Result<Coeff> {
		let mut total = self.add;
		for term in &self.terms {
			total += match term {
				LinTerm::Bool(l, c) if sol.value(*l) => *c,
				LinTerm::Bool(..) => 0,
				LinTerm::Int(x, c) => c * x.value(sol),
			};
		}
		Ok(total * self.mult)
	}
}

impl Add for LinExp {
	type Output = LinExp;

	fn add(mut self, rhs: Self) -> Self::Output {
		self += rhs;
		self
	}
}

impl Add<Coeff> for LinExp {
	type Output = LinExp;

	fn add(mut self, rhs: Coeff) -> Self::Output {
		self += rhs;
		self
	}
}

impl AddAssign for LinExp {
	fn add_assign(&mut self, rhs: Self) {
		// The pending multiplier reaches everything already here before
		// anything is added beside it.
		if self.mult != 1 {
			self.add *= self.mult;
			for term in self.terms.drain(..).collect_vec() {
				self.terms.push(term.scaled(self.mult));
			}
		}
		self.mult = 1;
		self.add += rhs.add * rhs.mult;
		self.terms
			.extend(rhs.terms.into_iter().map(|t| t.scaled(rhs.mult)));
	}
}

impl AddAssign<Coeff> for LinExp {
	fn add_assign(&mut self, rhs: Coeff) {
		self.add += rhs;
	}
}

impl Default for LinExp {
	fn default() -> Self {
		Self {
			terms: Default::default(),
			add: 0,
			mult: 1,
		}
	}
}

impl Display for LinExp {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"{}",
			self.terms
				.iter()
				.map(|t| match t {
					LinTerm::Bool(l, c) => (format!("{l}"), c * self.mult),
					LinTerm::Int(x, c) => (format!("{x}"), c * self.mult),
				})
				.format_with(" + ", |(name, c), f| match c {
					1 => f(&format_args!("{name}")),
					-1 => f(&format_args!("-{name}")),
					_ => f(&format_args!("{c}*{name}")),
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

impl From<Coeff> for LinExp {
	fn from(value: Coeff) -> Self {
		Self {
			add: value,
			..Default::default()
		}
	}
}

impl From<IntVar> for LinExp {
	fn from(x: IntVar) -> Self {
		Self {
			terms: vec![LinTerm::Int(x, 1)],
			..Default::default()
		}
	}
}

impl Mul<Coeff> for IntVar {
	type Output = LinExp;

	fn mul(self, rhs: Coeff) -> Self::Output {
		LinExp {
			terms: vec![LinTerm::Int(self, rhs)],
			..Default::default()
		}
	}
}

impl Add<IntVar> for LinExp {
	type Output = LinExp;

	fn add(self, rhs: IntVar) -> Self::Output {
		self + LinExp::from(rhs)
	}
}

impl From<Lit> for LinExp {
	fn from(lit: Lit) -> Self {
		Self {
			terms: vec![LinTerm::Bool(lit, 1)],
			..Default::default()
		}
	}
}

impl From<bool> for LinExp {
	fn from(b: bool) -> Self {
		Self {
			add: b.into(),
			..Default::default()
		}
	}
}

impl Mul<Coeff> for LinExp {
	type Output = LinExp;

	fn mul(mut self, rhs: Coeff) -> Self::Output {
		self *= rhs;
		self
	}
}

impl MulAssign<Coeff> for LinExp {
	fn mul_assign(&mut self, rhs: Coeff) {
		self.mult *= rhs;
	}
}

impl Neg for LinExp {
	type Output = Self;

	fn neg(mut self) -> Self::Output {
		self.mult = -self.mult;
		self
	}
}

impl Sub for LinExp {
	type Output = Self;

	fn sub(self, rhs: Self) -> Self::Output {
		let mut res = self.clone();
		res -= rhs;
		res
	}
}

impl SubAssign for LinExp {
	fn sub_assign(&mut self, rhs: Self) {
		self.add_assign(-rhs);
	}
}

impl Linear {
	/// Create a new Boolean linear constraint from a left hand side Boolean
	/// linear expression, a comparator, and a right hand side coefficient.
	pub fn new(exp: LinExp, cmp: Comparator, k: Coeff) -> Self {
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
			self.exp.terms.iter().map(|t| match t {
				LinTerm::Bool(l, c) => format!("{c:?}·{}", trace_print_lit(l)),
				LinTerm::Int(x, c) => format!("{c:?}·{}", x.label()),
			}),
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

impl Checker for Linear {
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

impl Display for Linear {
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

impl Display for LimitComp {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LimitComp::Equal => write!(f, "=="),
			LimitComp::LessEq => write!(f, "<="),
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

impl Default for SwcEncoder {
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

impl SwcEncoder {
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

impl Decompose for SwcEncoder {
	/// Carry a running total along the terms, one at a time.
	///
	/// Each step passes on what is left of the bound after the term it sees, so
	/// the totals telescope: adding the steps together leaves the first total
	/// against the last, which is the constraint. Counting down from nothing to
	/// minus the bound keeps every total within it.
	fn decompose<Db: ClauseDatabase + ?Sized>(
		&self,
		_db: &mut Db,
		con: &NormalizedIntLinear,
	) -> Result<Vec<TernaryIntLinear>, Unsatisfiable> {
		// Two terms or fewer are already as small as the chain would make them.
		if con.terms().len() <= 2 {
			return Ok(vec![con.into()]);
		}
		let (cmp, k, n) = (Comparator::from(con.cmp()), con.k(), con.terms().len());
		let totals = (0..=n)
			.map(|i| {
				// The ends are fixed, so that what the chain proves between
				// them is the constraint itself.
				let domain = match i {
					0 => 0..=0,
					_ if i == n => -k..=-k,
					_ => -k..=0,
				};
				IntVar::new(domain)
					.enforce_consistency(self.add_consistency)
					.with_label(format!("y{i}"))
			})
			.collect_vec();

		Ok(con
			.terms()
			.iter()
			.zip(totals.iter().tuple_windows())
			.map(|(x, (carried, left))| {
				TernaryIntLinear::new(
					x.clone(),
					Term::new(1, left.clone()),
					cmp,
					Term::new(1, carried.clone()),
				)
			})
			.collect())
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for SwcEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "swc_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		self.encoder().encode_decomposed(db, con, self)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for SwcEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for SwcEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
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
		if con.terms().len() <= 2 {
			return Ok(vec![con.into()]);
		}
		let (cmp, k) = (Comparator::from(con.cmp()), con.k());
		let mut cons = Vec::new();
		// Start from the narrowest, so that the wide terms meet late and the
		// intermediates below them stay small.
		let mut layer = con
			.terms()
			.iter()
			.cloned()
			.sorted_by_key(|t| t.max() - t.min())
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
							left.values()
								.into_iter()
								.cartesian_product(right.values())
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
							Term::new(1, parent.clone()),
						));
						next.push(Term::new(1, parent));
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
pub(crate) mod tests {
	macro_rules! linear_test_suite {
		($module:ident, $encoder:expr) => {
			mod $module {
				use traced_test::test;

				use crate::helpers::tests::prelude::*;

				#[test]
				fn small_le_1() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 2), (b, 3), (c, 5)]),
						LimitComp::LessEq,
						PosCoeff::new(6),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

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
					let con = NormalizedIntLinear::from_terms(
						construct_terms(
							&mut cnf,
							&[(!a, 3), (!b, 6), (!c, 1), (!d, 2), (!e, 3), (!f, 6)],
						),
						LimitComp::LessEq,
						PosCoeff::new(19),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

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
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 1), (b, 2), (c, 4)]),
						LimitComp::LessEq,
						PosCoeff::new(5),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

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
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 4), (b, 6), (c, 7)]),
						LimitComp::LessEq,
						PosCoeff::new(10),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

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
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 1), (b, 2), (c, 4)]),
						LimitComp::Equal,
						PosCoeff::new(5),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

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
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 1), (b, 2), (c, 3)]),
						LimitComp::Equal,
						PosCoeff::new(3),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

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
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 2), (b, 3), (c, 5), (d, 7)]),
						LimitComp::Equal,
						PosCoeff::new(10),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

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
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 2), (b, 1), (c, 2), (d, 2)]),
						LimitComp::Equal,
						PosCoeff::new(4),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_small_eq_4.sol"],
					);
				}

				/// Encode the at-most-one constraint over each of the `groups`, so
				/// that the solutions of the formula can be compared against those
				/// of encoders that ignore the grouping of the terms.
				fn amo(cnf: &mut Cnf, groups: &[&[Lit]]) {
					for lits in groups {
						PairwiseEncoder::default()
							.encode(
								cnf,
								&CardinalityOne {
									lits: lits.to_vec(),
									cmp: LimitComp::LessEq,
								},
							)
							.unwrap();
					}
				}

				#[test]
				fn choice_le() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b], &[c, d]]);
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[(a, PosCoeff::new(3)), (b, PosCoeff::new(5))],
								"x0",
								false,
							)
							.unwrap(),
							Term::from_at_most_one(
								&mut cnf,
								&[(c, PosCoeff::new(2)), (d, PosCoeff::new(4))],
								"x1",
								false,
							)
							.unwrap(),
						],
						LimitComp::LessEq,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_le.sol"],
					);
				}

				#[test]
				fn choice_eq() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b], &[c, d]]);
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[(a, PosCoeff::new(3)), (b, PosCoeff::new(5))],
								"x0",
								true,
							)
							.unwrap(),
							Term::from_at_most_one(
								&mut cnf,
								&[(c, PosCoeff::new(2)), (d, PosCoeff::new(4))],
								"x1",
								true,
							)
							.unwrap(),
						],
						LimitComp::Equal,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_eq.sol"],
					);
				}

				#[test]
				fn choice_shared_coefficient() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b, c]]);
					// Two of the mutually exclusive terms share a coefficient.
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[
									(a, PosCoeff::new(3)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(5)),
								],
								"x0",
								false,
							)
							.unwrap(),
							Term::from_at_most_one(&mut cnf, &[(d, PosCoeff::new(4))], "x1", false)
								.unwrap(),
						],
						LimitComp::LessEq,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_shared_coefficient.sol"],
					);
				}

				#[test]
				fn choice_shared_coefficient_eq() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					amo(&mut cnf, &[&[a, b, c]]);
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_at_most_one(
								&mut cnf,
								&[
									(a, PosCoeff::new(3)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(5)),
								],
								"x0",
								true,
							)
							.unwrap(),
							Term::from_at_most_one(&mut cnf, &[(d, PosCoeff::new(4))], "x1", true)
								.unwrap(),
						],
						LimitComp::Equal,
						PosCoeff::new(7),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_choice_shared_coefficient_eq.sol"],
					);
				}

				#[test]
				fn chain_le() {
					let mut cnf = Cnf::default();
					let (a, b, c, d) = cnf.new_lits();
					// The literal of each term is implied by the literal of the next.
					for (x, y) in [(a, b), (b, c)] {
						cnf.add_clause([!y, x]).unwrap();
					}
					let con = NormalizedIntLinear::from_terms(
						vec![
							Term::from_implication_chain(
								&mut cnf,
								&[
									(a, PosCoeff::new(2)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(4)),
								],
								"x0",
							)
							.unwrap(),
							Term::from_at_most_one(&mut cnf, &[(d, PosCoeff::new(5))], "x1", false)
								.unwrap(),
						],
						LimitComp::LessEq,
						PosCoeff::new(8),
					);
					$encoder.encode(&mut cnf, &con).unwrap();

					assert_solutions(
						&cnf,
						vec![a, b, c, d],
						&expect_file!["linear/test_chain_le.sol"],
					);
				}

				#[test]
				fn issue_177() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let con = NormalizedIntLinear::from_terms(
						construct_terms(&mut cnf, &[(a, 3), (b, 9)]),
						LimitComp::Equal,
						PosCoeff::new(10),
					);
					let res = $encoder.encode(&mut cnf, &con);
					if res.is_ok() {
						assert_solutions(
							&cnf,
							vec![a, b],
							&expect_file!["linear/test_issue_177.sol"],
						);
					}
				}
			}
		};
	}

	use std::num::NonZeroI32;

	use itertools::Itertools;
	use traced_test::test;

	use crate::{
		aggregator::{BoolLinAggregator, LinVariant, LinearEncoder, StaticLinEncoder},
		bool_linear::{
			AdderEncoder, BddEncoder, Comparator, LimitComp, LinExp, Linear, PosCoeff, SwcEncoder,
			TotalizerEncoder,
		},
		cardinality::tests::card_test_suite,
		cardinality_one::{tests::card1_test_suite, CardinalityOne, PairwiseEncoder},
		helpers::tests::{
			all_binary_solutions, assert_checker, assert_encoding, assert_solutions,
			binary_literals, expect_file,
		},
		int_linear::Term,
		constraint::sorted::SortedEncoder,
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Coeff, Encoder, Lit, Unsatisfiable,
	};

	/// An aggregated constraint as a test wants to read it: what each group of
	/// terms is worth, and what the sum is compared against.
	///
	/// A group is an integer by the time aggregation is done, so what it is
	/// worth is read back off whichever encoding it was given — which for every
	/// kind of group gives the literals and coefficients it was made from.
	#[derive(Debug, PartialEq)]
	pub(crate) enum Aggregated {
		Cardinality(Vec<Lit>, LimitComp, Coeff),
		CardinalityOne(Vec<Lit>, LimitComp),
		Linear(Vec<Vec<(Lit, Coeff)>>, LimitComp, Coeff),
		Trivial,
	}

	/// Aggregate `con` and read the result back.
	fn aggregated(
		db: &mut Cnf,
		agg: &BoolLinAggregator,
		con: &Linear,
	) -> Result<Aggregated, Unsatisfiable> {
		Ok(match agg.aggregate(db, con)? {
			LinVariant::Linear(lin) => {
				let (cmp, k) = (lin.cmp(), lin.k());
				Aggregated::Linear(sorted_weights(lin.grouped_weights(db)?), cmp, k)
			}
			LinVariant::Cardinality(card) => Aggregated::Cardinality(
				card.iter_lits().collect(),
				into_limit(card.comparator()),
				card.rhs(),
			),
			LinVariant::CardinalityOne(amo) => {
				Aggregated::CardinalityOne(amo.iter_lits().collect(), into_limit(amo.comparator()))
			}
			LinVariant::Trivial => Aggregated::Trivial,
		})
	}

	/// A comparator as normalisation leaves it, which is never `≥`.
	fn into_limit(cmp: Comparator) -> LimitComp {
		match cmp {
			Comparator::Equal => LimitComp::Equal,
			_ => LimitComp::LessEq,
		}
	}

	/// Groups in a settled order, neither the grouping nor what is in one
	/// depending on which way round they came out.
	fn sorted_weights(mut groups: Vec<Vec<(Lit, Coeff)>>) -> Vec<Vec<(Lit, Coeff)>> {
		for group in &mut groups {
			group.sort();
		}
		groups.sort();
		groups
	}

	#[test]
	fn ripple_carry_adder_computes_the_sum() {
		for (x_bits, y_bits) in [(1, 1), (2, 2), (3, 1)] {
			let mut cnf = Cnf::default();
			let (x, y) = (
				binary_literals(&mut cnf, x_bits),
				binary_literals(&mut cnf, y_bits),
			);
			let z = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, None).unwrap();

			let solutions = all_binary_solutions(&cnf, &[&x, &y, &z]);
			// The sum is wide enough to never overflow, so every assignment of
			// the inputs extends to exactly one model.
			assert_eq!(solutions.len(), 1 << (x_bits + y_bits));
			for s in &solutions {
				assert_eq!(s[2], s[0] + s[1], "{} + {} != {}", s[0], s[1], s[2]);
			}
		}
	}

	#[test]
	fn ripple_carry_adder_handles_fixed_bits() {
		// Shifting and grounding a binary encoding leaves constant bits in it,
		// so the adder has to fold them into the sum and the carry rather than
		// assume every bit is a literal.
		let mut cnf = Cnf::default();
		let x = vec![
			BoolVal::Const(true),
			BoolVal::Lit(cnf.new_lit()),
			BoolVal::Const(false),
		];
		let y = vec![BoolVal::Const(true), BoolVal::Lit(cnf.new_lit())];
		let z = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, None).unwrap();

		let solutions = all_binary_solutions(&cnf, &[&x, &y, &z]);
		assert_eq!(solutions.len(), 4);
		for s in &solutions {
			assert_eq!(s[2], s[0] + s[1], "{} + {} != {}", s[0], s[1], s[2]);
		}
	}

	#[test]
	fn ripple_carry_adder_constrains_a_given_sum() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			binary_literals(&mut cnf, 2),
			binary_literals(&mut cnf, 2),
			binary_literals(&mut cnf, 2),
		);
		let _ = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, Some(&z)).unwrap();

		let solutions = all_binary_solutions(&cnf, &[&x, &y, &z]);
		// `z` is only two bits wide, so sums that do not fit are ruled out.
		let expected: Vec<Vec<Coeff>> = (0..4)
			.flat_map(|a| (0..4).map(move |b| (a, b)))
			.filter(|(a, b)| a + b < 4)
			.map(|(a, b)| vec![a, b, a + b])
			.collect();
		assert_eq!(solutions, expected);
	}

	#[test]
	fn aggregator_at_least_one_negated() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		// Correctly detect that all but one literal can be set to true
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::LessEq,
					3
				)
			),
			Ok(Aggregated::Trivial)
		);
		assert_encoding(
			&cnf,
			&expect_file!["linear/aggregator/test_at_least_one_negated.cnf"],
		);

		// Correctly detect equal k
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, 1, 1], &[a, b, c]),
					Comparator::Equal,
					2
				)
			),
			// actually leaves over a CardinalityOne constraint
			Ok(Aggregated::CardinalityOne(
				vec![!a, !b, !c],
				LimitComp::LessEq
			))
		);
	}

	#[test]
	fn a_bound_of_zero_leaves_no_term_standing() {
		// Every coefficient is positive by the time an encoder sees it, so a
		// sum that has to come to nothing is every literal being false. The
		// adder has no bits to work with in that case, which is only reachable
		// at all because a constraint with integer terms keeps its bound.
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let y = crate::decision::integer::IntVar::new(0..=3).with_label("y");
		let con = Linear::new(a * 2 + y.clone() * 3, Comparator::LessEq, 0);
		let LinVariant::Linear(con) = BoolLinAggregator::default()
			.aggregate(&mut cnf, &con)
			.unwrap()
		else {
			panic!("a literal and an integer make a linear constraint");
		};
		cnf.encode(&con, &AdderEncoder::default()).unwrap();

		use crate::{
			solver::{cadical::Cadical, SolveResult, Solver},
			Valuation,
		};
		let mut slv = Cadical::from(&cnf);
		let SolveResult::Satisfied(value) = slv.solve() else {
			panic!("nothing being chosen satisfies it");
		};
		assert!(!value.value(a) && y.value(&value) == 0);
	}

	#[test]
	fn an_expression_may_mix_literals_and_integers() {
		// `a * 3 + y * 5` reads the same whichever kind each side is, and the
		// two come apart again in aggregation: the literal is grouped into the
		// integer it stands for, the integer passes through as it came.
		let mut cnf = Cnf::default();
		let a = cnf.new_lit();
		let y = crate::decision::integer::IntVar::new(0..=3).with_label("y");

		let con = Linear::new(a * 3 + y.clone() * 5, Comparator::LessEq, 11);
		let LinVariant::Linear(con) = BoolLinAggregator::default()
			.aggregate(&mut cnf, &con)
			.unwrap()
		else {
			panic!("a literal and an integer make a linear constraint");
		};
		assert_eq!(con.terms().len(), 2, "one term of each kind");
		cnf.encode(&con, &crate::int_linear::IntLinEncoder::default())
			.unwrap();

		use crate::{
			solver::{cadical::Cadical, SolveResult, Solver},
			Valuation,
		};
		let mut slv = Cadical::from(&cnf);
		let vars = cnf.get_variables();
		while let crate::solver::SolveResult::Satisfied(value) =
			crate::solver::Solver::solve(&mut slv)
		{
			assert!(
				Coeff::from(value.value(a)) * 3 + y.value(&value) * 5 <= 11,
				"every model of the encoding satisfies the constraint"
			);
			let no_good: Vec<Lit> = vars
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			if slv.add_clause(no_good).is_err() {
				break;
			}
		}
	}

	#[test]
	fn aggregator_zero_coefficient() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		// A term that cannot contribute to the sum is dropped entirely, rather
		// than kept with a coefficient of zero
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[0, 2, 3, 4], &[a, b, c, d]),
					Comparator::LessEq,
					8
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![vec![(b, 2)], vec![(c, 3)], vec![(d, 4)]]),
				LimitComp::LessEq,
				8
			))
		);
	}

	#[test]
	fn aggregator_gcd() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		// 2a + 4b + 6c ≤ 7 is divided by 2, rounding the right hand side down
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[2, 4, 6], &[a, b, c]),
					Comparator::LessEq,
					7
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![vec![(a, 1)], vec![(b, 2)], vec![(c, 3)]]),
				LimitComp::LessEq,
				3
			))
		);

		// An equality that does not sit on a multiple of the divisor is
		// unsatisfiable
		let mut cnf = Cnf::default();
		let (a, b) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(LinExp::from_slices(&[2, 4], &[a, b]), Comparator::Equal, 5)
			),
			Err(Unsatisfiable)
		);

		// Dropping terms whose coefficient exceeds k can leave behind a set of
		// coefficients with a larger common divisor than the constraint started
		// with, which is why normalization runs after that step. Here
		// gcd(3, 3, 3, 7) is 1, but once 7d is dropped the rest divides by 3,
		// leaving `a + b + c ≤ 1`.
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[3, 3, 3, 7], &[a, b, c, d]),
					Comparator::LessEq,
					5
				)
			),
			Ok(Aggregated::CardinalityOne(vec![a, b, c], LimitComp::LessEq))
		);

		// The same under `=`: once 7d is dropped the remaining sum can only reach
		// multiples of 3, so it can never equal 5.
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[3, 3, 3, 7], &[a, b, c, d]),
					Comparator::Equal,
					5
				)
			),
			Err(Unsatisfiable)
		);

		// Coprime coefficients are left untouched
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[2, 3, 4], &[a, b, c]),
					Comparator::LessEq,
					7
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![vec![(a, 2)], vec![(b, 3)], vec![(c, 4)]]),
				LimitComp::LessEq,
				7
			))
		);
	}

	#[test]
	fn aggregator_combine() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		// Simple aggregation of multiple occurrences of the same literal
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, 2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![
					vec![(1.into(), 3)],
					vec![(2.into(), 1)],
					vec![(3.into(), 2)]
				]),
				LimitComp::LessEq,
				3
			))
		);

		// Aggregation of positive and negative occurrences of the same literal
		// x1 +2*~x1 + ... <= 3
		// x1 +2 -2*x1 + ... <= 3
		// x1 -2*x1 + ... <= 1
		// -1*x1 + ... <= 1
		// +1*~x1 + ... <= 2
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, 2, 1, 2], &[a, !a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![vec![(!a, 1)], vec![(b, 1)], vec![(c, 2)]]),
				LimitComp::LessEq,
				2
			))
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, -2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					2,
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![vec![(!a, 1)], vec![(b, 1)], vec![(c, 2)]]),
				LimitComp::LessEq,
				3
			))
		);

		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_equal_one() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(3).iter_lits().collect_vec();
		// An exactly one constraint adds an exactly one constraint
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(LinExp::from_slices(&[1, 1, 1], &vars), Comparator::Equal, 1)
			),
			Ok(Aggregated::CardinalityOne(vars, LimitComp::Equal))
		);
		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_false_trivial_unsat() {
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f, g) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, 2, 1, 1, 4, 1, 1], &[a, !b, c, d, !e, f, !g]),
					Comparator::GreaterEq,
					7
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![
					vec![(e, 4)],
					vec![(b, 2)],
					vec![(g, 1)],
					vec![(!d, 1)],
					vec![(!a, 1)],
					vec![(!f, 1)],
					vec![(!c, 1)]
				]),
				LimitComp::LessEq,
				4
			))
		);
		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_sort_same_coefficients() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();

		assert_eq!(
			aggregated(
				&mut cnf,
				BoolLinAggregator::default().sort_same_coefficients(SortedEncoder::default(), 2),
				&Linear::new(
					LinExp::from_slices(&[3, 3, 5, 3], &[a, b, d, c]),
					Comparator::LessEq,
					10
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![
					vec![
						(Lit(NonZeroI32::new(5).unwrap()), 3),
						(Lit(NonZeroI32::new(6).unwrap()), 3),
						(Lit(NonZeroI32::new(7).unwrap()), 3)
					],
					vec![(d, 5)],
				]),
				LimitComp::LessEq,
				10
			))
		);
	}

	#[test]
	fn aggregator_sort_same_coefficients_using_minimal_chain() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(5).iter_lits().collect_vec();
		assert_eq!(
			aggregated(
				&mut cnf,
				BoolLinAggregator::default().sort_same_coefficients(SortedEncoder::default(), 2),
				&Linear::new(
					LinExp::from_slices(&[5, 5, 5, 5, 4], &vars),
					Comparator::LessEq,
					12 // only need 2 to sort
				)
			),
			Ok(Aggregated::Linear(
				sorted_weights(vec![
					vec![(*vars.last().unwrap(), 4)],
					vec![
						(Lit(NonZeroI32::new(6).unwrap()), 5),
						(Lit(NonZeroI32::new(7).unwrap()), 5)
					],
				]),
				LimitComp::LessEq,
				12
			))
		);
	}

	#[test]
	fn aggregator_unsat() {
		let mut db = Cnf::default();
		let vars = db.new_var_range(3).iter_lits().collect_vec();

		// Constant cannot be reached
		assert_eq!(
			aggregated(
				&mut db,
				&BoolLinAggregator::default(),
				&Linear::new(LinExp::from_slices(&[1, 2, 2], &vars), Comparator::Equal, 6)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			aggregated(
				&mut db,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::GreaterEq,
					6,
				)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			aggregated(
				&mut db,
				&BoolLinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::LessEq,
					-1
				)
			),
			Err(Unsatisfiable)
		);

		// Scaled counting constraint with off-scaled Constant
		assert_eq!(
			aggregated(
				&mut db,
				&BoolLinAggregator::default(),
				&Linear::new(LinExp::from_slices(&[4, 4, 4], &vars), Comparator::Equal, 6)
			),
			Err(Unsatisfiable)
		);
	}

	/// A term that nothing else constrains is an integer worth its coefficient
	/// when its literal holds, which is a group of one.
	pub(crate) fn construct_terms<L: Into<Lit> + Clone>(
		db: &mut Cnf,
		terms: &[(L, Coeff)],
	) -> Vec<Term> {
		terms
			.iter()
			.enumerate()
			.map(|(i, (lit, coef))| {
				let group = [(lit.clone().into(), PosCoeff::new(*coef))];
				Term::from_at_most_one(db, &group, &format!("x{i}"), false).unwrap()
			})
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
				&Linear::new(
					LinExp::from_slices(&[7, 10, 4, 4], &[a, b, c, d]),
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
	fn what_the_decompositions_cost() {
		// Clause counts for each way of decomposing a pseudo-Boolean
		// constraint. The `.sol` goldens these encoders already have are blind
		// to size, so this is the only thing standing between a decomposition
		// getting quietly worse and nobody noticing.
		let cases: [(&str, &[Coeff], Coeff); 5] = [
			("card-10", &[1; 10], 5),
			("pb-small", &[1, 2, 3, 4, 5], 8),
			("pb-mid", &[2, 3, 5, 7, 11, 13], 20),
			("pb-wide", &[1, 2, 4, 8, 16, 32, 64], 70),
			("pb-coprime", &[3, 5, 7, 11, 13, 17], 40),
		];
		let mut table = format!(
			"{:>11} {:>4} {:>6} {:>7} {:>8} {:>9}\n",
			"case", "cmp", "enc", "vars", "clauses", "literals"
		);
		for (name, coeffs, k) in cases {
			for cmp in [Comparator::LessEq, Comparator::Equal] {
				for enc in ["adder", "bdd", "swc", "gt"] {
					let mut cnf = Cnf::default();
					let vars = cnf.new_var_range(coeffs.len()).iter_lits().collect_vec();
					let con = Linear::new(LinExp::from_slices(coeffs, &vars), cmp.clone(), k);
					let done = match enc {
						"adder" => LinearEncoder::<StaticLinEncoder<AdderEncoder>>::default()
							.encode(&mut cnf, &con),
						"bdd" => LinearEncoder::<StaticLinEncoder<BddEncoder>>::default()
							.encode(&mut cnf, &con),
						"swc" => LinearEncoder::<StaticLinEncoder<SwcEncoder>>::default()
							.encode(&mut cnf, &con),
						_ => LinearEncoder::<StaticLinEncoder<TotalizerEncoder>>::default()
							.encode(&mut cnf, &con),
					};
					let cmp = if cmp == Comparator::LessEq {
						"<="
					} else {
						"=="
					};
					table += &match done {
						Err(Unsatisfiable) => {
							format!("{name:>11} {cmp:>4} {enc:>6} {:>27}\n", "unsatisfiable")
						}
						Ok(()) => format!(
							"{name:>11} {cmp:>4} {enc:>6} {:>7} {:>8} {:>9}\n",
							cnf.num_vars(),
							cnf.num_clauses(),
							cnf.literals()
						),
					};
				}
			}
		}
		expect_file!("linear/decompositions.size").assert_eq(&table);
	}

	#[test]
	fn pb_encode() {
		let mut cnf = Cnf::default();
		let vars = cnf.new_var_range(4).iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder>::default()
			.encode(
				&mut cnf,
				&Linear::new(
					LinExp::from_slices(&[1, 1, 1, 2], &vars),
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
		let con = Linear::new(
			LinExp::from_slices(&[3, 3, 1, 1, 3], &vars),
			Comparator::GreaterEq,
			2,
		);
		encoder.encode(&mut db, &con).unwrap();
		assert_checker(&db, &con);
	}

	card_test_suite!(crate::bool_linear::AdderEncoder::default());
	card1_test_suite! {
		adder_encoder_card1, crate::bool_linear::AdderEncoder::default()
	}
	linear_test_suite! {adder_encoder, crate::bool_linear::AdderEncoder::default()}

	linear_test_suite! {int_lin_encoder, crate::int_linear::IntLinEncoder::default()}

	card1_test_suite! {
		bdd_encoder_card1, crate::bool_linear::BddEncoder::default()
	}
	linear_test_suite! {bdd_encoder, crate::bool_linear::BddEncoder::default()}

	card1_test_suite! {
		swc_encoder_card1, crate::bool_linear::SwcEncoder::default()
	}
	linear_test_suite! {swc_encoder, crate::bool_linear::SwcEncoder::default()}

	card1_test_suite! {
		totalizer_encoder_card1, crate::bool_linear::TotalizerEncoder::default()
	}
	linear_test_suite!(
		totalizer_encoder,
		crate::bool_linear::TotalizerEncoder::default()
	);

	// Test propagation feature
	linear_test_suite!(
		totalizer_encoder_prop_bounds,
		crate::bool_linear::TotalizerEncoder::default()
			.with_propagation(crate::decision::integer::Consistency::Bounds)
	);

	linear_test_suite!(
		totalizer_encoder_prop_doms,
		crate::bool_linear::TotalizerEncoder::default()
			.with_propagation(crate::decision::integer::Consistency::Domain)
	);

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
		cnf.encode(&con, &crate::bool_linear::BddEncoder::default())
			.unwrap();

		assert_eq!(
			cnf.num_vars(),
			4,
			"the three terms and the one total the layers still tell apart"
		);
	}
}
