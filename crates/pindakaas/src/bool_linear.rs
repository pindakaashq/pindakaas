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
//! encoder based on the [`LinVariant`] produced by [`BoolLinAggregator`].
//! [`LinearEncoder`] can be used to pipeline [`BoolLinAggregator`] and a
//! [`LinVariant`] [`Encoder`].

use std::{
	cmp::{max, min, Ordering},
	collections::VecDeque,
	fmt::{self, Display},
	iter::once,
	ops::{Add, AddAssign, Deref, DerefMut, Mul, MulAssign, Neg, Range, Sub, SubAssign},
	rc::Rc,
};

use itertools::Itertools;
use rangelist::RangeList;

use crate::{
	cardinality::Cardinality,
	cardinality_one::CardinalityOne,
	helpers::{as_binary, bit, new_named_lit},
	int_linear::{Decompose, IntLinEncoder, IntLinear, NormalizedIntLinear, Term},
	integer::{lex_leq_const, Consistency, GROUND_BINARY_AT_LB},
	propositional_logic::{Formula, TseitinEncoder},
	BoolVal, Checker, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, IntEncoding, Lit,
	Result, Unsatisfiable, Valuation,
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
pub struct BoolLinExp {
	/// All terms of the pseudo-Boolean linear expression
	pub(crate) terms: VecDeque<(Lit, Coeff)>,
	/// Number of unconstrained terms (located at the front of `terms`)
	pub(crate) num_free: usize,
	/// Constraints placed on different terms, and the number of terms involved
	/// in the constraint
	pub(crate) constraints: Vec<(Constraint, usize)>,
	/// Additive constant
	pub(crate) add: Coeff,
	/// Multiplicative contant
	pub(crate) mult: Coeff,
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
	pub(crate) exp: BoolLinExp,
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

#[allow(
	dead_code,
	reason = "used once the integer constraint encoding is reachable from the pseudo-Boolean entry point"
)]
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

#[derive(Debug, Clone)]
/// An [`BoolLinear`] expression that has been aggregated and normalized.
///
/// The constraint captured by this struct contains only positive coefficients,
/// contains at most one term with the same variable, and its comparator has
/// been limited to `≤` or `=`. Objects of this type are generally the result of
/// using the [`BoolLinAggregator`], and are generally the required input type
/// for encoders of boolean linear constraints.
pub struct NormalizedBoolLinear {
	pub(crate) terms: Vec<Part>,
	pub(crate) cmp: LimitComp,
	pub(crate) k: PosCoeff,
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

impl Part {
	/// Divide every coefficient in the part, and any domain bounds it carries,
	/// by `g`.
	///
	/// The caller is required to ensure that `g` divides each of these values
	/// exactly.
	pub(crate) fn div_assign(&mut self, g: Coeff) {
		let terms = match self {
			Part::Amo(terms) | Part::Ic(terms) => terms,
			Part::Dom(terms, lb, ub) => {
				debug_assert!(
					**lb % g == 0 && **ub % g == 0,
					"domain bounds {lb}..{ub} are not divisible by {g}"
				);
				**lb /= g;
				**ub /= g;
				terms
			}
		};
		for (_, coef) in terms {
			debug_assert!(
				**coef % g == 0,
				"coefficient {coef} is not divisible by {g}"
			);
			**coef /= g;
		}
	}

	pub(crate) fn iter(&self) -> impl Iterator<Item = &(Lit, PosCoeff)> {
		self.into_iter()
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// PosCoeff is a type for coefficients that are guaranteed by the programmer to
/// be 0 or greater.
pub(crate) struct PosCoeff(pub(crate) Coeff);

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
		_lbl: String,
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

		let carry = out.unwrap_or_else(|| BoolVal::Lit(new_named_lit!(db, _lbl)));
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
	#[allow(
		dead_code,
		reason = "consumed by the binary integer encoding, added in a later change"
	)]
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
		_lbl: String,
	) -> Result<BoolVal>
	where
		Db: ClauseDatabase + ?Sized,
	{
		let out = out.unwrap_or_else(|| BoolVal::Lit(new_named_lit!(db, _lbl)));
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

impl LinMarker for AdderEncoder {}

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

impl Decompose for BddEncoder {
	/// Follow the terms one at a time, keeping a layer of the totals still
	/// worth telling apart.
	///
	/// Totals that lead to the same outcome whatever the remaining terms do are
	/// one node, so a layer holds intervals rather than values and the diagram
	/// stays narrow. Where a layer agrees with the next one from some total
	/// upwards, its literal for that total is the next layer's, which is what
	/// keeps the layers from each paying for their own.
	fn decompose(&self, con: &NormalizedIntLinear) -> Result<Vec<IntLinear>, Unsatisfiable> {
		// The widest terms first, so that the layers narrow early and the ones
		// after them have less to tell apart.
		let terms = con
			.terms()
			.iter()
			.cloned()
			.sorted_by(|a: &Term, b: &Term| b.ub().cmp(&a.ub()))
			.collect_vec();
		let (cmp, k) = (Comparator::from(con.cmp()), con.k());

		// A variable per layer, over the totals its nodes stand for.
		let mut layers = Vec::with_capacity(terms.len() + 1);
		let mut shared = Vec::with_capacity(terms.len() + 1);
		for (i, nodes) in Self::construct_bdd(&terms, cmp, k).into_iter().enumerate() {
			let mut vals = Vec::new();
			let mut views = Vec::new();
			for (interval, node) in nodes {
				// A node stands for the largest total in its interval.
				let val = interval.end - 1;
				match node {
					BddNode::Gap => {}
					BddNode::Val => vals.push(val),
					BddNode::View(of) => {
						vals.push(val);
						views.push((val, of));
					}
				}
			}
			if vals.is_empty() {
				return Err(Unsatisfiable);
			}
			layers.push(crate::integer::var::IntVar::new(
				vals.into_iter().map(|v| v..=v).collect(),
				self.add_consistency,
				format!("y{i}"),
			));
			shared.push(views);
		}

		// Now that every layer exists, say which of their literals are shared.
		for (i, views) in shared.into_iter().enumerate() {
			for (val, of) in views {
				layers[i].set_ord_view_of(val, Rc::clone(&layers[i + 1]), of);
			}
		}

		Ok(terms
			.into_iter()
			.enumerate()
			.map(|(i, x)| {
				IntLinear::new(
					vec![
						Term::new(1, Rc::clone(&layers[i])),
						x,
						Term::new(-1, Rc::clone(&layers[i + 1])),
					],
					cmp,
					0,
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
		IntLinEncoder::default().encode_decomposed(db, con, self)
	}
}

impl LinMarker for BddEncoder {}

impl BoolLinExp {
	// TODO I'm not really happy with this interface yet...
	// Probably makes more sense to use something like int encodings
	/// Add a log encoding to the linear expression, where it is given that the
	/// log encoding is known to be within `lb..=ub`.
	///
	/// Note that `lb` and `ub` bound the integer that the terms encode, not the
	/// value the terms contribute to the expression. For terms `(x₀, c)`,
	/// `(x₁, 2c)`, `(x₂, 4c)`, a bound of `0..=3` means the contribution is at
	/// most `3c`.
	pub fn add_bounded_log_encoding(
		mut self,
		terms: &[(Lit, Coeff)],
		lb: Coeff,
		ub: Coeff,
	) -> Self {
		debug_assert!(
			lb <= ub,
			"lower bound {lb} of a log encoding exceeds its upper bound {ub}"
		);
		debug_assert!(
			terms.is_empty()
				|| (lb >= 0
					&& terms[0].1.abs().saturating_mul(ub)
						<= terms.iter().map(|(_, coef)| coef.abs()).sum::<Coeff>()),
			"bounds {lb}..={ub} lie outside the range the given terms can represent"
		);
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
				Some(Constraint::AtMostOne)
					if sum != 0 && terms.iter().filter(|&&&(l, _)| sol.value(l)).count() > 1 =>
				{
					return Err(Unsatisfiable);
				}
				Some(Constraint::ImplicationChain)
					if terms
						.iter()
						.map(|(l, _)| *l)
						.tuple_windows()
						.any(|(a, b)| !sol.value(a) & sol.value(b)) =>
				{
					return Err(Unsatisfiable);
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
				_ => {}
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
				for (k, lit) in (first..).zip(vals.iter()) {
					self.terms.push_back((*lit, k));
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
				for (k, lit) in (first..).zip(vals.iter()) {
					terms.push_back((*lit, k));
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
	Db: ClauseDatabase + ?Sized,
	Enc: Encoder<Db, NormalizedIntLinear> + LinMarker,
{
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		// A cardinality constraint is a linear one whose terms all count for
		// one, so it is read as an integer constraint the same way.
		let lin = NormalizedBoolLinear::from(con.clone());
		let con = NormalizedIntLinear::from_normalized(db, &lin)?;
		self.encode(db, &con)
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

impl NormalizedBoolLinear {
	/// The comparator of the constraint, which normalising leaves as `≤` or
	/// `=`.
	pub(crate) fn limit_comparator(&self) -> LimitComp {
		self.cmp.clone()
	}

	/// The groups of terms the constraint was found to have.
	pub(crate) fn parts(&self) -> impl Iterator<Item = &Part> + '_ {
		self.terms.iter()
	}

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

impl Decompose for SwcEncoder {
	/// Carry a running total along the terms, one at a time.
	///
	/// Each step passes on what is left of the bound after the term it sees, so
	/// the totals telescope: adding the steps together leaves the first total
	/// against the last, which is the constraint. Counting down from nothing to
	/// minus the bound keeps every total within it.
	fn decompose(&self, con: &NormalizedIntLinear) -> Result<Vec<IntLinear>, Unsatisfiable> {
		// Two terms or fewer are already as small as the chain would make them.
		if con.terms().len() <= 2 {
			return Ok(vec![con.into()]);
		}
		let (cmp, k, n) = (Comparator::from(con.cmp()), con.k(), con.terms().len());
		let totals = (0..=n)
			.map(|i| {
				// The ends are fixed, so that what the chain proves between
				// them is the constraint itself.
				let dom = match i {
					0 => 0..=0,
					_ if i == n => -k..=-k,
					_ => -k..=0,
				};
				crate::integer::var::IntVar::new(
					RangeList::from_iter([dom]),
					self.add_consistency,
					format!("y{i}"),
				)
			})
			.collect_vec();

		Ok(con
			.terms()
			.iter()
			.zip(totals.iter().tuple_windows())
			.map(|(x, (carried, left))| {
				IntLinear::new(
					vec![
						x.clone(),
						Term::new(1, Rc::clone(left)),
						Term::new(-1, Rc::clone(carried)),
					],
					cmp,
					0,
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
		IntLinEncoder::default().encode_decomposed(db, con, self)
	}
}

impl LinMarker for SwcEncoder {}

impl TotalizerEncoder {
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
	fn decompose(&self, con: &NormalizedIntLinear) -> Result<Vec<IntLinear>, Unsatisfiable> {
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
			.sorted_by_key(|t| t.ub() - t.lb())
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
						let dom: RangeList<Coeff> = if at_root {
							RangeList::from_iter([k..=k])
						} else {
							left.values()
								.into_iter()
								.cartesian_product(right.values())
								.map(|(a, b)| a + b)
								.filter(|&d| d <= k)
								.map(|d| d..=d)
								.collect()
						};
						if dom.is_empty() {
							return Err(Unsatisfiable);
						}
						let parent = crate::integer::var::IntVar::new(
							dom,
							self.add_consistency,
							format!("t{i}"),
						);
						cons.push(IntLinear::new(
							vec![
								left.clone(),
								right.clone(),
								Term::new(-1, Rc::clone(&parent)),
							],
							cmp,
							0,
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
		IntLinEncoder::default().encode_decomposed(db, con, self)
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
						tests::construct_terms, LimitComp, NormalizedBoolLinear, Part, PosCoeff,
					},
					cardinality_one::{CardinalityOne, PairwiseEncoder},
					helpers::tests::{assert_solutions, expect_file},
					int_linear::NormalizedIntLinear,
					ClauseDatabaseTools, Cnf, Encoder, Lit,
				};

				#[test]
				fn small_le_1() {
					let mut cnf = Cnf::default();
					let a = cnf.new_lit();
					let b = cnf.new_lit();
					let c = cnf.new_lit();
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 2), (b, 3), (c, 5)]),
							cmp: LimitComp::LessEq,
							k: PosCoeff::new(6),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 1), (b, 2), (c, 4)]),
							cmp: LimitComp::LessEq,
							k: PosCoeff::new(5),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 4), (b, 6), (c, 7)]),
							cmp: LimitComp::LessEq,
							k: PosCoeff::new(10),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 1), (b, 2), (c, 4)]),
							cmp: LimitComp::Equal,
							k: PosCoeff::new(5),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 1), (b, 2), (c, 3)]),
							cmp: LimitComp::Equal,
							k: PosCoeff::new(3),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 2), (b, 3), (c, 5), (d, 7)]),
							cmp: LimitComp::Equal,
							k: PosCoeff::new(10),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 2), (b, 1), (c, 2), (d, 2)]),
							cmp: LimitComp::Equal,
							k: PosCoeff::new(4),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: vec![
								Part::Amo(vec![(a, PosCoeff::new(3)), (b, PosCoeff::new(5))]),
								Part::Amo(vec![(c, PosCoeff::new(2)), (d, PosCoeff::new(4))]),
							],
							cmp: LimitComp::LessEq,
							k: PosCoeff::new(7),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: vec![
								Part::Amo(vec![(a, PosCoeff::new(3)), (b, PosCoeff::new(5))]),
								Part::Amo(vec![(c, PosCoeff::new(2)), (d, PosCoeff::new(4))]),
							],
							cmp: LimitComp::Equal,
							k: PosCoeff::new(7),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: vec![
								Part::Amo(vec![
									(a, PosCoeff::new(3)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(5)),
								]),
								Part::Amo(vec![(d, PosCoeff::new(4))]),
							],
							cmp: LimitComp::LessEq,
							k: PosCoeff::new(7),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: vec![
								Part::Amo(vec![
									(a, PosCoeff::new(3)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(5)),
								]),
								Part::Amo(vec![(d, PosCoeff::new(4))]),
							],
							cmp: LimitComp::Equal,
							k: PosCoeff::new(7),
						},
					)
					.unwrap();
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
					let con = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: vec![
								Part::Ic(vec![
									(a, PosCoeff::new(2)),
									(b, PosCoeff::new(3)),
									(c, PosCoeff::new(4)),
								]),
								Part::Amo(vec![(d, PosCoeff::new(5))]),
							],
							cmp: LimitComp::LessEq,
							k: PosCoeff::new(8),
						},
					)
					.unwrap();
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
					let res = NormalizedIntLinear::from_normalized(
						&mut cnf,
						&NormalizedBoolLinear {
							terms: construct_terms(&[(a, 3), (b, 9)]),
							cmp: LimitComp::Equal,
							k: PosCoeff::new(10),
						},
					)
					.and_then(|con| $encoder.encode(&mut cnf, &con));
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

	use std::{cmp::Ordering, num::NonZeroI32};

	use itertools::Itertools;
	use traced_test::test;

	use crate::{
		aggregator::{BoolLinAggregator, LinVariant, LinearEncoder, StaticLinEncoder},
		bool_linear::{
			AdderEncoder, BoolLinExp, BoolLinear, Comparator, LimitComp, Part, PosCoeff,
			TotalizerEncoder,
		},
		cardinality::{tests::card_test_suite, Cardinality},
		cardinality_one::{tests::card1_test_suite, CardinalityOne, PairwiseEncoder},
		helpers::tests::{
			all_bin_solutions, assert_checker, assert_encoding, assert_solutions, bin_lits,
			expect_file,
		},
		sorted::SortedEncoder,
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
		con: &BoolLinear,
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

	/// The literals and coefficients of each group, as the parts a test names
	/// them by.
	fn weights(parts: Vec<Part>) -> Vec<Vec<(Lit, Coeff)>> {
		sorted_weights(
			parts
				.iter()
				.map(|p| p.iter().map(|&(l, c)| (l, *c)).collect())
				.collect(),
		)
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
			let (x, y) = (bin_lits(&mut cnf, x_bits), bin_lits(&mut cnf, y_bits));
			let z = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, None).unwrap();

			let solutions = all_bin_solutions(&cnf, &[&x, &y, &z]);
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

		let solutions = all_bin_solutions(&cnf, &[&x, &y, &z]);
		assert_eq!(solutions.len(), 4);
		for s in &solutions {
			assert_eq!(s[2], s[0] + s[1], "{} + {} != {}", s[0], s[1], s[2]);
		}
	}

	#[test]
	fn ripple_carry_adder_constrains_a_given_sum() {
		let mut cnf = Cnf::default();
		let (x, y, z) = (
			bin_lits(&mut cnf, 2),
			bin_lits(&mut cnf, 2),
			bin_lits(&mut cnf, 2),
		);
		let _ = AdderEncoder::ripple_carry_adder(&mut cnf, &x, &y, None, Some(&z)).unwrap();

		let solutions = all_bin_solutions(&cnf, &[&x, &y, &z]);
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1], &[a, b, c]),
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
	fn aggregator_zero_coefficient() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		// A term that cannot contribute to the sum is dropped entirely, rather
		// than kept with a coefficient of zero
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[0, 2, 3, 4], &[a, b, c, d]),
					Comparator::LessEq,
					8
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(b, 2), (c, 3), (d, 4)])),
				LimitComp::LessEq,
				*PosCoeff::new(8)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[2, 4, 6], &[a, b, c]),
					Comparator::LessEq,
					7
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(a, 1), (b, 2), (c, 3)])),
				LimitComp::LessEq,
				*PosCoeff::new(3)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[2, 4], &[a, b]),
					Comparator::Equal,
					5
				)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[3, 3, 3, 7], &[a, b, c, d]),
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[3, 3, 3, 7], &[a, b, c, d]),
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[2, 3, 4], &[a, b, c]),
					Comparator::LessEq,
					7
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(a, 2), (b, 3), (c, 4)])),
				LimitComp::LessEq,
				*PosCoeff::new(7)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(1, 3), (2, 1), (3, 2)])),
				LimitComp::LessEq,
				*PosCoeff::new(3)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 1, 2], &[a, !a, b, c]),
					Comparator::LessEq,
					3
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(!a, 1), (b, 1), (c, 2)])),
				LimitComp::LessEq,
				*PosCoeff::new(2)
			))
		);

		// Aggregation of positive and negative coefficients of the same literal
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, -2, 1, 2], &[a, a, b, c]),
					Comparator::LessEq,
					2,
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(!a, 1), (b, 1), (c, 2)])),
				LimitComp::LessEq,
				*PosCoeff::new(3)
			))
		);

		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_detection() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();

		// Correctly detect at most one
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1], &[a, b, c]),
					Comparator::LessEq,
					1
				)
			),
			Ok(Aggregated::CardinalityOne(vec![a, b, c], LimitComp::LessEq))
		);
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[2, 2, 2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(Aggregated::CardinalityOne(vec![a, b, c], LimitComp::LessEq))
		);

		// Correctly detect at most k
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::LessEq,
					2
				)
			),
			Ok(Aggregated::Cardinality(
				vec![a, b, c, d],
				LimitComp::LessEq,
				*PosCoeff::new(2)
			))
		);
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[3, 3, 3, 3], &[a, b, c, d]),
					Comparator::LessEq,
					7
				)
			),
			Ok(Aggregated::Cardinality(
				vec![a, b, c, d],
				LimitComp::LessEq,
				*PosCoeff::new(2)
			))
		);

		// Correctly detect equal k
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1, 1], &[a, b, c, d]),
					Comparator::Equal,
					2
				)
			),
			Ok(Aggregated::Cardinality(
				vec![a, b, c, d],
				LimitComp::Equal,
				*PosCoeff::new(2)
			))
		);
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[3, 3, 3, 3], &[a, b, c, d]),
					Comparator::Equal,
					6
				)
			),
			Ok(Aggregated::Cardinality(
				vec![a, b, c, d],
				LimitComp::Equal,
				*PosCoeff::new(2)
			))
		);

		// Is still normal Boolean linear in-equality
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(a, 1), (b, 2), (c, 2)])),
				LimitComp::LessEq,
				*PosCoeff::new(2)
			))
		);

		// Is still normal Boolean linear equality
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &[a, b, c]),
					Comparator::Equal,
					2
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(a, 1), (b, 2), (c, 2)])),
				LimitComp::Equal,
				*PosCoeff::new(2)
			))
		);

		// Correctly identify that the AMO is limiting the LHS ub
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_terms(&[(c, -1)]).add_choice(&[(a, -1), (b, -1)]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(Aggregated::Trivial)
		);
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 1, 1], &vars),
					Comparator::Equal,
					1
				)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 1, 1, 4, 1, 1], &[a, !b, c, d, !e, f, !g]),
					Comparator::GreaterEq,
					7
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[
					(e, 4),
					(b, 2),
					(g, 1),
					(!d, 1),
					(!a, 1),
					(!f, 1),
					(!c, 1)
				])),
				LimitComp::LessEq,
				*PosCoeff::new(4)
			))
		);
		assert_eq!(cnf.num_clauses(), 0);
	}

	#[test]
	fn aggregator_neg_coeff() {
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();

		// Correctly convert a negative coefficient
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[2, 3, -2], &[a, b, c]),
					Comparator::LessEq,
					2
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(a, 2), (b, 3), (!c, 2)])),
				LimitComp::LessEq,
				*PosCoeff::new(4)
			))
		);

		// Correctly convert multiple negative coefficients
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[-1, -1, -1], &[a, b, c]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(Aggregated::CardinalityOne(
				vec![!a, !b, !c],
				LimitComp::LessEq
			))
		);
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[-1, -2, -3], &[a, b, c]),
					Comparator::LessEq,
					-2,
				)
			),
			Ok(Aggregated::Linear(
				weights(construct_terms(&[(!a, 1), (!b, 2), (!c, 3)])),
				LimitComp::LessEq,
				*PosCoeff::new(4)
			))
		);

		// Correctly convert multiple negative coefficients with AMO constraints
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::default()
						.add_choice(&[(a, -1), (b, -3), (c, -4)])
						.add_choice(&[(d, -2), (e, -3), (f, -5)]),
					Comparator::LessEq,
					-4,
				)
			),
			Ok(Aggregated::Linear(
				weights(vec![
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
				]),
				LimitComp::LessEq,
				*PosCoeff::new(5)
			))
		);

		// Correctly convert multiple negative coefficients with side constraints
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
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
			Ok(Aggregated::Linear(
				weights(vec![
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
				]),
				LimitComp::LessEq,
				*PosCoeff::new(11)
			))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::default()
						.add_choice(&[(a, 1), (b, 2), (c, 3), (d, 4)])
						.add_choice(&[(e, 1), (f, 3)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(Aggregated::Linear(
				weights(vec![
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
				]),
				LimitComp::LessEq,
				*PosCoeff::new(4)
			))
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e, f) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::default()
						.add_chain(&[(a, 1), (b, 1), (c, 1), (d, 1)])
						.add_chain(&[(e, 1), (f, 2)]),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(Aggregated::Linear(
				weights(vec![
					Part::Ic(vec![
						(!d, PosCoeff::new(1)),
						(!c, PosCoeff::new(1)),
						(!b, PosCoeff::new(1)),
						(!a, PosCoeff::new(1)),
					]),
					Part::Ic(vec![(!f, PosCoeff::new(2)), (!e, PosCoeff::new(1))]),
				]),
				LimitComp::LessEq,
				*PosCoeff::new(4)
			))
		);

		// The declared upper bound of the group, rather than the sum of its
		// coefficients, decides whether the constraint can still be violated. The
		// group is known to be at most 3, so it can never exceed 5.
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::default().add_bounded_log_encoding(&[(a, 1), (b, 2), (c, 4)], 0, 3),
					Comparator::LessEq,
					5,
				)
			),
			Ok(Aggregated::Trivial)
		);

		// Raising the bound above `k` leaves a constraint that must be encoded
		let mut cnf = Cnf::default();
		let (a, b, c) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::default().add_bounded_log_encoding(&[(a, 1), (b, 2), (c, 4)], 0, 6),
					Comparator::LessEq,
					5,
				)
			),
			Ok(Aggregated::Linear(
				weights(vec![Part::Dom(
					vec![
						(a, PosCoeff::new(1)),
						(b, PosCoeff::new(2)),
						(c, PosCoeff::new(4))
					],
					PosCoeff::new(0),
					PosCoeff::new(6)
				),]),
				LimitComp::LessEq,
				*PosCoeff::new(5)
			))
		);

		// Dropping the most significant term lowers the value the group can still
		// reach, so its upper bound is re-clamped to what is left. Here 8d cannot
		// be true, and the remaining bits cannot exceed 7 either.
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::default().add_bounded_log_encoding(
						&[(a, 1), (b, 2), (c, 4), (d, 8)],
						0,
						15
					),
					Comparator::LessEq,
					7,
				)
			),
			Ok(Aggregated::Trivial)
		);

		// Correctly convert GreaterEq into LessEq with side constrains
		let mut cnf = Cnf::default();
		let (a, b, c, d, e) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::default()
						.add_bounded_log_encoding(&[(a, 1), (b, 2), (c, 4)], 0, 5)
						.add_bounded_log_encoding(&[(d, 3), (e, 6)], 0, 2),
					Comparator::GreaterEq,
					3,
				)
			),
			Ok(Aggregated::Linear(
				weights(vec![
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
				]),
				LimitComp::LessEq,
				*PosCoeff::new(13)
			))
		);
	}

	#[test]
	fn aggregator_sort_same_coefficients() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();

		assert_eq!(
			aggregated(
				&mut cnf,
				BoolLinAggregator::default().sort_same_coefficients(SortedEncoder::default(), 2),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[3, 3, 5, 3], &[a, b, d, c]),
					Comparator::LessEq,
					10
				)
			),
			Ok(Aggregated::Linear(
				weights(vec![
					Part::Ic(vec![
						(Lit(NonZeroI32::new(5).unwrap()), PosCoeff::new(3)),
						(Lit(NonZeroI32::new(6).unwrap()), PosCoeff::new(3)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(3))
					]),
					Part::Amo(vec![(d, PosCoeff::new(5))]),
				]),
				LimitComp::LessEq,
				*PosCoeff::new(10)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[5, 5, 5, 5, 4], &vars),
					Comparator::LessEq,
					12 // only need 2 to sort
				)
			),
			Ok(Aggregated::Linear(
				weights(vec![
					Part::Amo(vec![(*vars.last().unwrap(), PosCoeff::new(4))]),
					Part::Ic(vec![
						(Lit(NonZeroI32::new(6).unwrap()), PosCoeff::new(5)),
						(Lit(NonZeroI32::new(7).unwrap()), PosCoeff::new(5))
					]),
				]),
				LimitComp::LessEq,
				*PosCoeff::new(12)
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
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &vars),
					Comparator::Equal,
					6
				)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			aggregated(
				&mut db,
				&BoolLinAggregator::default(),
				&BoolLinear::new(
					BoolLinExp::from_slices(&[1, 2, 2], &vars),
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
			aggregated(
				&mut db,
				&BoolLinAggregator::default(),
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

	linear_test_suite! {integer_encoder, crate::int_linear::IntegerEncoder::default()}

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
			.with_propagation(crate::integer::Consistency::Bounds)
	);

	linear_test_suite!(
		totalizer_encoder_prop_doms,
		crate::bool_linear::TotalizerEncoder::default()
			.with_propagation(crate::integer::Consistency::Domain)
	);
}
