//! Turning a linear constraint into the form an encoder takes.
//!
//! A constraint as written is a sum of literals with coefficients, sometimes
//! with side constraints saying how some of them relate. Aggregation folds the
//! duplicates together, makes every coefficient positive, divides through by
//! what they have in common, and settles which terms belong with which. What
//! it is left with is either a constraint about counting, which has encoders of
//! its own, or a sum of integers — each group being an integer already,
//! encoded on the literals it was found on.

use std::{cmp::min, iter::once};

use itertools::Itertools;
use rustc_hash::{FxBuildHasher, FxHashMap};

use crate::{
	bool_linear::{
		AdderEncoder, BoolLinear, Comparator, Constraint, LimitComp, NormalizedBoolLinear, Part,
		PosCoeff,
	},
	cardinality::Cardinality,
	cardinality_one::{BitwiseEncoder, CardinalityOne},
	helpers::is_powers_of_two,
	int_linear::NormalizedIntLinear,
	integer::IntVar,
	sorted::{Sorted, SortedEncoder},
	ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Lit, Result,
};

#[derive(Debug)]
/// What a linear constraint turned out to be once aggregated.
///
/// Aggregation works out which terms belong together and what relates them,
/// and hands the general case on as a constraint over the integers those
/// groups encode. What it recognises as counting rather than weighing keeps a
/// form of its own, there being encoders that do only that.
pub enum LinVariant {
	/// Most general form: a sum of integer terms that must be
	/// (smaller-or-)equal to a constant. The groups the aggregator recognised
	/// have each become an integer, encoded on the literals they were found on.
	Linear(NormalizedIntLinear),
	/// Cardinality constraint (also known as a counting constraint): a sum of
	/// Boolean literals that must be (smaller-or-)equal to a positive constant.
	Cardinality(Cardinality),
	/// Cardinality constraint with the constant 1 (i.e. at-least or exactly 1
	/// literal must be true).
	CardinalityOne(CardinalityOne),
	/// Constraint was trivially encoded into clauses.
	Trivial,
}

impl BoolLinAggregator {
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "aggregator", skip_all, fields(constraint = lin.trace_print()))
	)]
	/// Normalise a [`BoolLinear`] constraint and work out which of the
	/// specialised forms it is, with its terms grouped by whatever relates
	/// them.
	pub fn aggregate<Db>(&self, db: &mut Db, lin: &BoolLinear) -> Result<LinVariant>
	where
		Db: ClauseDatabase + ?Sized,
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

		// Add remaining (unconstrained) terms.
		debug_assert!(agg.len() <= lin.exp.num_free);
		for (var, coef) in agg.into_iter().sorted_by_key(|&(var, _)| var) {
			partition.push((Constraint::AtMostOne, vec![(var.into(), coef)]));
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
							db.add_clause(terms.iter().map(|(lit, _)| *lit).chain(once(y)))
								.unwrap();

							// y -> ( ~x1 /\ ~x2 /\ .. ) == ~y \/ ~x1, ~y \/ ~x2, ..
							for lit in terms.iter().map(|tup| tup.0) {
								db.add_clause([!y, !lit]).unwrap();
							}

							// this term will cancel out later when we add q*min_lit to the LHS
							let _ = terms.remove(min_index);

							// since y + x1 + x2 + ... = 1 (exactly-one), we have q*y + q*x1 + q*x2
							// + ... = q after adding term 0*y, we can add q*y + q*x1 + q*x2
							// + ... on the LHS, and q on the RHS
							terms.push((y, 0)); // note: it's fine to add y into the same AMO group
							terms = terms.iter().map(|(lit, coef)| (*lit, *coef + q)).collect();
							k += q;
						}

						// all coefficients should be positive (since we subtracted the most
						// negative coefficient)
						vec![Part::Amo(
							terms
								.into_iter()
								.map(|(lit, coef)| (lit, PosCoeff::new(coef)))
								.collect(),
						)]
					}

					(Constraint::ImplicationChain, terms) => {
						// normalize by splitting up the chain into two chains by coef polarity,
						// inverting the coefs of the neg
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
					(Constraint::Domain { lb: l, ub: u }, terms) => {
						assert!(
							terms.iter().all(|(_, coef)| coef.is_positive())
								|| terms.iter().all(|(_, coef)| coef.is_negative()),
							"Normalizing mixed positive/negative coefficients not yet \
							 supported for Dom constraint on {terms:?}"
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
				let filter_zero_coefficients =
					|terms: Vec<(Lit, PosCoeff)>| -> Vec<(Lit, PosCoeff)> {
						terms.into_iter().filter(|&(_, coef)| *coef != 0).collect()
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
			db.contradiction()?;
			unreachable!();
		}
		// trivial case: no literals can be activated
		if k == 0 {
			for part in partition {
				for (lit, _) in part.iter() {
					db.add_clause([!*lit])?;
				}
			}
			return Ok(LinVariant::Trivial);
		}
		let mut k = PosCoeff::new(k);

		// Remove terms with coefs higher than k
		let mut partition = partition
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

		// Normalize the constraint by the greatest common divisor of its
		// coefficients, shrinking both the coefficients and `k` for every encoder
		// downstream.
		{
			let mut iter = partition
				.iter()
				.flat_map(|part| part.iter())
				.map(|&(_, coef)| coef.0);
			if let Some(mut divisor) = iter.next() {
				for coef in iter {
					let mut other = coef;
					while other != 0 {
						(divisor, other) = (other, divisor % other);
					}
					if divisor == 1 {
						break;
					}
				}
				if divisor > 1 {
					// The left hand side can only take on multiples of the divisor, so an
					// equality that does not sit on one of those multiples is unsatisfiable.
					if cmp == LimitComp::Equal && *k % divisor != 0 {
						db.contradiction()?;
						unreachable!();
					}
					for part in &mut partition {
						part.div_assign(divisor);
					}
					// Rounding down is sound for `≤` for the same reason.
					k = PosCoeff::new(*k / divisor);
				}
			}
		}

		// Check whether some literals can violate / satisfy the constraint
		let lhs_ub = PosCoeff::new(
			partition
				.iter()
				.map(|part| match part {
					// Only a single literal of the group can be true.
					Part::Amo(terms) => terms.iter().map(|&(_, i)| *i).max().unwrap_or(0),
					// Every literal of the chain can be true at the same time.
					Part::Ic(terms) => terms.iter().map(|&(_, coef)| *coef).sum(),
					// The group is known to stay within its declared bounds, which
					// can be tighter than the sum of its coefficients.
					Part::Dom(terms, _, u) => {
						debug_assert!(
							**u <= terms.iter().map(|&(_, coef)| *coef).sum(),
							"upper bound {u:?} of a domain group exceeds the sum of \
							 its coefficients, so it cannot be used as a bound here"
						);
						**u
					}
				})
				.sum(),
		);

		match cmp {
			LimitComp::LessEq => {
				if lhs_ub <= k {
					return Ok(LinVariant::Trivial);
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
					return Ok(LinVariant::Trivial);
				}
			}
			LimitComp::Equal => {
				if lhs_ub < k {
					db.contradiction()?;
					unreachable!();
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
					return Ok(LinVariant::Trivial);
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

		// special case: all coefficients are equal, which the normalization above
		// will have reduced to one
		if partition
			.iter()
			.flat_map(|part| part.iter())
			.all(|&(_, coef)| *coef == 1)
		{
			let partition = partition
				.iter()
				.flat_map(|part| part.iter())
				.map(|&(lit, _)| lit)
				.collect_vec();
			if *k == 1 {
				// Cardinality One constraint
				return Ok(LinVariant::CardinalityOne(CardinalityOne {
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
					return Ok(LinVariant::Trivial);
				} else {
					// we still need to constrain x1 + x2 .. >= n-1
					//   == (1 - ~x1) + (1 - ~x2) + .. >= n-1
					//   == - ~x1 - ~x2 - .. <= n-1-n ( == .. <= -1)
					//   == ~x1 + ~x2 + .. <= 1
					return Ok(LinVariant::CardinalityOne(CardinalityOne {
						lits: neg.collect_vec(),
						cmp: LimitComp::LessEq,
					}));
				}
			}

			// Encode count constraint
			return Ok(LinVariant::Cardinality(Cardinality {
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

					let y = IntVar::new(0..=c).with_label("s");
					// The sorted variable counts how many hold, so each of its
					// order literals is worth another `coef`. They are wanted
					// either way, so there is nothing to gain by waiting.
					let order = y.order_encoding(db)?;
					let terms = order.iter_lits().map(|l| (l, coef)).collect();
					self.sorted_encoder
						.encode(db, &Sorted::new(&lits, cmp.clone(), &y))
						.unwrap();
					partition.push(Part::Ic(terms));
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

		// The groups are what the constraint is made of, so hand them on as
		// the integers they encode rather than as literals with the grouping
		// noted alongside.
		Ok(LinVariant::Linear(NormalizedIntLinear::from_normalized(
			db,
			&NormalizedBoolLinear {
				terms: partition,
				cmp,
				k,
			},
		)?))
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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// A transformation of a general [`BoolLinear`] constraint into a aggregated
/// and normalized variant.
pub struct BoolLinAggregator {
	sorted_encoder: SortedEncoder,
	sort_same_coefficients: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// An encoder for Boolean linear constraints that performs aggregation using a
/// [`BoolLinAggregator`] and then encodes the aggregated constraints using a
/// [`Encoder`] for [`LinVariant`].
pub struct LinearEncoder<Enc = StaticLinEncoder, Agg = BoolLinAggregator> {
	enc: Enc,
	agg: Agg,
}

impl<Enc, Agg> LinearEncoder<Enc, Agg> {
	/// Access the [`BoolLinAggregator`] used by this encoder.
	pub fn linear_aggregator(&self) -> &Agg {
		&self.agg
	}

	/// Create a new [`LinearEncoder`] with the given [`Encoder`] for
	/// [`LinVariant`]s and [`BoolLinAggregator`].
	pub fn new(enc: Enc, agg: Agg) -> Self {
		Self { enc, agg }
	}

	/// Access the [`Encoder`] for [`LinVariant`]s used by this encoder.
	pub fn variant_encoder(&self) -> &Enc {
		&self.enc
	}

	/// Change the [`BoolLinAggregator`] used by this encoder.
	pub fn with_linear_aggregator(&mut self, agg: Agg) -> &mut Self {
		self.agg = agg;
		self
	}

	/// Change the [`Encoder`] for [`LinVariant`]s used by this encoder.
	pub fn with_variant_encoder(&mut self, enc: Enc) -> &mut Self {
		self.enc = enc;
		self
	}
}

/// An encoder for general boolean linear constraints that dispatches to a
/// different choice of sub-encoder for cardinality and cardinality-one
/// constraints.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct StaticLinEncoder<
	LinEnc = AdderEncoder,
	CardEnc = AdderEncoder, // TODO: Actual Cardinality encoding
	Card1Enc = BitwiseEncoder,
> {
	lin_enc: LinEnc,
	card_enc: CardEnc,
	amo_enc: Card1Enc,
}

impl<LinEnc, CardEnc, AmoEnc> StaticLinEncoder<LinEnc, CardEnc, AmoEnc> {
	/// Get mutable access to the encoder that is used to encode
	/// [`LinVariant::CardinalityOne`] variants.
	pub fn amo_encoder(&mut self) -> &mut AmoEnc {
		&mut self.amo_enc
	}

	/// Get mutable access to the encoder that is used to encode
	/// [`LinVariant::Cardinality`] variants.
	pub fn card_encoder(&mut self) -> &mut CardEnc {
		&mut self.card_enc
	}

	/// Get mutable access to the encoder that is used to encode
	/// [`LinVariant::Linear`] variants.
	pub fn lin_encoder(&mut self) -> &mut LinEnc {
		&mut self.lin_enc
	}

	/// Create a new [`StaticLinEncoder`] with the given encoders to encode
	/// [`LinVariant::Linear`], [`LinVariant::Cardinality`], and
	/// [`LinVariant::CardinalityOne`] variants respectively.
	pub fn new(lin_enc: LinEnc, card_enc: CardEnc, amo_enc: AmoEnc) -> Self {
		Self {
			lin_enc,
			card_enc,
			amo_enc,
		}
	}
}

impl<Db, LinEnc, CardEnc, AmoEnc> Encoder<Db, LinVariant>
	for StaticLinEncoder<LinEnc, CardEnc, AmoEnc>
where
	Db: ClauseDatabase + ?Sized,
	LinEnc: Encoder<Db, NormalizedIntLinear>,
	CardEnc: Encoder<Db, Cardinality>,
	AmoEnc: Encoder<Db, CardinalityOne>,
{
	fn encode(&self, db: &mut Db, lin: &LinVariant) -> Result {
		match &lin {
			LinVariant::Linear(lin) => self.lin_enc.encode(db, lin),
			LinVariant::Cardinality(card) => self.card_enc.encode(db, card),
			LinVariant::CardinalityOne(amo) => self.amo_enc.encode(db, amo),
			LinVariant::Trivial => Ok(()),
		}
	}
}

impl<Db, Enc> Encoder<Db, BoolLinear> for LinearEncoder<Enc>
where
	Db: ClauseDatabase + ?Sized,
	Enc: Encoder<Db, LinVariant>,
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
