//! Turning a linear constraint into the form an encoder takes.
//!
//! A constraint as written is a sum of literals with coefficients, sometimes
//! with side constraints saying how some of them relate. Aggregation folds the
//! duplicates together, makes every coefficient positive, divides through by
//! what they have in common, and settles which terms belong with which. What
//! it is left with is either a constraint about counting, which has encoders of
//! its own, or a sum of integers — each group being an integer already,
//! encoded on the literals it was found on.

use itertools::Itertools;
use rustc_hash::{FxBuildHasher, FxHashMap};

use crate::{
	bool_linear::{AdderEncoder, Comparator, LimitComp, Linear, PosCoeff},
	cardinality::Cardinality,
	cardinality_one::{BitwiseEncoder, CardinalityOne},
	constraint::sorted::{Sorted, SortedEncoder},
	decision::integer::IntVar,
	int_linear::{NormalizedIntLinear, Term},
	ClauseDatabase, ClauseDatabaseTools, Encoder, Lit, Result,
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
	/// Normalise a [`Linear`] constraint and work out which of the
	/// specialised forms it is, with its terms grouped by whatever relates
	/// them.
	pub fn aggregate<Db>(&self, db: &mut Db, lin: &Linear) -> Result<LinVariant>
	where
		Db: ClauseDatabase + ?Sized,
	{
		let mut k = lin.k;
		// Aggregate multiple occurrences of the same
		// variable.
		let mut agg = FxHashMap::with_capacity_and_hasher(lin.exp.terms.len(), FxBuildHasher);
		for (lit, coef) in lin.exp.terms() {
			let entry = agg.entry(lit.var()).or_insert(0);
			let mut coef = coef * lin.exp.mult;
			if lit.is_negated() {
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

		// A term that arrived as an integer is already what the grouping below
		// is trying to recover from literals, so it only needs the same
		// normalising: the pending multiplier, the turn from `≥`, and a
		// coefficient made positive by counting the variable from the far end.
		let mut int_terms = Vec::new();
		for (x, c) in lin.exp.int_terms() {
			let mut c = c * lin.exp.mult;
			if lin.cmp == Comparator::GreaterEq {
				c = -c;
			}
			let x = if c < 0 {
				k -= c * (x.min() + x.max());
				c = -c;
				IntVar::mirrored(db, x)?
			} else {
				x.clone()
			};
			int_terms.push((x, c));
		}

		// Every literal stands on its own: a group of them is an integer, and
		// an integer is a term of the expression rather than an annotation on
		// its literals. So normalising is just making each coefficient
		// positive, by taking the literal the other way round.
		let mut k = k - lin.exp.add;
		let cmp = match lin.cmp {
			Comparator::LessEq | Comparator::GreaterEq => LimitComp::LessEq,
			Comparator::Equal => LimitComp::Equal,
		};
		let mut partition: Vec<(Lit, PosCoeff)> = agg
			.into_iter()
			.sorted_by_key(|&(var, _)| var)
			.map(|(var, coef)| {
				let (lit, coef) = (Lit::from(var), coef);
				if coef.is_negative() {
					k += -coef;
					(!lit, PosCoeff::new(-coef))
				} else {
					(lit, PosCoeff::new(coef))
				}
			})
			.filter(|&(_, coef)| *coef != 0)
			.collect();

		// trivial case: constraint is unsatisfiable
		if k < 0 {
			db.contradiction()?;
			unreachable!();
		}
		// trivial case: no literals can be activated
		if k == 0 && int_terms.is_empty() {
			for (lit, _) in &partition {
				db.add_clause([!*lit])?;
			}
			return Ok(LinVariant::Trivial);
		}
		let mut k = PosCoeff::new(k);

		// A literal worth more than the bound can never hold.
		if int_terms.is_empty() {
			partition.retain(|&(lit, coef)| {
				if coef > k {
					db.add_clause([!lit]).unwrap();
					false
				} else {
					true
				}
			});
		}

		// The sum only lands on multiples of what divides every coefficient.
		{
			let mut iter = partition
				.iter()
				.map(|&(_, coef)| *coef)
				.chain(int_terms.iter().map(|&(_, c)| c));
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
					// An equality that does not sit on one of those multiples
					// is unsatisfiable.
					if cmp == LimitComp::Equal && *k % divisor != 0 {
						db.contradiction()?;
						unreachable!();
					}
					for (_, coef) in &mut partition {
						*coef = PosCoeff::new(**coef / divisor);
					}
					for (_, c) in &mut int_terms {
						*c /= divisor;
					}
					// Rounding down is sound for `≤` for the same reason.
					k = PosCoeff::new(*k / divisor);
				}
			}
		}

		// What follows reasons about a sum that runs from nothing up to its
		// bound, which holds of literals but not of a variable whose least
		// value is not zero, so a constraint with integer terms is left alone.
		if int_terms.is_empty() {
			let lhs_ub = PosCoeff::new(partition.iter().map(|&(_, coef)| *coef).sum());
			match cmp {
				LimitComp::LessEq => {
					if lhs_ub <= k {
						return Ok(LinVariant::Trivial);
					}
				}
				LimitComp::Equal => {
					if lhs_ub < k {
						db.contradiction()?;
						unreachable!();
					}
					if lhs_ub == k {
						for (lit, _) in &partition {
							db.add_clause([*lit])?;
						}
						return Ok(LinVariant::Trivial);
					}
				}
			}

			// Every literal counts for the same, so this is a counting
			// constraint rather than a weighted one.
			if partition.iter().all(|&(_, coef)| *coef == 1) {
				let lits = partition.iter().map(|&(lit, _)| lit).collect_vec();
				if *k == 1 {
					return Ok(LinVariant::CardinalityOne(CardinalityOne { lits, cmp }));
				}
				// At most n-1 out of n is at least one of them being false.
				if lits.len() == (*k + 1) as usize {
					let neg = lits.iter().map(|&l| !l);
					db.add_clause(neg.clone())?;
					return Ok(if cmp == LimitComp::LessEq {
						LinVariant::Trivial
					} else {
						LinVariant::CardinalityOne(CardinalityOne {
							lits: neg.collect_vec(),
							cmp: LimitComp::LessEq,
						})
					});
				}
				return Ok(LinVariant::Cardinality(Cardinality { lits, cmp, k }));
			}
		}

		// Literals that count for the same are worth sorting first, so that
		// what they come to together is one integer rather than one each.
		if self.sort_same_coefficients >= 2 {
			let mut kept = Vec::new();
			// Sorted, since a hash map hands its keys back in whatever order
			// it likes and the encoding has to be the same every run.
			for (coef, lits) in partition
				.into_iter()
				.map(|(lit, coef)| (coef, lit))
				.into_group_map()
				.into_iter()
				.sorted_by_key(|&(coef, _)| coef)
			{
				if lits.len() >= self.sort_same_coefficients {
					let y = IntVar::new(0..=(*k / *coef)).with_label("s");
					// Its literals are wanted either way, so there is nothing
					// to gain by leaving them to the network below.
					let _ = y.order_encoding(db)?;
					self.sorted_encoder
						.encode(db, &Sorted::new(&lits, cmp.clone(), &y))
						.unwrap();
					int_terms.push((y, *coef));
				} else {
					kept.extend(lits.into_iter().map(|lit| (lit, coef)));
				}
			}
			kept.sort_by_key(|&(lit, _)| lit);
			partition = kept;
		}

		// A term is the integer it stands for: a literal is one worth its
		// coefficient when it holds, and a variable is one already.
		let mut terms = partition
			.iter()
			.enumerate()
			.map(|(i, &(lit, coef))| {
				Term::from_at_most_one(db, &[(lit, coef)], &format!("x{i}"), false)
			})
			.collect::<Result<Vec<_>, _>>()?;
		terms.extend(int_terms.into_iter().map(|(x, c)| Term::new(c, x)));
		Ok(LinVariant::Linear(NormalizedIntLinear::from_terms(
			terms, cmp, k,
		)))
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
/// A transformation of a general [`Linear`] constraint into a aggregated
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

impl<Db, Enc> Encoder<Db, Linear> for LinearEncoder<Enc>
where
	Db: ClauseDatabase + ?Sized,
	Enc: Encoder<Db, LinVariant>,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "linear_encoder", skip_all, fields(constraint = lin.trace_print()))
	)]
	fn encode(&self, db: &mut Db, lin: &Linear) -> Result {
		let variant = self.agg.aggregate(db, lin)?;
		self.enc.encode(db, &variant)
	}
}
