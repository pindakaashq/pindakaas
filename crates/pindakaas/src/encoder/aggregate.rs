//! Reading a general Boolean linear constraint into the narrower one it is,
//! and handing that to an encoder that takes it.

use itertools::Itertools;
use rangelist::RangeList;
use rustc_hash::{FxBuildHasher, FxHashMap};

use crate::{
	constraint::{
		linear::{AdderEncoder, Comparator, LimitComp, Linear, PosCoeff},
		cardinality::Cardinality,
		cardinality_one::{BitwiseEncoder, CardinalityOne},
		int_linear::NormalizedIntLinear,
		linear::LinVariant,
		sorted::{Sorted, SortedEncoder},
	},
	decision::integer::IntVar,
	ClauseDatabase, ClauseDatabaseTools, Encoder, Lit, Result,
};

impl LinAggregator {
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
		let mut k = lin.k - lin.exp.add * lin.exp.mult;
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
				// The literal says the term is worth its coefficient and its
				// negation that the term is worth nothing, which is a direct
				// encoding of the two values already.
				let domain = RangeList::from_elements([0, *coef]);
				IntVar::from_direct_encoding(db, domain, &[!lit, lit])
					.map(|x| (PosCoeff::new(1), x.with_label(format!("x{i}"))))
			})
			.collect::<Result<Vec<_>, _>>()?;
		terms.extend(int_terms.into_iter().map(|(x, c)| (PosCoeff::new(c), x)));
		Ok(LinVariant::Linear(NormalizedIntLinear::new(terms, cmp, k)))
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
pub struct LinAggregator {
	sorted_encoder: SortedEncoder,
	sort_same_coefficients: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// An encoder for Boolean linear constraints that performs aggregation using a
/// [`LinAggregator`] and then encodes the aggregated constraints using a
/// [`Encoder`] for [`LinVariant`].
pub struct LinearEncoder<Enc = StaticLinEncoder, Agg = LinAggregator> {
	enc: Enc,
	agg: Agg,
}

impl<Enc, Agg> LinearEncoder<Enc, Agg> {
	/// Access the [`LinAggregator`] used by this encoder.
	pub fn linear_aggregator(&self) -> &Agg {
		&self.agg
	}

	/// Create a new [`LinearEncoder`] with the given [`Encoder`] for
	/// [`LinVariant`]s and [`LinAggregator`].
	pub fn new(enc: Enc, agg: Agg) -> Self {
		Self { enc, agg }
	}

	/// Access the [`Encoder`] for [`LinVariant`]s used by this encoder.
	pub fn variant_encoder(&self) -> &Enc {
		&self.enc
	}

	/// Change the [`LinAggregator`] used by this encoder.
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

#[cfg(test)]
mod tests {
	use std::num::NonZeroI32;

	use traced_test::test;

	use crate::helpers::tests::prelude::*;

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
		agg: &LinAggregator,
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
	fn aggregator_at_least_one_negated() {
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		// Correctly detect that all but one literal can be set to true
		assert_eq!(
			aggregated(
				&mut cnf,
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
		let LinVariant::Linear(con) = LinAggregator::default()
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
		let LinVariant::Linear(con) = LinAggregator::default()
			.aggregate(&mut cnf, &con)
			.unwrap()
		else {
			panic!("a literal and an integer make a linear constraint");
		};
		assert_eq!(con.terms().len(), 2, "one term of each kind");
		cnf.encode(
			&con,
			&crate::constraint::linear::BddEncoder::default(),
		)
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
				&Linear::new(
					LinExp::from_slices(&[3, 3, 3, 7], &[a, b, c, d]),
					Comparator::LessEq,
					5
				)
			),
			Ok(Aggregated::CardinalityOne(vec![a, b, c], LimitComp::LessEq))
		);

		// The same under `=`: once 7d is dropped the remaining sum can only
		// reach multiples of 3, so it can never equal 5.
		let mut cnf = Cnf::default();
		let (a, b, c, d) = cnf.new_lits();
		assert_eq!(
			aggregated(
				&mut cnf,
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				LinAggregator::default().sort_same_coefficients(SortedEncoder::default(), 2),
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
				LinAggregator::default().sort_same_coefficients(SortedEncoder::default(), 2),
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
				&LinAggregator::default(),
				&Linear::new(LinExp::from_slices(&[1, 2, 2], &vars), Comparator::Equal, 6)
			),
			Err(Unsatisfiable)
		);
		assert_eq!(
			aggregated(
				&mut db,
				&LinAggregator::default(),
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
				&LinAggregator::default(),
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
				&LinAggregator::default(),
				&Linear::new(LinExp::from_slices(&[4, 4, 4], &vars), Comparator::Equal, 6)
			),
			Err(Unsatisfiable)
		);
	}

	/// The constant of an expression is scaled by its multiplier and flips
	/// sign with the comparator, so shifting it into `k` must do both.
	#[test]
	fn constant_matches_the_equivalent_shifted_constraint() {
		use crate::decision::integer::IntVar;

		let k_of = |exp, cmp, k| {
			let mut db = Cnf::default();
			match LinAggregator::default().aggregate(&mut db, &Linear::new(exp, cmp, k)) {
				Ok(LinVariant::Linear(lin)) => Some(lin.k()),
				_ => None,
			}
		};
		let x = IntVar::new(0..=5);
		for (cmp, k) in [(Comparator::LessEq, 6), (Comparator::GreaterEq, -6)] {
			let sign = if cmp == Comparator::LessEq { 1 } else { -1 };
			let plain = k_of(x.clone() * (2 * sign), cmp, k);
			assert!(plain.is_some());
			assert_eq!(k_of(x.clone() * (2 * sign) + 7, cmp, k + 7), plain);
			assert_eq!(
				k_of((x.clone() * (2 * sign) + 7) * 3, cmp, (k + 7) * 3),
				plain
			);
		}
	}
}
