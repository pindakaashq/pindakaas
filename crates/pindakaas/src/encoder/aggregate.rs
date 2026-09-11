//! Reading a general Boolean linear constraint into the narrower one it is,
//! and handing that to an encoder that takes it.

use itertools::Itertools;
use rangelist::RangeList;
use rustc_hash::{FxBuildHasher, FxHashMap};

use crate::{
	constraint::{
		bool_linear::NormalizedBoolLinear,
		linear::{AdderEncoder, Comparator, LimitComp, Linear, PosCoeff},
		cardinality::Cardinality,
		cardinality_one::{BitwiseEncoder, CardinalityOne},
		int_linear::NormalizedIntLinear,
		linear::LinVariant,
		count::{Count, SortingNetworkEncoder},
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
	///
	/// Coefficients here are post-aggregation values: repeated variables,
	/// negated literals, constants, and the expression multiplier have already
	/// been combined.
	///
	/// # Errors
	///
	/// [`crate::Unsatisfiable`] when normalisation proves the constraint
	/// inconsistent or emitting a simplifying clause fails.
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
			int_terms.push((x.clone(), c));
		}

		// Every literal stands on its own: a group of them is an integer, and
		// an integer is a term of the expression rather than an annotation on
		// its literals. Normalising therefore makes each coefficient
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

		// Counting literals into an integer, which a sorting network states
		// outright where the general case would count into intermediates
		// first. Read before the mirror below, which would hide the variable.
		if let [(y, -1)] = &int_terms[..] {
			if k == 0 && partition.iter().all(|&(_, coef)| *coef == 1) {
				let lits = partition.iter().map(|&(lit, _)| lit).collect();
				return Ok(LinVariant::Count(Count::new(lits, cmp, y.clone())));
			}
		}

		// A coefficient is made positive by counting the variable from the far
		// end, which is a view on it rather than a variable of its own.
		for (x, c) in &mut int_terms {
			if *c < 0 {
				k -= *c * (x.min() + x.max());
				*c = -*c;
				*x = IntVar::mirrored(db, x)?;
			}
		}

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
						.encode(db, &Count::new(lits.clone(), cmp.clone(), y.clone()))
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
		// Weighted, but over literals alone, so it stays in them rather than
		// becoming an integer per literal for an encoder to take apart again.
		if int_terms.is_empty() {
			return Ok(LinVariant::BoolLinear(NormalizedBoolLinear::new(
				partition, cmp, k,
			)));
		}

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
	/// Pre-aggregation of at least `n` equal-coefficient literals by `sorted_encoder`.
	///
	/// Zero disables the transformation, as in the default configuration.
	pub fn sort_same_coefficients(&mut self, sorted_encoder: SortingNetworkEncoder, n: usize) -> &mut Self {
		self.sorted_encoder = sorted_encoder;
		self.sort_same_coefficients = n;
		self
	}
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
/// Normalisation and specialisation of a general [`Linear`] constraint.
pub struct LinAggregator {
	sorted_encoder: SortingNetworkEncoder,
	sort_same_coefficients: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
/// Aggregation followed by encoding of the resulting [`LinVariant`].
pub struct LinearEncoder<Enc = StaticLinEncoder, Agg = LinAggregator> {
	enc: Enc,
	agg: Agg,
}

impl<Enc, Agg> LinearEncoder<Enc, Agg> {
	/// Returns the aggregation stage used by this encoder.
	pub fn linear_aggregator(&self) -> &Agg {
		&self.agg
	}

	/// Creates an encoder with independently selected aggregation and dispatch stages.
	pub fn new(enc: Enc, agg: Agg) -> Self {
		Self { enc, agg }
	}

	/// Returns the post-aggregation encoder.
	pub fn variant_encoder(&self) -> &Enc {
		&self.enc
	}

	/// Replaces the [`LinAggregator`] used by this encoder.
	pub fn with_linear_aggregator(&mut self, agg: Agg) -> &mut Self {
		self.agg = agg;
		self
	}

	/// Replaces the [`Encoder`] for [`LinVariant`]s used by this encoder.
	pub fn with_variant_encoder(&mut self, enc: Enc) -> &mut Self {
		self.enc = enc;
		self
	}
}

/// Static dispatch from each aggregated constraint shape to its encoder.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct StaticLinEncoder<
	LinEnc = AdderEncoder,
	BoolLinEnc = AdderEncoder,
	CardEnc = AdderEncoder, // TODO: Actual Cardinality encoding
	Card1Enc = BitwiseEncoder,
	CountEnc = SortingNetworkEncoder,
> {
	lin_enc: LinEnc,
	bool_lin_enc: BoolLinEnc,
	card_enc: CardEnc,
	amo_enc: Card1Enc,
	count_enc: CountEnc,
}

impl<LinEnc, BoolLinEnc, CardEnc, AmoEnc, CountEnc>
	StaticLinEncoder<LinEnc, BoolLinEnc, CardEnc, AmoEnc, CountEnc>
{
	/// Returns mutable access to the cardinality-one encoder.
	pub fn amo_encoder(&mut self) -> &mut AmoEnc {
		&mut self.amo_enc
	}

	/// Returns mutable access to the cardinality encoder.
	pub fn card_encoder(&mut self) -> &mut CardEnc {
		&mut self.card_enc
	}

	/// Returns mutable access to the integer-linear encoder.
	pub fn lin_encoder(&mut self) -> &mut LinEnc {
		&mut self.lin_enc
	}

	/// Creates a dispatcher with one encoder for every [`LinVariant`] carrying data.
	pub fn new(
		lin_enc: LinEnc,
		bool_lin_enc: BoolLinEnc,
		card_enc: CardEnc,
		amo_enc: AmoEnc,
		count_enc: CountEnc,
	) -> Self {
		Self {
			lin_enc,
			bool_lin_enc,
			card_enc,
			amo_enc,
			count_enc,
		}
	}

	/// Returns mutable access to the Boolean-linear encoder.
	pub fn bool_lin_encoder(&mut self) -> &mut BoolLinEnc {
		&mut self.bool_lin_enc
	}

	/// Returns mutable access to the variable-bound count encoder.
	pub fn count_encoder(&mut self) -> &mut CountEnc {
		&mut self.count_enc
	}
}

impl<Db, LinEnc, BoolLinEnc, CardEnc, AmoEnc, CountEnc> Encoder<Db, LinVariant>
	for StaticLinEncoder<LinEnc, BoolLinEnc, CardEnc, AmoEnc, CountEnc>
where
	Db: ClauseDatabase + ?Sized,
	LinEnc: Encoder<Db, NormalizedIntLinear>,
	BoolLinEnc: Encoder<Db, NormalizedBoolLinear>,
	CardEnc: Encoder<Db, Cardinality>,
	AmoEnc: Encoder<Db, CardinalityOne>,
	CountEnc: Encoder<Db, Count>,
{
	fn encode(&self, db: &mut Db, lin: &LinVariant) -> Result {
		match &lin {
			LinVariant::BoolLinear(lin) => self.bool_lin_enc.encode(db, lin),
			LinVariant::Linear(lin) => self.lin_enc.encode(db, lin),
			LinVariant::Cardinality(card) => self.card_enc.encode(db, card),
			LinVariant::CardinalityOne(amo) => self.amo_enc.encode(db, amo),
			LinVariant::Count(count) => self.count_enc.encode(db, count),
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
		Count(Vec<Lit>, LimitComp, Vec<Coeff>),
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
			// A literal is a group of its own, which is what it would have
			// become had it been read as an integer.
			LinVariant::BoolLinear(lin) => {
				let groups = lin.terms().iter().map(|&(l, c)| vec![(l, *c)]).collect();
				Aggregated::Linear(sorted_weights(groups), lin.cmp(), lin.k())
			}
			LinVariant::Cardinality(card) => Aggregated::Cardinality(
				card.iter_lits().collect(),
				into_limit(card.comparator()),
				card.rhs(),
			),
			LinVariant::CardinalityOne(amo) => {
				Aggregated::CardinalityOne(amo.iter_lits().collect(), into_limit(amo.comparator()))
			}
			LinVariant::Count(count) => Aggregated::Count(
				count.lits.clone(),
				count.cmp.clone(),
				count.y.domain().iter().flatten().collect(),
			),
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
			&crate::constraint::linear::DecisionDiagramEncoder::default(),
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
				LinAggregator::default().sort_same_coefficients(SortingNetworkEncoder::default(), 2),
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
				LinAggregator::default().sort_same_coefficients(SortingNetworkEncoder::default(), 2),
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

	#[test]
	fn literals_against_an_integer_are_a_count() {
		use crate::decision::integer::IntVar;

		let mut cnf = Cnf::default();
		let (a, b, c) = (cnf.new_lit(), cnf.new_lit(), cnf.new_lit());
		let y = IntVar::new(0..=3).with_label("y");

		// Both spellings of `a + b + c ≤ y` reach the same constraint.
		for con in [
			Linear::new(
				LinExp::from_slices(&[1, 1, 1], &[a, b, c]) - LinExp::from(y.clone()),
				Comparator::LessEq,
				0,
			),
			Linear::new(
				LinExp::from(y.clone()) - LinExp::from_slices(&[1, 1, 1], &[a, b, c]),
				Comparator::GreaterEq,
				0,
			),
		] {
			let LinVariant::Count(count) =
				LinAggregator::default().aggregate(&mut cnf, &con).unwrap()
			else {
				panic!("literals against an integer are a count");
			};
			assert_eq!(count.lits, vec![a, b, c]);
			assert_eq!(count.cmp, LimitComp::LessEq);
			assert_eq!(count.y.min(), 0);
			assert_eq!(count.y.max(), 3);
		}
	}

	#[test]
	fn a_count_admits_exactly_the_assignments_it_should() {
		use crate::{
			constraint::count::SortingNetworkEncoder,
			decision::integer::IntVar,
			solver::{cadical::Cadical, SolveResult, Solver},
			Valuation,
		};

		for cmp in [Comparator::LessEq, Comparator::Equal] {
			let mut cnf = Cnf::default();
			let lits = (0..3).map(|_| cnf.new_lit()).collect_vec();
			let y = IntVar::new(0..=2).with_label("y");
			let exp = LinExp::from_slices(&[1; 3], &lits) - LinExp::from(y.clone());
			let con = Linear::new(exp, cmp, 0);
			let LinVariant::Count(count) =
				LinAggregator::default().aggregate(&mut cnf, &con).unwrap()
			else {
				panic!("literals against an integer are a count");
			};
			SortingNetworkEncoder::default().encode(&mut cnf, &count).unwrap();

			let mut seen = Vec::new();
			let mut slv = Cadical::from(&cnf);
			while let SolveResult::Satisfied(sol) = slv.solve() {
				let count: Coeff = lits.iter().filter(|&&l| sol.value(l)).count() as Coeff;
				seen.push((count, y.value(&sol)));
				let no_good = lits.iter().map(|&l| if sol.value(l) { !l } else { l });
				if slv.add_clause(no_good).is_err() {
					break;
				}
			}
			assert!(!seen.is_empty(), "{cmp:?} has solutions");
			for &(n, v) in &seen {
				match cmp {
					Comparator::Equal => assert_eq!(n, v, "{cmp:?}: {n} counted, y = {v}"),
					_ => assert!(n <= v, "{cmp:?}: {n} counted, y = {v}"),
				}
			}
		}
	}
}
