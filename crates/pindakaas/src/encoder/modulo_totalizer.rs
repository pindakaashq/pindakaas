//! Encoding a linear constraint as a tree of partial sums held in a mixed
//! radix base.
//!
//! The totalizer holds each node as one order-encoded integer, which costs
//! `O(d)` literals and `O(d²)` clauses for a node over `d` values. Holding it
//! as a sequence of order-encoded digits instead costs `O(β·log d)` literals
//! and `O(β²·log d)` clauses, at the price of a ripple-carry addition between
//! nodes rather than a single one.

use std::cmp::min;

use itertools::Itertools;
use rangelist::RangeList;

use crate::{
	constraint::{
		bool_linear::NormalizedBoolLinear,
		cardinality::Cardinality,
		count::Count,
		cardinality_one::CardinalityOne,
		int_linear::{term_max, term_values, NormalizedIntLinear},
		int_ternary::{IntTernary, IntTernaryConfig, IntTernaryEncoder},
		linear::{Comparator, LimitComp},
	},
	decision::integer::{lex_leq, Consistency, IntVar},
	BoolVal, ClauseDatabase, ClauseDatabaseTools, Coeff, Encoder, Result, Unsatisfiable,
};

/// Encoder for a linear constraint, as a generalized n-level modulo totalizer
/// (GMTO).
///
/// Like the [`TotalizerEncoder`](super::totalizer::TotalizerEncoder) the
/// constraint becomes a binary tree of additions, but the value of a node is
/// not one order-encoded integer: it is a sequence of order-encoded digits in a
/// mixed radix base β, so the node stands for `∑ⱼ digitⱼ·(β₀·…·βⱼ₋₁)`. Adding
/// two nodes is then a ripple-carry addition over their digits. A node over `d`
/// values costs `O(β·log d)` literals and `O(β²·log d)` clauses where the
/// totalizer costs `O(d)` and `O(d²)`.
///
/// The base suits the coefficients of the constraint; see
/// [`ModuloTotalizerEncoder::with_base`].
///
/// # Examples
///
/// ```rust
/// # use pindakaas::{
/// #     constraint::{linear::{Comparator, Linear}, int_linear::ModuloTotalizerEncoder,
/// #                  linear::{LinAggregator, LinVariant}},
/// #     decision::integer::IntVar, Cnf, Encoder,
/// # };
/// # let mut f = Cnf::default();
/// # let (x, y) = (IntVar::new(0..=5), IntVar::new(0..=5));
/// let con = Linear::new(x * 2 + y * 3, Comparator::LessEq, 10);
/// let LinVariant::Linear(con) = LinAggregator::default().aggregate(&mut f, &con)? else {
///     panic!("a sum of integer terms is a linear constraint");
/// };
/// ModuloTotalizerEncoder::default().encode(&mut f, &con)?;
/// # Ok::<(), pindakaas::Unsatisfiable>(())
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModuloTotalizerEncoder {
	add_consistency: bool,
	add_propagation: Consistency,
	base: Option<Vec<Coeff>>,
	cutoff: Option<Coeff>,
}

impl Default for ModuloTotalizerEncoder {
	fn default() -> Self {
		Self {
			add_consistency: false,
			add_propagation: Consistency::Bounds,
			base: None,
			cutoff: None,
		}
	}
}

impl ModuloTotalizerEncoder {
	/// Encode `x + y = z`, giving back `z` over the values it can still take
	/// without passing `ub`.
	fn add_eq<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		x: &IntVar,
		y: &IntVar,
		ub: Coeff,
	) -> Result<IntVar, Unsatisfiable> {
		// Adding zero asks for no clauses, as long as it cannot pass `ub`.
		if Self::is_zero(x) && y.max() <= ub {
			return Ok(y.clone());
		} else if Self::is_zero(y) && x.max() <= ub {
			return Ok(x.clone());
		}
		let domain = x
			.domain()
			.iter()
			.flatten()
			.cartesian_product(y.domain().iter().flatten().collect_vec())
			.map(|(a, b)| a + b)
			.filter(|&v| v <= ub)
			.map(|v| v..=v)
			.collect();
		let z = self.new_int_var(db, domain, "s")?;
		self.encoder().encode(
			db,
			&IntTernary::new(
				(1, x.clone()),
				(1, y.clone()),
				Comparator::Equal,
				(1, z.clone()),
			),
		)?;
		Ok(z)
	}

	/// Ripple-carry the digits of two nodes, giving back the digits of their
	/// sum over the values it can still take without passing `ub`.
	fn add_nodes<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		x: &[IntVar],
		y: &[IntVar],
		base: &[Coeff],
		ub: Coeff,
	) -> Result<Vec<IntVar>, Unsatisfiable> {
		let zero = IntVar::new(0..=0);
		let len = x.len().max(y.len());
		let mut digits = Vec::with_capacity(len + 1);
		let mut carry = zero.clone();
		// What the digits from here up may come to. Anything larger would put
		// the value of the node past `ub`.
		let mut pos_ub = ub;
		for j in 0..len {
			let b = Self::base_at(base, j);
			let x_j = x.get(j).unwrap_or(&zero);
			let y_j = y.get(j).unwrap_or(&zero);
			let w = self.add_eq(db, x_j, &carry, min(b, pos_ub))?;
			let s = self.add_eq(
				db,
				&w,
				y_j,
				min(b.saturating_mul(2).saturating_sub(1), pos_ub),
			)?;
			let (digit, next) = self.split(db, &s, b)?;
			digits.push(digit);
			carry = next;
			pos_ub /= b;
		}
		// The carry out of the top is zero unless the sum wants another digit.
		if !Self::is_zero(&carry) {
			digits.push(carry);
		}
		Ok(digits)
	}

	/// The radix of the digit at `j`, the last of the base standing for every
	/// position past it.
	fn base_at(base: &[Coeff], j: usize) -> Coeff {
		base[min(j, base.len() - 1)]
	}

	/// The `len` least significant digits of `k` in `base`, least significant
	/// first, or `None` where `k` does not fit in `len` of them.
	fn const_digits(base: &[Coeff], len: usize, k: Coeff) -> Option<Vec<Coeff>> {
		let mut rem = k;
		let ks: Vec<Coeff> = (0..len)
			.map(|j| {
				let b = Self::base_at(base, j);
				let digit = rem % b;
				rem /= b;
				digit
			})
			.collect();
		(rem == 0).then_some(ks)
	}

	/// The value of `x` as order-encoded digits in `base`, least significant
	/// first.
	fn digits<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		x: &IntVar,
		base: &[Coeff],
	) -> Result<Vec<IntVar>, Unsatisfiable> {
		let mut digits = Vec::new();
		let mut rem = x.clone();
		while rem.max() >= Self::base_at(base, digits.len()) {
			let (digit, carry) = self.split(db, &rem, Self::base_at(base, digits.len()))?;
			digits.push(digit);
			rem = carry;
		}
		digits.push(rem);
		Ok(digits)
	}

	/// The encoder of the additions this one breaks a constraint into.
	fn encoder(&self) -> IntTernaryEncoder {
		IntTernaryEncoder::with_config(IntTernaryConfig {
			propagate: self.add_propagation != Consistency::None,
			cutoff: self.cutoff,
		})
	}

	/// Build a mixed radix base from the coefficients of the constraint,
	/// given how many terms it has.
	///
	/// Starts from the heuristic of Zha et al. [^1] as the generalized
	/// n-level modulo totalizer of Bofill et al. [^2] uses it: values are
	/// added to the base until it spans every value up to `k`, each the one
	/// dividing the most coefficients, and the coefficients are divided by it
	/// afterwards so the next value suits the next digit.
	///
	/// Measured against CaDiCaL conflicts and wall time rather than clause
	/// counts alone, that rule loses to plain `⌊√n⌋` on constraints whose
	/// coefficients share no real structure — a shared divisor there is
	/// coincidence, not structure, and trusting it costs more digits than it
	/// saves. So a divisor is only trusted where it covers at least half the
	/// (remaining) coefficients; short of that every further digit falls back
	/// to `⌊√n⌋` straight away. A tie takes the smallest divisor rather than
	/// the largest, for the same reason: a digit costs `O(β²)` clauses here,
	/// so a larger radix only pays where it divides strictly more.
	///
	/// [^1]: A. Zha, M. Koshimura, H. Fujita, "N-level modulo-based CNF
	/// encodings of pseudo-Boolean constraints for MaxSAT", Constraints 24(2)
	/// (2019) 133–161.
	///
	/// [^2]: M. Bofill, J. Coll, P. Nightingale, J. Suy, F. Ulrich-Oltean, M.
	/// Villaret, "SAT encodings for pseudo-Boolean constraints together with
	/// at-most-one constraints", Artificial Intelligence 302 (2022) 103604.
	fn greedy_base(coefs: impl IntoIterator<Item = Coeff>, n: usize, k: Coeff) -> Vec<Coeff> {
		// Heuristic: divisors are tried up to a bound rather than the
		// coefficients being factorised, which no constraint seen so far pays
		// for.
		const MAX_DIVISOR: Coeff = 1 << 10;
		// Heuristic: a divisor below this share of the coefficients is
		// coincidence rather than structure; fall back instead of trusting
		// it. Best on every case measured, close behind at every other.
		const DIVISOR_SHARE_PCT: usize = 50;

		let fallback = ((n as f64).sqrt() as Coeff).max(2);
		let mut coefs = coefs.into_iter().collect_vec();
		let mut base = Vec::new();
		let mut product: Coeff = 1;
		while product <= k {
			let min_share = coefs.len() * DIVISOR_SHARE_PCT / 100;
			let b = (2..=min(MAX_DIVISOR, coefs.iter().copied().max().unwrap_or_default()))
				.map(|d| (coefs.iter().filter(|&&q| q > 0 && q % d == 0).count(), -d))
				.max()
				.filter(|&(count, _)| count >= min_share.max(1))
				.map_or(fallback, |(_, d)| -d);
			base.push(b);
			product = product.saturating_mul(b);
			for q in &mut coefs {
				*q /= b;
			}
		}
		if base.is_empty() {
			base.push(fallback);
		}
		base
	}

	/// Whether the variable can only be zero, which is what an absent digit and
	/// a carry that never happens both come to.
	fn is_zero(x: &IntVar) -> bool {
		x.card() == 1 && x.min() == 0
	}

	/// Constrain the value `digits` stands for to be at most `k`.
	fn lex_leq<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		digits: &[IntVar],
		base: &[Coeff],
		k: Coeff,
	) -> Result {
		let Some(ks) = Self::const_digits(base, digits.len(), k) else {
			// `k` is past anything the digits can stand for.
			return Ok(());
		};
		let pairs = digits
			.iter()
			.zip_eq(ks)
			.map(|(digit, k_j)| {
				Ok((
					digit.lit_at_least(db, k_j)?,
					digit.lit_at_least(db, k_j + 1)?,
				))
			})
			.collect::<Result<Vec<(BoolVal, BoolVal)>, Unsatisfiable>>()?;
		lex_leq(db, &pairs)
	}

	/// A variable over `domain`, or a constant where that leaves one value.
	fn new_int_var<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		domain: RangeList<Coeff>,
		label: &str,
	) -> Result<IntVar, Unsatisfiable> {
		if domain.is_empty() {
			db.contradiction()?;
			unreachable!()
		}
		Ok(IntVar::new(domain)
			.enforce_consistency(self.add_consistency)
			.with_label(label))
	}

	/// Constrain the value `digits` stands for to be exactly `k`.
	fn pin<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		digits: &[IntVar],
		base: &[Coeff],
		k: Coeff,
	) -> Result {
		let Some(ks) = Self::const_digits(base, digits.len(), k) else {
			// `k` is past anything the digits can stand for.
			return db.contradiction();
		};
		for (digit, k_j) in digits.iter().zip_eq(ks) {
			let at_least = digit.lit_at_least(db, k_j)?;
			db.add_clause([at_least])?;
			let greater = digit.lit_at_least(db, k_j + 1)?;
			db.add_clause([!greater])?;
		}
		Ok(())
	}

	/// Split `x` into `(x mod base, x div base)`.
	fn split<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		x: &IntVar,
		base: Coeff,
	) -> Result<(IntVar, IntVar), Unsatisfiable> {
		if x.max() < base {
			return Ok((x.clone(), IntVar::new(0..=0)));
		}
		let domain = x.domain();
		let digit = self.new_int_var(
			db,
			domain.iter().flatten().map(|v| v % base..=v % base).collect(),
			"r",
		)?;
		let carry = self.new_int_var(
			db,
			domain.iter().flatten().map(|v| v / base..=v / base).collect(),
			"q",
		)?;
		// The radix is the carry's coefficient, so nothing has to be scaled.
		self.encoder().encode(
			db,
			&IntTernary::new(
				(1, digit.clone()),
				(base, carry.clone()),
				Comparator::Equal,
				(1, x.clone()),
			),
		)?;
		Ok((digit, carry))
	}

	/// Set the mixed radix base the value of a node is held in.
	///
	/// A node stands for `∑ⱼ digitⱼ·(β₀·…·βⱼ₋₁)`, where `digitⱼ < βⱼ`. The last
	/// value given stands for every further digit, so `vec![2]` holds the nodes
	/// in binary and any base past `k` gives each of them a single digit, as
	/// the [`TotalizerEncoder`](super::totalizer::TotalizerEncoder) does.
	/// Neither extreme reproduces that encoder or the
	/// [`AdderEncoder`](super::adder::AdderEncoder): only the way a node is
	/// held coincides, not the way two of them are added.
	///
	/// `None`, the default, chooses the base from the coefficients of the
	/// constraint.
	pub fn with_base(&mut self, base: Option<Vec<Coeff>>) -> &mut Self {
		self.base = base;
		self
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

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Cardinality> for ModuloTotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &Cardinality) -> Result {
		let con = con.as_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, Count> for ModuloTotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &Count) -> Result {
		// Counting into a variable is a linear constraint whose bound is not a
		// constant, which this encoder takes once the bound is a term.
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db: ClauseDatabase + ?Sized> Encoder<Db, CardinalityOne> for ModuloTotalizerEncoder {
	fn encode(&self, db: &mut Db, con: &CardinalityOne) -> Result {
		self.encode(db, &Cardinality::from(con.clone()))
	}
}

impl<Db> Encoder<Db, NormalizedBoolLinear> for ModuloTotalizerEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	fn encode(&self, db: &mut Db, con: &NormalizedBoolLinear) -> Result {
		// The tree is built over integers, so the literals become them first.
		let con = con.as_int_linear(db)?;
		self.encode(db, &con)
	}
}

impl<Db> Encoder<Db, NormalizedIntLinear> for ModuloTotalizerEncoder
where
	Db: ClauseDatabase + ?Sized,
{
	#[cfg_attr(
		any(feature = "tracing", test),
		tracing::instrument(name = "modulo_totalizer_encoder", skip_all, fields(constraint = format!("{con:?}")))
	)]
	fn encode(&self, db: &mut Db, con: &NormalizedIntLinear) -> Result {
		let k = con.k();
		let base = match &self.base {
			Some(base) => base.clone(),
			// What a term is worth is the values it can take, not the
			// coefficient in front of it: aggregation leaves that at one and
			// puts the weight in the variable's domain.
			None => Self::greedy_base(
				con.terms()
					.iter()
					.flat_map(|(c, x)| term_values(&(**c, x.clone())))
					.filter(|&v| v > 0),
				con.terms().len(),
				k,
			),
		};
		debug_assert!(base.iter().all(|&b| b > 1));

		// A term is already the one leaf its group comes to, so the widest are
		// left to meet late.
		let xs = con
			.terms()
			.iter()
			.map(|(c, x)| (**c, x.clone()))
			.sorted_by_key(term_max)
			.collect_vec();

		// Every node is its digits, together with what it may come to. Every
		// coefficient is positive, so a partial sum past `k` already breaks the
		// constraint.
		let mut layer = Vec::with_capacity(xs.len());
		for x in &xs {
			let ub = min(term_max(x), k);
			// The coefficient scales the leaf, which the digits below count in.
			let leaf = self.scaled(db, x, ub)?;
			let digits = self.digits(db, &leaf, &base)?;
			self.lex_leq(db, &digits, &base, k)?;
			layer.push((digits, ub));
		}

		while layer.len() > 1 {
			let mut next = Vec::with_capacity(layer.len().div_ceil(2));
			for children in layer.chunks(2) {
				match children {
					[x] => next.push(x.clone()),
					[x, y] => {
						let ub = min(x.1 + y.1, k);
						let digits = self.add_nodes(db, &x.0, &y.0, &base, ub)?;
						self.lex_leq(db, &digits, &base, k)?;
						next.push((digits, ub));
					}
					_ => unreachable!("nodes are taken two at a time"),
				}
			}
			layer = next;
		}

		let root = layer.pop().map(|(digits, _)| digits).unwrap_or_default();
		match con.cmp() {
			LimitComp::LessEq => self.lex_leq(db, &root, &base, k),
			LimitComp::Equal => self.pin(db, &root, &base, k),
		}
	}
}

impl ModuloTotalizerEncoder {
	/// The leaf a term comes to, its coefficient counted in.
	///
	/// A unit coefficient is the variable itself; anything else is the variable
	/// scaled, which is a view on its values rather than a constraint on them.
	fn scaled<Db: ClauseDatabase + ?Sized>(
		&self,
		db: &mut Db,
		term: &(Coeff, IntVar),
		ub: Coeff,
	) -> Result<IntVar, Unsatisfiable> {
		let (c, x) = term;
		if *c == 1 {
			return Ok(x.clone());
		}
		let domain = x
			.domain()
			.iter()
			.flatten()
			.map(|v| v * c)
			.filter(|&v| v <= ub)
			.map(|v| v..=v)
			.collect();
		let scaled = self.new_int_var(db, domain, "c")?;
		self.encoder().encode(
			db,
			&IntTernary::new(
				(*c, x.clone()),
				(1, IntVar::new(0..=0)),
				Comparator::Equal,
				(1, scaled.clone()),
			),
		)?;
		Ok(scaled)
	}
}

#[cfg(test)]
mod tests {
	use crate::helpers::tests::{linear_test_suite, prelude::*};

	card1_test_suite! {
		modulo_totalizer_encoder_card1, ModuloTotalizerEncoder::default()
	}
	linear_test_suite!(modulo_totalizer_encoder, ModuloTotalizerEncoder::default());

	// The radix is what sets the number of levels: two holds a node in binary,
	// and anything past `k` gives it a single digit.
	linear_test_suite!(
		modulo_totalizer_encoder_base_2,
		ModuloTotalizerEncoder::default().with_base(Some(vec![2]))
	);
	linear_test_suite!(
		modulo_totalizer_encoder_base_3,
		ModuloTotalizerEncoder::default().with_base(Some(vec![3]))
	);
	linear_test_suite!(
		modulo_totalizer_encoder_base_100,
		ModuloTotalizerEncoder::default().with_base(Some(vec![100]))
	);
	linear_test_suite!(
		modulo_totalizer_encoder_base_3_2,
		ModuloTotalizerEncoder::default().with_base(Some(vec![3, 2]))
	);

	#[test]
	fn greedy_base_divides_the_coefficients() {
		let base = |coefs: &[Coeff], k| ModuloTotalizerEncoder::greedy_base(coefs.to_vec(), coefs.len(), k);
		// Three divides every coefficient, meeting the 50% share, so the
		// first digit is zero for all of them. Two clears the share once
		// more; past that nothing does, and every remaining digit is the
		// `⌊√4⌋` fallback.
		assert_eq!(base(&[3, 6, 9, 12], 30), vec![3, 2, 2, 2, 2]);
		// Without a divisor to exploit every digit is the fallback.
		assert_eq!(base(&[1, 1, 1], 7), vec![2, 2, 2]);
		// Dividing one of two coefficients is only a 50% share, which still
		// clears the bar, and a tie takes the smallest, so five is preferred
		// over seven.
		assert_eq!(base(&[5, 7], 12), vec![5, 2, 2]);
		// Six ties with its own divisors, so it comes apart into them.
		assert_eq!(base(&[6, 6], 5), vec![2, 3]);
		// The base has to be usable even for a degenerate bound.
		assert_eq!(base(&[1], 0), vec![2]);
	}

	/// The point of the modulo totalizer is that its nodes are smaller than the
	/// totalizer's, so guard against a change that would make it pointless.
	#[test]
	fn smaller_than_the_totalizer() {
		const N: usize = 40;
		let con = |vars: &[Lit]| {
			Linear::new(
				LinExp::from_slices(&(1..=N as Coeff).collect_vec(), vars),
				Comparator::LessEq,
				400,
			)
		};

		let mut gt = Cnf::default();
		let vars = gt.new_var_range(N).iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder<TotalizerEncoder, TotalizerEncoder>>::default()
			.encode(&mut gt, &con(&vars))
			.unwrap();

		let mut gmto = Cnf::default();
		let vars = gmto.new_var_range(N).iter_lits().collect_vec();
		LinearEncoder::<StaticLinEncoder<ModuloTotalizerEncoder, ModuloTotalizerEncoder>>::default()
			.encode(&mut gmto, &con(&vars))
			.unwrap();

		assert!(
			gmto.num_vars() < gt.num_vars(),
			"expected fewer variables than the totalizer, got {} instead of {}",
			gmto.num_vars(),
			gt.num_vars()
		);
		assert!(
			gmto.num_clauses() < gt.num_clauses(),
			"expected fewer clauses than the totalizer, got {} instead of {}",
			gmto.num_clauses(),
			gt.num_clauses()
		);
	}
}
