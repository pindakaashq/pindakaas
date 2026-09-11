//! Timing every linear encoder over the constraint shapes that tell them apart.
//!
//! Wall time alone does not say whether a slow encoder is slow per clause or
//! merely producing a large encoding, so every case is also measured for size
//! and reported as clauses per second. The size table printed by
//! `PINDAKAAS_SIZES=1` is the same measurement the throughput counter uses.
//!
//! ```text
//! cargo bench -p pindakaas --bench encoding        # timings
//! PINDAKAAS_SIZES=1 cargo bench -p pindakaas --bench encoding   # sizes only
//! ```

// Only some of the crate's dev-dependencies are used by any one test target.
#![allow(
	unused_crate_dependencies,
	reason = "shared across the crate's test targets"
)]

use std::fmt::{self, Display};

use divan::{counter::ItemsCount, Bencher};
use pindakaas::{
	constraint::{
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		linear::{Comparator, LimitComp, LinExp, Linear},
	},
	decision::integer::IntVar,
	BoolVal, ClauseDatabase, Cnf, Encoder, Lit,
};

mod common;

use common::{coefficients, encode, Coeff, CARD_ENCODERS, ENCODERS};

/// What a term of a benchmarked constraint is made of.
enum Terms {
	/// One literal per term, worth its coefficient.
	Lits(Vec<Coeff>),
	/// One exactly-one group per term, worth whichever of its weights is
	/// chosen — the shape the generalized encodings are named for.
	Groups(Vec<Vec<Coeff>>),
	/// One integer variable per term, over `0..=max`. Nothing about a linear
	/// constraint says its terms are literals, and a wide domain is where the
	/// intermediates of a decomposition are widest.
	Ints(Vec<Coeff>),
}

/// A constraint to be encoded, before it is given a comparator.
struct Shape {
	name: String,
	terms: Terms,
	k: Coeff,
}

/// One measurement: an encoder against a shape under one comparator.
///
/// The size is taken once when the case is built, so that the throughput
/// counter and the size table are the same number rather than two
/// measurements that could disagree.
struct Case {
	enc: &'static str,
	shape: Shape,
	cmp: Comparator,
	size: Option<(usize, usize, usize)>,
}

impl Display for Case {
	/// What divan labels the case with, and what the size table sorts by.
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let op = if self.cmp == Comparator::LessEq {
			"<="
		} else {
			"=="
		};
		write!(f, "{} {op} {}", self.shape.name, self.enc)
	}
}

impl Case {
	/// Every encoder of `encoders` against every shape, under both
	/// comparators.
	fn matrix(
		shapes: impl IntoIterator<Item = Shape>,
		encoders: &'static [&'static str],
	) -> Vec<Self> {
		let mut cases = Vec::new();
		for shape in shapes {
			for cmp in [Comparator::LessEq, Comparator::Equal] {
				for &enc in encoders {
					let shape = Shape {
						name: shape.name.clone(),
						terms: match &shape.terms {
							Terms::Lits(c) => Terms::Lits(c.clone()),
							Terms::Groups(g) => Terms::Groups(g.clone()),
							Terms::Ints(d) => Terms::Ints(d.clone()),
						},
						k: shape.k,
					};
					let mut case = Self {
						enc,
						shape,
						cmp,
						size: None,
					};
					case.size = case.measure();
					cases.push(case);
				}
			}
		}
		cases
	}

	/// What one encoding of the case costs in output, or `None` where
	/// encoding it proves the constraint unsatisfiable.
	fn measure(&self) -> Option<(usize, usize, usize)> {
		let (mut cnf, con) = self.build();
		let before = (cnf.num_vars(), cnf.num_clauses(), cnf.literals());
		encode(self.enc, &mut cnf, &con).ok()?;
		Some((
			cnf.num_vars() - before.0,
			cnf.num_clauses() - before.1,
			cnf.literals() - before.2,
		))
	}

	/// Build the constraint into a fresh database.
	///
	/// Everything a term stands for — the literals of a group and the
	/// at-most-one constraint over them — is in the database before the linear
	/// encoder runs, so that a measurement covers the linear encoding and
	/// nothing else.
	fn build(&self) -> (Cnf, Linear) {
		let mut cnf = Cnf::default();
		let exp = match &self.shape.terms {
			Terms::Lits(coeffs) => {
				let lits: Vec<Lit> = cnf.new_var_range(coeffs.len()).iter_lits().collect();
				LinExp::from_slices(coeffs, &lits)
			}
			Terms::Groups(groups) => {
				let mut exp = LinExp::default();
				for weights in groups {
					let lits: Vec<Lit> = cnf.new_var_range(weights.len()).iter_lits().collect();
					PairwiseEncoder::default()
						.encode(
							&mut cnf,
							&CardinalityOne::new(lits.clone(), LimitComp::Equal),
						)
						.expect("an exactly-one over fresh literals is satisfiable");
					let walk = weights
						.iter()
						.copied()
						.zip(lits.iter().map(|&l| BoolVal::Lit(l)));
					let x = IntVar::from_direct_walk(&mut cnf, walk)
						.expect("a group of fresh literals channels to nothing");
					exp = exp + x;
				}
				exp
			}
			Terms::Ints(maxima) => maxima
				.iter()
				.fold(LinExp::default(), |exp, &max| exp + IntVar::new(0..=max)),
		};
		(cnf, Linear::new(exp, self.cmp, self.shape.k))
	}

	/// Time the case, counting the clauses it emits so that a slow encoder
	/// producing a large encoding reads differently from a slow one producing
	/// a small.
	fn run(&self, bencher: Bencher) {
		let clauses = self.size.map_or(1, |(_, clauses, _)| clauses.max(1));
		bencher
			.counter(ItemsCount::new(clauses))
			.with_inputs(|| self.build())
			.bench_local_values(|(mut cnf, con)| {
				let _ = encode(self.enc, &mut cnf, &con);
			});
	}
}

/// A bound the sum can in fact reach, so that an equality is not settled
/// before any encoder sees it: every second coefficient, which is near half
/// the total and is a subset sum by construction.
fn reachable_bound(coeffs: &[Coeff]) -> Coeff {
	coeffs.iter().step_by(2).sum()
}

/// Shapes that differ in what the coefficients look like, at a fixed width.
fn shapes() -> Vec<Shape> {
	let mut out = Vec::new();
	for (label, max) in [("pb-small", 8), ("pb-large", 512)] {
		let coeffs = coefficients(10, max, 1);
		out.push(Shape {
			name: format!("{label}-10"),
			k: reachable_bound(&coeffs),
			terms: Terms::Lits(coeffs),
		});
	}
	let coprime = vec![3, 5, 7, 11, 13, 17, 19, 23];
	out.push(Shape {
		name: "pb-coprime-8".into(),
		k: reachable_bound(&coprime),
		terms: Terms::Lits(coprime),
	});
	let wide = coefficients(40, 4, 2);
	out.push(Shape {
		name: "pb-wide-40".into(),
		k: reachable_bound(&wide),
		terms: Terms::Lits(wide),
	});
	let groups: Vec<Vec<Coeff>> = (0..6).map(|g| coefficients(4, 12, 10 + g)).collect();
	// A group contributes one of its weights, so a bound the sum reaches is a
	// choice from each of them.
	let k = groups.iter().map(|g| g[g.len() / 2]).sum::<Coeff>();
	out.push(Shape {
		name: "amo-6x4".into(),
		k,
		terms: Terms::Groups(groups),
	});
	let maxima = vec![40; 6];
	out.push(Shape {
		name: "int-6x40".into(),
		k: maxima.iter().sum::<Coeff>() / 2,
		terms: Terms::Ints(maxima),
	});
	out
}

/// Cardinality constraints, which reach a different encoder slot and are the
/// only shapes [`SortingNetworkEncoder`] takes.
fn card_shapes() -> Vec<Shape> {
	[10, 20, 40, 80]
		.into_iter()
		.map(|n| Shape {
			name: format!("card-{n}"),
			terms: Terms::Lits(vec![1; n]),
			k: n as Coeff / 2,
		})
		.collect()
}

/// The same shape at growing widths, so the exponent is visible.
fn widths() -> Vec<Shape> {
	[8, 16, 32, 64]
		.into_iter()
		.map(|n| {
			let coeffs = coefficients(n, 8, 3);
			Shape {
				name: format!("pb-n{n}"),
				k: reachable_bound(&coeffs),
				terms: Terms::Lits(coeffs),
			}
		})
		.collect()
}

/// The same width at growing coefficients, which is what grows the bound.
///
/// Scaling every coefficient together would change nothing: aggregation
/// divides a constraint by the greatest common divisor of its terms.
fn bounds() -> Vec<Shape> {
	[8, 64, 512, 4096]
		.into_iter()
		.map(|max| {
			let coeffs = coefficients(8, max, 4);
			let k = reachable_bound(&coeffs);
			Shape {
				name: format!("pb-k{k}"),
				k,
				terms: Terms::Lits(coeffs),
			}
		})
		.collect()
}

#[divan::bench(args = Case::matrix(shapes(), ENCODERS))]
fn shape(bencher: Bencher, case: &Case) {
	case.run(bencher);
}

#[divan::bench(args = Case::matrix(card_shapes(), CARD_ENCODERS))]
fn cardinality(bencher: Bencher, case: &Case) {
	case.run(bencher);
}

#[divan::bench(args = Case::matrix(widths(), ENCODERS))]
fn width(bencher: Bencher, case: &Case) {
	case.run(bencher);
}

#[divan::bench(args = Case::matrix(bounds(), ENCODERS))]
fn bound(bencher: Bencher, case: &Case) {
	case.run(bencher);
}

fn main() {
	if std::env::var_os("PINDAKAAS_SIZES").is_some() {
		println!(
			"{:>14} {:>4} {:>7} {:>7} {:>8} {:>9}",
			"shape", "cmp", "enc", "vars", "clauses", "literals"
		);
		let all = [
			Case::matrix(card_shapes(), CARD_ENCODERS),
			Case::matrix(shapes(), ENCODERS),
			Case::matrix(widths(), ENCODERS),
			Case::matrix(bounds(), ENCODERS),
		];
		for case in all.iter().flatten() {
			let op = if case.cmp == Comparator::LessEq {
				"<="
			} else {
				"=="
			};
			match case.size {
				Some((vars, clauses, literals)) => println!(
					"{:>14} {op:>4} {:>7} {vars:>7} {clauses:>8} {literals:>9}",
					case.shape.name, case.enc
				),
				None => println!(
					"{:>14} {op:>4} {:>7} {:>27}",
					case.shape.name, case.enc, "unsatisfiable"
				),
			}
		}
		return;
	}
	divan::main();
}
