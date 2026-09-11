//! What an encoding costs the solver, rather than what it costs to produce.
//!
//! Wall time on a modern SAT solver moves with the machine and with the order
//! the clauses happened to be added, so the primary measure here is the least
//! conflict budget CaDiCaL needs before it decides the instance — found by
//! doubling and then bisecting the `conflicts` limit. It is deterministic, and
//! it is the number that moves when an encoding's propagation strength moves.
//! Wall time is reported beside it, best of three, for scale.
//!
//! The instances search: a lone constraint is settled by propagation and
//! separates nothing. Run with
//!
//! ```text
//! cargo run --release --example encoding_quality
//! ```

// Only some of the crate's dev-dependencies are used by any one test target.
#![allow(
	unused_crate_dependencies,
	reason = "shared across the crate's test targets"
)]

#[path = "../benches/common/mod.rs"]
mod common;

use std::{
	io::{self, Write},
	time::{Duration, Instant},
};

use common::{coefficients, encode, Coeff, CARD_ENCODERS, ENCODERS};
use pindakaas::{
	constraint::{
		cardinality_one::{CardinalityOne, PairwiseEncoder},
		linear::{Comparator, LimitComp, LinExp, Linear},
	},
	decision::integer::IntVar,
	solver::{cadical::Cadical, SolveResult, Solver, TermSignal, TerminateCallback},
	BoolVal, ClauseDatabase, Cnf, Encoder, Lit, Unsatisfiable,
};

/// How long one solve is given before the clock ends it, whatever its
/// conflict limit says.
const BUDGET: Duration = Duration::from_secs(90);

/// Conflict budget past which an instance is reported as unmeasured rather
/// than waited for.
const CAP: i32 = 1 << 20;

/// An instance and the encoders it is worth running.
struct Family {
	name: &'static str,
	encoders: &'static [&'static str],
	/// Build the instance with the named encoder, or report that encoding it
	/// already proved it unsatisfiable.
	build: fn(&str) -> Result<Cnf, Unsatisfiable>,
}

/// How a solve ended.
#[derive(PartialEq)]
enum Probe {
	/// Satisfiable or unsatisfiable, within both limits.
	Decided(&'static str),
	/// The conflict limit was reached.
	OutOfConflicts,
	/// The clock was reached, which says nothing about the conflict limit.
	OutOfTime,
}

/// A combinatorial auction: bids over overlapping item sets, with a revenue
/// floor.
///
/// The item constraints are at-most-one whatever the encoder, so what is
/// measured here is the encoder on the revenue constraint — a wide sum with
/// large coefficients — against a background it shares with every other run.
fn auction(enc: &str) -> Result<Cnf, Unsatisfiable> {
	const ITEMS: usize = 14;
	const BIDS: usize = 40;
	let mut cnf = Cnf::default();
	let bids: Vec<Lit> = cnf.new_var_range(BIDS).iter_lits().collect();
	let prices = coefficients(BIDS, 400, 30);
	let mut covers: Vec<Vec<Lit>> = vec![Vec::new(); ITEMS];
	for (b, &bid) in bids.iter().enumerate() {
		// Three items per bid, spread so that the bids overlap.
		for j in 0..3 {
			covers[(b * 5 + j * 3) % ITEMS].push(bid);
		}
	}
	for lits in covers {
		PairwiseEncoder::default()
			.encode(&mut cnf, &CardinalityOne::new(lits, LimitComp::LessEq))?;
	}
	// Heuristic: a floor near what a third of the bids are worth is past what
	// the item constraints leave room for, without being obviously so.
	let floor = prices.iter().sum::<Coeff>() / 3;
	let con = Linear::new(
		LinExp::from_slices(&prices, &bids),
		Comparator::GreaterEq,
		floor,
	);
	encode(enc, &mut cnf, &con)?;
	Ok(cnf)
}

/// The least conflict budget that decides `cnf`.
///
/// Doubling first, then bisecting: the budget spans several orders of
/// magnitude across the encoders, so a linear walk up to it would be the
/// expensive part of this program.
fn conflicts(cnf: &Cnf) -> Result<i32, &'static str> {
	let decided = |limit| match probe(cnf, Some(limit)).0 {
		Probe::Decided(_) => Ok(true),
		Probe::OutOfConflicts => Ok(false),
		Probe::OutOfTime => Err("t/o"),
	};
	if decided(1)? {
		return Ok(1);
	}
	let mut hi = 2;
	while hi <= CAP && !decided(hi)? {
		hi *= 2;
	}
	if hi > CAP {
		return Err("over");
	}
	let mut lo = hi / 2;
	while lo + 1 < hi {
		let mid = lo + (hi - lo) / 2;
		if decided(mid)? {
			hi = mid;
		} else {
			lo = mid;
		}
	}
	Ok(hi)
}

/// A multiple-choice knapsack: one item taken from each group, under a weight
/// budget and above a profit floor.
fn knapsack(enc: &str) -> Result<Cnf, Unsatisfiable> {
	const GROUPS: usize = 12;
	const CHOICES: usize = 6;
	let mut cnf = Cnf::default();
	let (mut weight, mut profit) = (LinExp::default(), LinExp::default());
	let (mut budget, mut floor) = (0, 0);
	for g in 0..GROUPS {
		let lits: Vec<Lit> = cnf.new_var_range(CHOICES).iter_lits().collect();
		PairwiseEncoder::default().encode(
			&mut cnf,
			&CardinalityOne::new(lits.clone(), LimitComp::Equal),
		)?;
		let ws = coefficients(CHOICES, 60, 20 + g as u64);
		// Heuristic: profit tracks weight, so cheap items are also poor ones
		// and the choice is a real trade-off rather than a dominated one.
		let ps: Vec<Coeff> = ws.iter().map(|w| w * 3 / 2 + 1).collect();
		let bools = || lits.iter().map(|&l| BoolVal::Lit(l));
		weight = weight + IntVar::from_direct_walk(&mut cnf, ws.iter().copied().zip(bools()))?;
		profit = profit + IntVar::from_direct_walk(&mut cnf, ps.iter().copied().zip(bools()))?;
		// Halfway between the cheapest and the dearest choice of each group,
		// so that neither constraint is slack.
		budget += (ws.iter().min().unwrap() + ws.iter().max().unwrap()) / 2;
		floor += (ps.iter().min().unwrap() + ps.iter().max().unwrap()) / 2;
	}
	encode(
		enc,
		&mut cnf,
		&Linear::new(weight, Comparator::LessEq, budget),
	)?;
	encode(
		enc,
		&mut cnf,
		&Linear::new(profit, Comparator::GreaterEq, floor + 1),
	)?;
	Ok(cnf)
}

fn main() {
	let families = [
		Family {
			name: "pigeonhole",
			encoders: CARD_ENCODERS,
			build: pigeonhole,
		},
		Family {
			name: "market-split",
			encoders: ENCODERS,
			build: market_split,
		},
		Family {
			name: "knapsack",
			encoders: ENCODERS,
			build: knapsack,
		},
		Family {
			name: "auction",
			encoders: ENCODERS,
			build: auction,
		},
	];
	println!(
		"{:>13} {:>7} {:>7} {:>8} {:>10} {:>9} {:>8}",
		"instance", "enc", "vars", "clauses", "conflicts", "time", "result"
	);
	for family in families {
		for &enc in family.encoders {
			let Ok(cnf) = (family.build)(enc) else {
				println!(
					"{:>13} {enc:>7} {:>45}",
					family.name, "unsatisfiable while encoding"
				);
				let _ = io::stdout().flush();
				continue;
			};
			// Timed first: an instance the solver cannot finish at all is one
			// the conflict search would spend its whole budget failing to
			// bisect.
			let (time, verdict) = wall_time(&cnf);
			let budget = if verdict == "t/o" {
				String::from("t/o")
			} else {
				conflicts(&cnf).map_or_else(
					|why| {
						if why == "over" {
							format!(">{CAP}")
						} else {
							why.to_owned()
						}
					},
					|c| c.to_string(),
				)
			};
			println!(
				"{:>13} {enc:>7} {:>7} {:>8} {budget:>10} {:>8.1}ms {verdict:>8}",
				family.name,
				cnf.num_vars(),
				cnf.num_clauses(),
				time.as_secs_f64() * 1e3,
			);
			// A row at a time, so a run that is still going says what it has.
			let _ = io::stdout().flush();
		}
	}
}

/// Two weighted equalities over the same literals, each reachable on its own.
///
/// A single subset-sum whose target is out of reach is settled by propagation
/// on any domain consistent encoding and measures nothing; two of them force
/// the search to reconcile them.
fn market_split(enc: &str) -> Result<Cnf, Unsatisfiable> {
	const N: usize = 20;
	let mut cnf = Cnf::default();
	let lits: Vec<Lit> = cnf.new_var_range(N).iter_lits().collect();
	for (seed, weights) in [coefficients(N, 40, 7), coefficients(N, 40, 8)]
		.into_iter()
		.enumerate()
	{
		// Every second weight is a subset sum, so neither equality is out of
		// reach by itself.
		let k = weights.iter().skip(seed).step_by(2).sum();
		let con = Linear::new(LinExp::from_slices(&weights, &lits), Comparator::Equal, k);
		encode(enc, &mut cnf, &con)?;
	}
	Ok(cnf)
}

/// `2n+1` pigeons into `n` holes of capacity two.
///
/// Capacity two rather than one keeps the hole constraint a cardinality
/// constraint: at one, aggregation reports it as at-most-one and it reaches
/// the at-most-one encoder instead of the one under test.
fn pigeonhole(enc: &str) -> Result<Cnf, Unsatisfiable> {
	const HOLES: usize = 7;
	const CAPACITY: Coeff = 2;
	let pigeons = HOLES * CAPACITY as usize + 1;
	let mut cnf = Cnf::default();
	let grid: Vec<Vec<Lit>> = (0..pigeons)
		.map(|_| cnf.new_var_range(HOLES).iter_lits().collect())
		.collect();
	for row in &grid {
		PairwiseEncoder::default().encode(
			&mut cnf,
			&CardinalityOne::new(row.clone(), LimitComp::Equal),
		)?;
	}
	for h in 0..HOLES {
		let column: Vec<Lit> = grid.iter().map(|row| row[h]).collect();
		let con = Linear::new(
			LinExp::from_slices(&vec![1; pigeons], &column),
			Comparator::LessEq,
			CAPACITY,
		);
		encode(enc, &mut cnf, &con)?;
	}
	Ok(cnf)
}

/// Solve `cnf` under `limit` conflicts, or without one.
fn probe(cnf: &Cnf, limit: Option<i32>) -> (Probe, Duration) {
	let mut slv = Cadical::from(cnf);
	if let Some(limit) = limit {
		slv.set_limit("conflicts", limit);
	}
	let start = Instant::now();
	slv.set_terminate_callback(Some(move || {
		if start.elapsed() > BUDGET {
			TermSignal::Terminate
		} else {
			TermSignal::Continue
		}
	}));
	let outcome = match slv.solve() {
		SolveResult::Satisfied(_) => Probe::Decided("sat"),
		SolveResult::Unsatisfiable(_) => Probe::Decided("unsat"),
		// A solve that ran out the clock is not one that ran out of
		// conflicts, and the two must not be read as the same answer.
		SolveResult::Unknown if start.elapsed() > BUDGET => Probe::OutOfTime,
		SolveResult::Unknown => Probe::OutOfConflicts,
	};
	(outcome, start.elapsed())
}

/// Best of three unlimited solves, and what the instance turned out to be.
///
/// Three runs of an instance that takes a minute say no more than one does, so
/// the repeats stop once they have cost enough to have settled the spread.
fn wall_time(cnf: &Cnf) -> (Duration, &'static str) {
	let mut best = Duration::MAX;
	let mut verdict = "t/o";
	let spent = Instant::now();
	for _ in 0..3 {
		let (outcome, took) = probe(cnf, None);
		let Probe::Decided(said) = outcome else {
			return (took, "t/o");
		};
		(best, verdict) = (best.min(took), said);
		if spent.elapsed() > Duration::from_secs(20) {
			break;
		}
	}
	(best, verdict)
}
