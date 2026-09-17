//! What the cost and the quality harness both need: the coefficient type the
//! library does not export, the list of encoders, and a way to run one by name.

use itertools::Itertools;
use pindakaas::{
	constraint::linear::{
		AdderEncoder, DecisionDiagramEncoder, Linear, LinearEncoder, MixedRadixEncoder,
		SequentialCounterEncoder, StaticLinEncoder, TotalizerEncoder, WatchdogEncoder,
	},
	encoder::sorting_network::SortingNetworkEncoder,
	Cnf, Encoder, Unsatisfiable,
};

/// [`SortingNetworkEncoder`] only takes a cardinality constraint, so it joins
/// the others on the shapes that aggregate to one.
pub(crate) const CARD_ENCODERS: &[&str] = &[
	"adder", "diagram", "seq", "tree", "radix", "wdog", "wdog-l", "sort",
];

/// Encoders that take a linear constraint whatever its coefficients are.
pub(crate) const ENCODERS: &[&str] =
	&["adder", "diagram", "seq", "tree", "radix", "wdog", "wdog-l"];

/// Coefficient type of the library, which does not export the alias it uses.
pub(crate) type Coeff = i64;

/// Deterministic pseudo-random coefficients in `1..=max`, so that a case is
/// the same one from run to run without a dependency saying so.
pub(crate) fn coefficients(n: usize, max: Coeff, seed: u64) -> Vec<Coeff> {
	let mut state = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
	(0..n)
		.map(|_| {
			state = state
				.wrapping_mul(6364136223846793005)
				.wrapping_add(1442695040888963407);
			((state >> 33) % max as u64) as Coeff + 1
		})
		.collect()
}

/// [`coefficients`] without repeats, for weights a direct walk takes as values.
pub(crate) fn distinct_coefficients(n: usize, max: Coeff, seed: u64) -> Vec<Coeff> {
	let distinct = coefficients(16 * n, max, seed)
		.into_iter()
		.unique()
		.take(n)
		.collect_vec();
	assert_eq!(distinct.len(), n, "{n} distinct draws from 1..={max}");
	distinct
}

/// Encode `con` with the encoder named, whichever shape aggregation leaves.
pub(crate) fn encode(name: &str, cnf: &mut Cnf, con: &Linear) -> Result<(), Unsatisfiable> {
	match name {
		"adder" => LinearEncoder::<AdderEncoder>::default().encode(cnf, con),
		"diagram" => LinearEncoder::<DecisionDiagramEncoder>::default().encode(cnf, con),
		"seq" => LinearEncoder::<SequentialCounterEncoder>::default().encode(cnf, con),
		"tree" => LinearEncoder::<TotalizerEncoder>::default().encode(cnf, con),
		"radix" => LinearEncoder::<MixedRadixEncoder>::default().encode(cnf, con),
		"wdog" => LinearEncoder::<WatchdogEncoder>::default().encode(cnf, con),
		"wdog-l" => {
			// The local form is the same encoder, so it is configured rather
			// than named separately.
			let mut enc = WatchdogEncoder::default();
			let _ = enc.with_local(true);
			LinearEncoder::new(enc).encode(cnf, con)
		}
		"sort" => LinearEncoder::<
			StaticLinEncoder<AdderEncoder, AdderEncoder, SortingNetworkEncoder>,
		>::default()
		.encode(cnf, con),
		_ => unreachable!("unknown encoder {name}"),
	}
}
