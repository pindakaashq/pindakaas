//! What the cost and the quality harness both need: the coefficient type the
//! library does not export, the list of encoders, and a way to run one by name.

use pindakaas::{
	constraint::linear::{
		AdderEncoder, DecisionDiagramEncoder, LinAggregator, Linear, LinearEncoder,
		MixedRadixEncoder, SequentialCounterEncoder, StaticLinEncoder, TotalizerEncoder,
		WatchdogEncoder,
	},
	encoder::sorting_network::SortingNetworkEncoder,
	Cnf, Encoder, Unsatisfiable,
};

/// Coefficient type of the library, which does not export the alias it uses.
pub(crate) type Coeff = i64;

/// Encoders that take a linear constraint whatever its coefficients are.
pub(crate) const ENCODERS: &[&str] =
	&["adder", "diagram", "seq", "tree", "radix", "wdog", "wdog-l"];

/// [`SortingNetworkEncoder`] only takes a cardinality constraint, so it joins
/// the others on the shapes that aggregate to one.
pub(crate) const CARD_ENCODERS: &[&str] = &[
	"adder", "diagram", "seq", "tree", "radix", "wdog", "wdog-l", "sort",
];

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

/// Encode `con` with the encoder named, in every slot aggregation may reach.
///
/// Naming an encoder only for the integer-linear slot would leave a
/// cardinality or Boolean-linear constraint on [`StaticLinEncoder`]'s default,
/// which is the adder whatever was asked for.
pub(crate) fn encode(name: &str, cnf: &mut Cnf, con: &Linear) -> Result<(), Unsatisfiable> {
	match name {
		"adder" => {
			LinearEncoder::<StaticLinEncoder<AdderEncoder, AdderEncoder, AdderEncoder>>::default()
				.encode(cnf, con)
		}
		"diagram" => LinearEncoder::<
			StaticLinEncoder<
				DecisionDiagramEncoder,
				DecisionDiagramEncoder,
				DecisionDiagramEncoder,
			>,
		>::default()
		.encode(cnf, con),
		"seq" => LinearEncoder::<
			StaticLinEncoder<
				SequentialCounterEncoder,
				SequentialCounterEncoder,
				SequentialCounterEncoder,
			>,
		>::default()
		.encode(cnf, con),
		"tree" => LinearEncoder::<
			StaticLinEncoder<TotalizerEncoder, TotalizerEncoder, TotalizerEncoder>,
		>::default()
		.encode(cnf, con),
		"radix" => LinearEncoder::<
			StaticLinEncoder<MixedRadixEncoder, MixedRadixEncoder, MixedRadixEncoder>,
		>::default()
		.encode(cnf, con),
		"wdog" => LinearEncoder::<
			StaticLinEncoder<WatchdogEncoder, WatchdogEncoder, WatchdogEncoder>,
		>::default()
		.encode(cnf, con),
		"wdog-l" => {
			// The local form is the same encoder, so it is configured rather
			// than named separately.
			let mut enc =
				StaticLinEncoder::<WatchdogEncoder, WatchdogEncoder, WatchdogEncoder>::default();
			let _ = enc.lin_encoder().with_local(true);
			let _ = enc.bool_lin_encoder().with_local(true);
			let _ = enc.card_encoder().with_local(true);
			LinearEncoder::new(enc, LinAggregator::default()).encode(cnf, con)
		}
		"sort" => LinearEncoder::<
			StaticLinEncoder<AdderEncoder, AdderEncoder, SortingNetworkEncoder>,
		>::default()
		.encode(cnf, con),
		_ => unreachable!("unknown encoder {name}"),
	}
}
