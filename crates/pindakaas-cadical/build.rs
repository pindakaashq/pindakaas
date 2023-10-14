fn main() {
	let src = [
		"vendor/cadical/src/analyze.cpp",
		"vendor/cadical/src/arena.cpp",
		"vendor/cadical/src/assume.cpp",
		"vendor/cadical/src/averages.cpp",
		"vendor/cadical/src/backtrack.cpp",
		"vendor/cadical/src/backward.cpp",
		"vendor/cadical/src/bins.cpp",
		"vendor/cadical/src/block.cpp",
		"vendor/cadical/src/ccadical.cpp",
		"vendor/cadical/src/checker.cpp",
		"vendor/cadical/src/clause.cpp",
		"vendor/cadical/src/collect.cpp",
		"vendor/cadical/src/compact.cpp",
		"vendor/cadical/src/condition.cpp",
		"vendor/cadical/src/config.cpp",
		"vendor/cadical/src/constrain.cpp",
		"vendor/cadical/src/contract.cpp",
		"vendor/cadical/src/cover.cpp",
		"vendor/cadical/src/decide.cpp",
		"vendor/cadical/src/decompose.cpp",
		"vendor/cadical/src/deduplicate.cpp",
		"vendor/cadical/src/elim.cpp",
		"vendor/cadical/src/ema.cpp",
		"vendor/cadical/src/extend.cpp",
		"vendor/cadical/src/external.cpp",
		"vendor/cadical/src/external_propagate.cpp",
		"vendor/cadical/src/file.cpp",
		"vendor/cadical/src/flags.cpp",
		"vendor/cadical/src/flip.cpp",
		"vendor/cadical/src/format.cpp",
		"vendor/cadical/src/gates.cpp",
		"vendor/cadical/src/instantiate.cpp",
		"vendor/cadical/src/internal.cpp",
		"vendor/cadical/src/limit.cpp",
		"vendor/cadical/src/logging.cpp",
		"vendor/cadical/src/lookahead.cpp",
		"vendor/cadical/src/lratbuilder.cpp",
		"vendor/cadical/src/lratchecker.cpp",
		"vendor/cadical/src/lucky.cpp",
		"vendor/cadical/src/message.cpp",
		"vendor/cadical/src/minimize.cpp",
		"vendor/cadical/src/occs.cpp",
		"vendor/cadical/src/options.cpp",
		"vendor/cadical/src/parse.cpp",
		"vendor/cadical/src/phases.cpp",
		"vendor/cadical/src/probe.cpp",
		"vendor/cadical/src/profile.cpp",
		"vendor/cadical/src/proof.cpp",
		"vendor/cadical/src/propagate.cpp",
		"vendor/cadical/src/queue.cpp",
		"vendor/cadical/src/random.cpp",
		"vendor/cadical/src/reap.cpp",
		"vendor/cadical/src/reduce.cpp",
		"vendor/cadical/src/rephase.cpp",
		"vendor/cadical/src/report.cpp",
		"vendor/cadical/src/resources.cpp",
		"vendor/cadical/src/restart.cpp",
		"vendor/cadical/src/restore.cpp",
		"vendor/cadical/src/score.cpp",
		"vendor/cadical/src/shrink.cpp",
		"vendor/cadical/src/signal.cpp",
		"vendor/cadical/src/solution.cpp",
		"vendor/cadical/src/solver.cpp",
		"vendor/cadical/src/stats.cpp",
		"vendor/cadical/src/subsume.cpp",
		"vendor/cadical/src/terminal.cpp",
		"vendor/cadical/src/ternary.cpp",
		"vendor/cadical/src/tracer.cpp",
		"vendor/cadical/src/transred.cpp",
		"vendor/cadical/src/util.cpp",
		"vendor/cadical/src/var.cpp",
		"vendor/cadical/src/version.cpp",
		"vendor/cadical/src/vivify.cpp",
		"vendor/cadical/src/walk.cpp",
		"vendor/cadical/src/watch.cpp",
	];

	let mut builder = cc::Build::new();
	let build = builder
		.cpp(true)
		.flag_if_supported("-std=c++11")
		.define("NBUILD", None)
		.define("NUNLOCKED", None)
		.define("NTRACING", None)
		.define("QUIET", None);

	assert_eq!(
		env!("CARGO_PKG_VERSION"),
		include_str!("vendor/cadical/VERSION").trim()
	);

	build.files(src);

	build.compile("cadical");
}
