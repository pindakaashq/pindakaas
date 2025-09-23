//! This module contains the build script for the `pindakaas-kissat` crate. It
//! is responsible for compiling the Kissat SAT solver using a C compiler and
//! linking it to the crate.

use std::{path::Path, process::Command};

fn main() {
	let src = [
		"vendor/kissat/src/allocate.c",
		"vendor/kissat/src/analyze.c",
		"vendor/kissat/src/ands.c",
		"vendor/kissat/src/application.c",
		"vendor/kissat/src/arena.c",
		"vendor/kissat/src/assign.c",
		"vendor/kissat/src/averages.c",
		"vendor/kissat/src/backbone.c",
		"vendor/kissat/src/backtrack.c",
		"vendor/kissat/src/build.c",
		"vendor/kissat/src/bump.c",
		"vendor/kissat/src/check.c",
		"vendor/kissat/src/classify.c",
		"vendor/kissat/src/clause.c",
		"vendor/kissat/src/collect.c",
		"vendor/kissat/src/colors.c",
		"vendor/kissat/src/compact.c",
		"vendor/kissat/src/config.c",
		"vendor/kissat/src/congruence.c",
		"vendor/kissat/src/decide.c",
		"vendor/kissat/src/deduce.c",
		"vendor/kissat/src/definition.c",
		"vendor/kissat/src/dense.c",
		"vendor/kissat/src/dump.c",
		"vendor/kissat/src/eliminate.c",
		"vendor/kissat/src/equivalences.c",
		"vendor/kissat/src/error.c",
		"vendor/kissat/src/factor.c",
		"vendor/kissat/src/fastel.c",
		"vendor/kissat/src/extend.c",
		"vendor/kissat/src/file.c",
		"vendor/kissat/src/flags.c",
		"vendor/kissat/src/format.c",
		"vendor/kissat/src/forward.c",
		"vendor/kissat/src/gates.c",
		"vendor/kissat/src/handle.c",
		"vendor/kissat/src/heap.c",
		"vendor/kissat/src/ifthenelse.c",
		"vendor/kissat/src/import.c",
		"vendor/kissat/src/internal.c",
		"vendor/kissat/src/kimits.c",
		"vendor/kissat/src/krite.c",
		"vendor/kissat/src/kitten.c",
		"vendor/kissat/src/learn.c",
		"vendor/kissat/src/logging.c",
		"vendor/kissat/src/lucky.c",
		"vendor/kissat/src/minimize.c",
		"vendor/kissat/src/mode.c",
		"vendor/kissat/src/options.c",
		"vendor/kissat/src/parse.c",
		"vendor/kissat/src/phases.c",
		"vendor/kissat/src/preprocess.c",
		"vendor/kissat/src/print.c",
		"vendor/kissat/src/probe.c",
		"vendor/kissat/src/profile.c",
		"vendor/kissat/src/promote.c",
		"vendor/kissat/src/proof.c",
		"vendor/kissat/src/propbeyond.c",
		"vendor/kissat/src/propdense.c",
		"vendor/kissat/src/propinitially.c",
		"vendor/kissat/src/proprobe.c",
		"vendor/kissat/src/propsearch.c",
		"vendor/kissat/src/queue.c",
		"vendor/kissat/src/reduce.c",
		"vendor/kissat/src/reorder.c",
		"vendor/kissat/src/reluctant.c",
		"vendor/kissat/src/rephase.c",
		"vendor/kissat/src/report.c",
		"vendor/kissat/src/resize.c",
		"vendor/kissat/src/resolve.c",
		"vendor/kissat/src/resources.c",
		"vendor/kissat/src/restart.c",
		"vendor/kissat/src/search.c",
		"vendor/kissat/src/shrink.c",
		"vendor/kissat/src/smooth.c",
		"vendor/kissat/src/sort.c",
		"vendor/kissat/src/stack.c",
		"vendor/kissat/src/statistics.c",
		"vendor/kissat/src/strengthen.c",
		"vendor/kissat/src/substitute.c",
		"vendor/kissat/src/sweep.c",
		"vendor/kissat/src/terminate.c",
		"vendor/kissat/src/tiers.c",
		"vendor/kissat/src/trail.c",
		"vendor/kissat/src/transitive.c",
		"vendor/kissat/src/utilities.c",
		"vendor/kissat/src/vector.c",
		"vendor/kissat/src/vivify.c",
		"vendor/kissat/src/walk.c",
		"vendor/kissat/src/warmup.c",
		"vendor/kissat/src/watch.c",
		"vendor/kissat/src/weaken.c",
		"vendor/kissat/src/witness.c",
	];

	let mut builder = cc::Build::new();

	let compiler = builder.try_get_compiler().unwrap();
	let version = include_str!("vendor/kissat/VERSION").trim();
	assert_eq!(version, "4.0.2", "unexpected version of Kissat detected");
	let git_id = String::from_utf8(
		Command::new("git")
			.current_dir("vendor/kissat")
			.args(["rev-parse", "HEAD"])
			.output()
			.unwrap()
			.stdout,
	)
	.unwrap();
	let date = String::from_utf8(
		Command::new("date")
			.env("LC_LANG", "en_US")
			.output()
			.unwrap()
			.stdout,
	)
	.unwrap();
	let uname = String::from_utf8(
		Command::new("uname")
			.args(["-srmn"])
			.output()
			.unwrap()
			.stdout,
	)
	.unwrap();

	let build = builder
		.include("./src")
		.flag_if_supported("-std=c99")
		.define("VERSION", format!("\"{version}\"").as_str())
		.define(
			"COMPILER",
			format!(
				"{:?}",
				format!(
					"{} {}",
					compiler.path().to_str().unwrap(),
					compiler.args().join(" ".as_ref()).to_str().unwrap()
				)
			)
			.as_ref(),
		)
		.define("ID", format!("\"{}\"", git_id.trim()).as_ref())
		.define(
			"BUILD",
			format!("\"{} {}\"", date.trim(), uname.trim()).as_ref(),
		)
		.define("QUIET", None);

	#[cfg(not(debug_assertions))]
	// I'm not sure why this is not automatic, but assertions still seem to trigger otherwise.
	let _ = build.define("NDEBUG", None);

	if build.get_compiler().is_like_msvc() {
		let _ = build.include(Path::new("vendor/kissat/src/msvc"));
	}

	let _ = build.files(src);

	build.compile("kissat");
}
