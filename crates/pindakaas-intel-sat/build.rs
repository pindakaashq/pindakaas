//! This module contains the build script for the `pindakaas-intel-sat` crate.
//! It is responsible for compiling the Intel SAT solver using a C++ compiler
//! and linking it to the crate.

/// Function that renames the standard `ipasir_` when using the `cc` crate to
/// avoid conflicts when linking.
pub fn change_ipasir_prefix(build: &mut cc::Build, prefix: &str) {
	for f in [
		"_signature",
		"_init",
		"_release",
		"_add",
		"_assume",
		"_solve",
		"_val",
		"_failed",
		"_set_terminate",
		"_set_learn",
		"_connect_external_propagator",
		"_get_external_propagator",
		"_disconnect_external_propagator",
		"_add_observed_var",
		"_remove_observed_var",
		"_reset_observed_vars",
		"_is_decision",
		"_force_backtrack",
	] {
		let _ = build.define(&format!("ipasir{f}"), format!("{prefix}{f}").as_ref());
	}
}

fn main() {
	let src = [
		"vendor/intel_sat/Topi.cc",
		"vendor/intel_sat/TopiAsg.cc",
		"vendor/intel_sat/TopiBacktrack.cc",
		"vendor/intel_sat/TopiBcp.cc",
		"vendor/intel_sat/TopiBitCompression.cc",
		"vendor/intel_sat/TopiCompression.cc",
		"vendor/intel_sat/TopiConflictAnalysis.cc",
		"vendor/intel_sat/TopiDebugPrinting.cc",
		"vendor/intel_sat/TopiDecision.cc",
		"vendor/intel_sat/TopiInprocess.cc",
		"vendor/intel_sat/TopiRestart.cc",
		"vendor/intel_sat/TopiWL.cc",
		"vendor/intel_sat/Topor.cc",
		"vendor/intel_sat/ToporIpasir.cc",
	];

	let mut builder = cc::Build::new();
	let build = builder.cpp(true).flag_if_supported("-std=c++20");

	#[cfg(not(debug_assertions))]
	// I'm not sure why this is not automatic, but assertions still seem to trigger otherwise.
	let _ = build.define("NDEBUG", None);

	change_ipasir_prefix(build, "intel_sat");
	build.files(src).cargo_warnings(false).compile("intel_sat");
}
