use pindakaas_build_macros::change_ipasir_prefix;

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
	change_ipasir_prefix(build, "intel_sat");
	build.files(src).cargo_warnings(false).compile("intel_sat");
}
