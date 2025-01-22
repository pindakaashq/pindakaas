pub fn main() {
	#[cfg(feature = "scm")]
	{
		println!("cargo:rerun-if-changed=../pindakaas-scm/res");
		const LIMIT: Option<usize> = Some(10);
		std::fs::write(
			std::path::Path::new(&std::env::var("OUT_DIR").unwrap()).join("scm_db.rs"),
			pindakaas_scm::generate(LIMIT, true).unwrap(),
		)
		.unwrap();
	}
}
