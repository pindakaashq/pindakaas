use itertools::Itertools;

// macro_rules! p {
//     ($($tokens: tt)*) => {
//         println!("cargo:warning={}", format!($($tokens)*))
//     }
// }

use std::fs;
use std::path::Path;

use flate2::read::GzDecoder;
use tar::Archive;

fn scm() -> Result<Vec<(usize, u32, String)>, std::io::Error> {
	Archive::new(GzDecoder::new(fs::File::open(Path::new(
		"./res/scm.tar.gz",
	))?))
	.unpack("./res/")
	.unwrap();

	Ok(fs::read_dir("./res/scm")?
		.into_iter()
		.map(|f| {
			let path = f.unwrap().path();
			let scm = fs::read_to_string(&path)
				.unwrap()
				.lines()
				.filter(|line| !(line.is_empty() || line.starts_with('#')))
				.join(";");
			let (bits, v) = path
				.file_stem()
				.unwrap()
				.to_str()
				.unwrap()
				.split('_')
				.collect::<Vec<_>>()
				.into_iter()
				.collect_tuple()
				.unwrap();
			(bits.parse().unwrap(), v.parse().unwrap(), scm)
		})
		.sorted()
		.collect())
}

pub fn main() {
	println!("cargo:rerun-if-changed=res/scm.tar.gz");
	println!("cargo:rerun-if-changed=build.rs");

	let scm = scm().unwrap();

	let o = format!(
		"pub(crate) static SCM: [(usize, u32, &str); {}] = [\n{}\n];",
		scm.len(),
		scm.iter()
			.map(|(x, c, scm)| format!("\t({}, {}, \"{}\")", x, c, scm))
			.join(",\n")
	);
	fs::write("./src/int/scm.rs", o).unwrap();
}
