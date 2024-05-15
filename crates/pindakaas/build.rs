// macro_rules! p {
//     ($($tokens: tt)*) => {
//         println!("cargo:warning={}", format!($($tokens)*))
//     }
// }
use std::{fs, path::Path};

use flate2::read::GzDecoder;
use itertools::Itertools;
use tar::Archive;

fn scm() -> Result<Vec<(usize, u32, Vec<ScmNode>)>, std::io::Error> {
	if Path::new("./res/scm").exists() {
		fs::remove_dir_all("./res/scm")?;
		fs::create_dir("./res/scm")?;
	} else {
		fs::create_dir("./res/scm")?;
	}

	let db = Path::new("./res/scm.tar.gz");
	assert!(db.exists());

	Archive::new(GzDecoder::new(fs::File::open(db)?))
		.unpack("./res/")
		.unwrap();

	Ok(fs::read_dir("./res/scm")?
		.map(|f| {
			let path = f.unwrap().path();
			let scm = fs::read_to_string(&path)
				.unwrap()
				.lines()
				.filter(|line| !(line.is_empty() || line.starts_with('#')))
				.map(|line| match line.split(',').collect::<Vec<_>>()[..] {
					[i, i1, sh1, add, i2, sh2] => ScmNode {
						i: i.parse().unwrap(),
						i1: i1.parse().unwrap(),
						sh1: sh1.parse().unwrap(),
						add: match add {
							"+" => true,
							"-" => false,
							_ => unreachable!(),
						},
						i2: i2.parse().unwrap(),
						sh2: sh2.parse().unwrap(),
					},
					_ => panic!("Unexpected line {line}"),
				})
				.collect();
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
		.sorted_by_key(|(b, c, _)| (*b, *c))
		.collect())
}

//  TODO ? <C: Coefficient>
#[allow(dead_code)]
#[derive(Debug)]
pub(crate) struct ScmNode {
	i: u32,
	i1: u32,
	sh1: u32,
	add: bool,
	i2: u32,
	sh2: u32,
}

pub fn main() {
	println!("cargo:rerun-if-changed=res/scm.tar.gz");
	println!("cargo:rerun-if-changed=res/ecm.tar.gz");
	println!("cargo:rerun-if-changed=build.rs");

	let scm = scm().unwrap();

	let scm_node_def = r"use crate::Coeff;
#[derive(Debug, Clone)]
pub(crate) struct ScmNode {
pub(crate) i: usize,
pub(crate) i1: usize,
pub(crate) sh1: u32,
pub(crate) add: bool,
pub(crate) i2: usize,
pub(crate) sh2: u32,
}";
	// TODO make HashMap (but this is not easy using static/const)
	let o = format!(
		"{scm_node_def}
        pub(crate) static SCM: [(u32, Coeff, &[ScmNode]); {}] = [\n{}\n];",
		scm.len(),
		scm.iter()
			.map(|(x, c, scm)| format!("\t({}, {}, &{:?})", x, c, scm))
			.join(",\n")
	);
	fs::write("./src/int/res/scm_db.rs", o).unwrap();

	let db = Path::new("./res/ecm.tar.gz");
	assert!(db.exists());

	Archive::new(GzDecoder::new(fs::File::open(db).unwrap()))
		.unpack("./res/")
		.unwrap();
}
