use std::{
	fs::{self},
	path::Path,
};

use flate2::read::GzDecoder;
use itertools::Itertools;
use pindakaas::ScmNode;
use quote::quote;
use tar::Archive;
use tqdm::Iter;

const LIMIT: usize = 3;

// pub type ScmNodeKey = (usize, Coeff); // bits, multiplier
// #[derive(Debug, Clone)]
// pub struct ScmNode {
// 	pub i: usize,
// 	pub i1: usize,
// 	pub sh1: u32,
// 	pub add: bool,
// 	pub i2: usize,
// 	pub sh2: u32,
// }

fn scm() -> Result<String, std::io::Error> {
	// if Path::new("res/scm").exists() {
	// 	fs::remove_dir_all(env::cr "res/scm")?;
	// 	fs::create_dir("res/scm")?;
	// } else {
	// 	fs::create_dir("res/scm")?;
	// }

	let db = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/res/scm.tar.gz"));
	assert!(db.exists());

	fn to_key(path: &Path) -> String {
		path.file_stem().unwrap().to_str().unwrap().to_string()
	}

	Archive::new(GzDecoder::new(fs::File::open(db)?))
		.unpack("res/")
		.unwrap();

	let (scm_keys, scm_values): (Vec<_>, Vec<_>) = fs::read_dir("res/scm")?
		.map(|f| f.unwrap().path())
		.sorted()
		.take(LIMIT)
		.map(|path| {
			println!("Compiling {}", path.display());
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
				.map(
					|ScmNode {
					     i,
					     i1,
					     sh1,
					     add,
					     i2,
					     sh2,
					 }| {
						quote! {
							ScmNode {
								i: #i,
								i1: #i1,
																sh1: #sh1,
																add: #add,
																i2: #i2,
																sh2: #sh2,
							}
						}
					},
				)
				.collect_vec();

			let key = to_key(&path);
			(quote! { #key }, quote! { &[#(#scm),*] })
		})
		.unzip();

	let p = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/res/ecm.tar.gz"));
	Archive::new(GzDecoder::new(fs::File::open(p).unwrap()))
		.unpack("res/")
		.unwrap();
	let (ecm_keys, ecm_values): (Vec<_>, Vec<_>) = fs::read_dir("res/ecm")?
		.map(|f| f.unwrap().path())
		.sorted()
		.take(LIMIT)
		.tqdm()
		.map(|path| {
			let (lits, sizes): (Vec<_>, Vec<_>) = pindakaas::Cnf::from_file(&path)
				.unwrap()
				.iter()
				.map(|clause| {
					let clause = clause
						.iter()
						.map(|l| i32::from(*l))
						.map(|l| quote! { crate::lit!(#l) })
						.collect_vec();
					let size = clause.len();
					(quote! { #(#clause),* }, size)
				})
				.unzip();
			(
				to_key(&path),
				quote! { crate::ConstCnf {lits: &[#(#lits),*], sizes: &[#(#sizes),*]} },
			)
		})
		.map(|(key, dimacs)| (quote! { #key }, dimacs))
		.unzip();

	Ok(quote! {
	pub(crate) static SCM: ScmDB = ScmDB {
			scm: phf::phf_map! {
					#( #scm_keys => #scm_values ),*
				},
							 ecm: phf::phf_map! {

					#( #ecm_keys => #ecm_values ),*

							 }

		};
		}
	.to_string())
}

pub fn main() {
	let scm = scm().unwrap();
	fs::write(
		concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/../pindakaas/src/gen/scm_db.rs"
		),
		prettyplease::unparse(
			&syn::parse_file(&scm)
				.unwrap_or_else(|e| panic!("Failed to format {scm} with err: {e}")),
		),
	)
	.unwrap();
}

#[cfg(test)]
mod tests {
	use crate::main;

	#[test]
	fn hello() {
		main();
	}
}
