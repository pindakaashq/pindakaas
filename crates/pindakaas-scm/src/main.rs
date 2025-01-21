use std::{
	fs::{self},
	io::{BufRead, BufReader, Read},
	path::Path,
};

use flate2::read::GzDecoder;
use itertools::Itertools;
use pindakaas::ScmNode;
use quote::quote;
use tar::Archive;
use tqdm::Iter;

const LIMIT: Option<usize> = None;
const FORMAT: bool = true;

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

	// TODO stream i/o unpack

	let (scm_keys, scm_values): (Vec<_>, Vec<_>) =
		Archive::new(GzDecoder::new(fs::File::open(db)?))
			.entries()
			.into_iter()
			.flatten()
			.skip(1)
			// .take(LIMIT)
			.map(|entry| {
				let mut entry = entry.unwrap();
				let path = entry.path().unwrap().to_path_buf();
				println!("Compiling {path:?}");
				let scm = BufReader::new(entry)
					.lines()
					.map(|l| l.unwrap())
					.filter(|line| !(line.is_empty() || line.starts_with('#')))
					.map(|line| match line.split(',').collect::<Vec<_>>()[..] {
						// TODO rewrite without using scmnode
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

	let (ecm_keys, ecm_values): (Vec<_>, Vec<_>) = Archive::new(GzDecoder::new(fs::File::open(
		Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/res/ecm.tar.gz")),
	)?))
	.entries()
	.into_iter()
	.flatten()
	.map(|entry| {
		let entry = entry.unwrap();
		(entry.path().unwrap().to_path_buf(), entry)
	})
	.skip(1)
	// .take(LIMIT)
	.filter(|(p, _)| {
		if let Some(limit) = LIMIT {
			p.file_stem()
				.unwrap()
				.to_str()
				.unwrap()
				.split("_")
				.nth(1)
				.unwrap()
				.parse::<usize>()
				.unwrap() < limit
		} else {
			true
		}
	})
	.tqdm()
	.map(|(path, mut entry)| {
		let mut s = String::new();
		_ = entry.read_to_string(&mut s);
		(to_key(&path), quote! {#s})
	})
	.map(|(key, dimacs)| (quote! { #key }, dimacs))
	.unzip();

	Ok(quote! {
			use std::num::NonZeroI32;
	pub(crate) static SCM: ScmDB = unsafe { ScmDB {
			scm: phf::phf_map! {
					#( #scm_keys => #scm_values ),*
				},
							 ecm: phf::phf_map! {

					#( #ecm_keys => #ecm_values ),*

							 }

		}};
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
		if FORMAT {
			prettyplease::unparse(
				&syn::parse_file(&scm)
					.unwrap_or_else(|e| panic!("Failed to format {scm} with err: {e}")),
			)
		} else {
			scm
		},
	)
	.unwrap();
}

// #[cfg(test)]
// mod tests {
// 	use crate::main;
// 	#[test]
// 	fn hello() {
// 		main();
// 	}
// }
