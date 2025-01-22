use std::{
	fs::{self},
	io::{BufRead, BufReader, Read},
	path::Path,
};

use flate2::read::GzDecoder;
use itertools::Itertools;
use quote::quote;
use tar::Archive;

pub fn generate(limit: Option<usize>, format: bool) -> Result<String, std::io::Error> {
	let db = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/res/scm.tar.gz"));
	assert!(db.exists());

	fn to_key(path: &Path) -> String {
		path.file_stem().unwrap().to_str().unwrap().to_string()
	}

	let (scm_keys, scm_values): (Vec<_>, Vec<_>) =
		Archive::new(GzDecoder::new(fs::File::open(db)?))
			.entries()
			.into_iter()
			.flatten()
			.skip(1)
			.map(|entry| {
				let entry = entry.unwrap();
				(entry.path().unwrap().to_path_buf(), entry)
			})
			.filter(|(p, _)| {
				if let Some(limit) = limit {
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
			.map(|(path, entry)| {
				let scm = BufReader::new(entry)
					.lines()
					.map(|l| l.unwrap())
					.filter(|line| !(line.is_empty() || line.starts_with('#')))
					.map(|line| match line.split(',').collect::<Vec<_>>()[..] {
						// TODO how to not output the suffix?
						[i, i1, sh1, add, i2, sh2] => (
							i.parse::<usize>().unwrap(),
							i1.parse::<usize>().unwrap(),
							sh1.parse::<u32>().unwrap(),
							match add {
								"+" => true,
								"-" => false,
								_ => unreachable!(),
							},
							i2.parse::<usize>().unwrap(),
							sh2.parse::<u32>().unwrap(),
						),
						_ => panic!("Unexpected line {line}"),
					})
					.map(|(i, i1, sh1, add, i2, sh2)| {
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
					})
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
	.filter(|(p, _)| {
		if let Some(limit) = limit {
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
	.map(|(path, mut entry)| {
		let mut s = String::new();
		_ = entry.read_to_string(&mut s);
		(to_key(&path), quote! {#s})
	})
	.map(|(key, dimacs)| (quote! { #key }, dimacs))
	.unzip();

	let scm = quote! {
	pub(crate) static SCM: ScmDB = ScmDB {
			scm: phf::phf_map! {
					#( #scm_keys => #scm_values ),*
				},
							 ecm: phf::phf_map! {

					#( #ecm_keys => #ecm_values ),*

							 }

		};
		}
	.to_string();

	Ok(if format {
		prettyplease::unparse(
			&syn::parse_file(&scm)
				.unwrap_or_else(|e| panic!("Failed to format {scm} with err: {e}")),
		)
	} else {
		scm
	})
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn test_generate() {
		let out = generate(Some(2), true).unwrap();
		println!("{out}");
	}
}
