use std::{fs, path::Path};

use flate2::read::GzDecoder;
use itertools::Itertools;
use pindakaas::{Cnf, ScmNode, ScmNodeKey};
use quote::quote;
use tar::Archive;

// const LIMIT: usize = 5;

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

	Archive::new(GzDecoder::new(fs::File::open(db)?))
		.unpack("res/")
		.unwrap();

	let (keys, values): (Vec<_>, Vec<_>) = fs::read_dir("res/scm")?
		.map(|f| f.unwrap().path())
		.collect_vec()
		.into_iter()
		.sorted()
		// .take(LIMIT)
		.map(|path| {
			let scm = fs::read_to_string(&path)
				.unwrap()
				.lines()
				.filter(|line| !(line.is_empty() || line.starts_with('#')))
				// .map(|line| match line.split(',').collect::<Vec<_>>()[..] {
				// 	[i, i1, sh1, add, i2, sh2] => quote! {
				// 							ScmNode {
				// 		i: quote!{#i},
				// 		i1: #i1,
				// 		sh1: #sh1,
				// 								add: true,
				// 		// add: match add {
				// 		// 	"+" => true,
				// 		// 	"-" => false,
				// 		// 	_ => unreachable!(),
				// 		// },
				// 		i2: #i2,
				// 		sh2: #sh2,
				// 	} },
				// 	_ => panic!("Unexpected line {line}"),
				// })
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

			// let key: ScmNodeKey = path
			// 	.file_stem()
			// 	.unwrap()
			// 	.to_str()
			// 	.unwrap()
			// 	.split('_')
			// 	.collect::<Vec<_>>()
			// 	.into_iter()
			// 	.collect_tuple()
			// 	.map(|(bits, v)| (bits.parse().unwrap(), v.parse().unwrap()))
			// 	.unwrap();
			// let (bits, v) = key;

			let key = path.file_stem().unwrap().to_str().unwrap();

			// (quote! { (#bits, #v)}, quote! { [#(#scm),*] })
			(quote! { #key }, quote! { &[#(#scm),*] })
		})
		.unzip();

	// let p = Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/res/ecm.tar.gz"));
	// Archive::new(GzDecoder::new(fs::File::open(p).unwrap()))
	// 	.unpack("res/")
	// 	.unwrap();
	// fs::read_dir("res/ecm")?
	// 	.map(|f| f.unwrap().path())
	// 	.collect_vec()
	// 	.into_iter()
	// 	.sorted()
	// 	.take(LIMIT)
	// 	.map(|path| {
	// 		let key = f?.path();
	// 		Ok((quote! { #key }, Cnf::from_file(&p)?))
	// 	})
	// 	.try_collect();

	Ok(quote! {
							 use crate::{ScmNode,ScmDB};
													 use ::phf::phf_map;
	pub(crate) static SCM: ScmDB = ScmDB(
			phf_map! {
					#( #keys => #values ),*
				});
		}
	.to_string())
}

pub fn main() {
	let scm = scm().unwrap();
	fs::write(
		concat!(
			env!("CARGO_MANIFEST_DIR"),
			"/../pindakaas/src/integer/scm_db.rs" //"/src/db.rs"
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
