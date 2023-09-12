use std::{
	collections::HashMap,
	fs::File,
	io::{BufReader, Read},
	path::PathBuf,
	rc::Rc,
};

use bzip2::read::BzDecoder;

use crate::{
	int::model::{LinExp, Obj, Term},
	Coefficient, Comparator, Lin, Literal, Model,
};
use flate2::bufread::GzDecoder;
use itertools::Itertools;

pub enum Format {
	Lp,
	Opb,
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	pub fn from_file(path: PathBuf) -> Result<Self, String> {
		let ext = path.extension().unwrap().to_str().unwrap();
		let file = File::open(path.clone()).unwrap();
		let mut s = String::new();

		if ext == "gz" {
			GzDecoder::new(BufReader::new(file))
				.read_to_string(&mut s)
				.unwrap();
		} else if ext == "bz2" {
			BzDecoder::new(file).read_to_string(&mut s).unwrap();
		} else if ext == "lp" || ext == "opb" {
			BufReader::new(file).read_to_string(&mut s).unwrap();
		} else {
			panic!("Unknown ext {ext}");
		}

		let format = if ext != "opb" && ext != "bz2" {
			Format::Lp
		} else {
			Format::Opb
		};

		Model::from_string(s, format)
	}

	pub fn from_string(s: String, format: Format) -> Result<Self, String> {
		type ParseLinExp<C> = (Vec<String>, Vec<C>);

		#[derive(PartialEq)]
		enum ParseObj<C> {
			Minimize(ParseLinExp<C>),
			Maximize(ParseLinExp<C>),
			Satisfy,
		}

		#[derive(PartialEq)]
		enum State {
			None,
			SubjectTo,
			Binary,
			Bounds,
			Minimize,
			Maximize,
			// Satisfy,
		}

		let mut vars: HashMap<String, (C, C)> = HashMap::new();

		let mut cons: Vec<(ParseLinExp<C>, Comparator, C, Option<String>)> = vec![];

		let set_bounds = |var: &str, lb: &str, ub: &str, vars: &mut HashMap<String, (C, C)>| {
			//let id = var[1..].parse::<usize>().unwrap();
			let bnds = (
				lb.parse::<C>()
					.unwrap_or_else(|_| panic!("Could not parse lb {lb}")),
				ub.parse::<C>()
					.unwrap_or_else(|_| panic!("Could not parse ub {ub}")),
			);
			vars.entry(var.to_string())
				.and_modify(|var| *var = bnds)
				.or_insert(bnds);
		};

		let mut obj = ParseObj::Satisfy;

		let mut state = State::None;

		// (var name as string, coefficient)
		let mut con: ParseLinExp<C> = (vec![], vec![]);

		let mut lbl: Option<String> = None;
		let mut cmp: Option<Comparator> = None;
		let mut k: Option<C> = None;
		let mut is_positive: bool = true;

		for (i, line) in s.lines().enumerate() {
			match format {
				Format::Lp => {
					match line
						.to_lowercase()
						.split_whitespace()
						.collect::<Vec<_>>()
						.as_slice()
					{
						[] | ["*", "\\", ..] => continue,
						line if matches!(line[0].chars().next(), Some('*' | '\\')) => continue,
						["end"] => break,
						["subject", "to"] | ["st" | "s.t."] => {
							match state {
								State::Minimize => {
									obj = ParseObj::Minimize(con);
								}
								State::Maximize => {
									obj = ParseObj::Maximize(con);
								}
								_ => {
									obj = ParseObj::Satisfy;
								}
							}
							cmp = None;
							k = None;
							con = (vec![], vec![]);
							is_positive = true;
							state = State::SubjectTo;
							lbl = None;
						}
						["binary" | "binaries" | "bin"] => {
							state = State::Binary;
						}
						["bounds"] => {
							state = State::Bounds;
						}
						["generals" | "general" | "gen" | "semi-continuous" | "semis" | "semi"] => {
							return Err(String::from(
								"Generals/semi-continuous sections not supported",
							));
						}
						["minimize" | "minimum" | "min"] => state = State::Minimize,
						["maximize" | "maximum" | "max"] => state = State::Maximize,
						[var, "=", val] if state == State::Bounds => {
							set_bounds(var, val, val, &mut vars);
						}
						[lb, "<=", var, "<=", ub] if state == State::Bounds => {
							set_bounds(var, lb, ub, &mut vars);
						}
						[var, ">=", lb] if state == State::Bounds => {
							return Err(format!(
								"Unsupported single bound setting for {var}>={lb}"
							));
						}
						xs if state == State::Binary => {
							xs.iter().for_each(|x| {
								set_bounds(x, "0", "1", &mut vars);
							});
						}
						line if matches!(
							state,
							State::SubjectTo | State::Minimize | State::Maximize
						) =>
						{
							for token in line {
								match *token {
									"->" => {
										return Err(format!(
											"Indicator variables (in cons {lbl:?}) not supported",
										));
									}
									">=" => {
										cmp = Some(Comparator::GreaterEq);
									}
									"<=" => {
										cmp = Some(Comparator::LessEq);
									}
									"=" => {
										cmp = Some(Comparator::Equal);
									}
									"+" => {
										is_positive = true;
									}
									"-" => {
										is_positive = false;
									}
									token => {
										if let Some(next_lbl) = token.strip_suffix(':') {
											lbl = Some(next_lbl.to_string());
										} else if token.chars().next().unwrap().is_alphabetic()
											|| token.starts_with('_')
										{
											let var = token.to_string();
											con.0.push(var);
											// if we didn't see a coefficient, it should be +/- 1
											if con.1.len() == con.0.len() - 1 {
												con.1.push(if is_positive {
													C::one()
												} else {
													-C::one()
												});
												is_positive = true;
											}
										} else {
											let coef = token.parse::<C>().map_err(|_| {
												format!("Failed parsing to integer on {token}")
											})?;
											if cmp.is_some() {
												k = Some(coef);
											} else {
												con.1.push(if is_positive { coef } else { -coef });
												is_positive = true;
											}
										}
									}
								}
							}

							// push last constraint/obj if exists
							if let (Some(curr_cmp), Some(curr_k)) = (cmp, k) {
								cons.push((con, curr_cmp, curr_k, Some(lbl.unwrap().to_string())));
								lbl = None;
								cmp = None;
								k = None;
								con = (vec![], vec![]);
								is_positive = true;
							}

							assert!(
							con.0.len() == con.1.len(),
							"Got unequal number of vars/coefs ({}/{}) with {con:?} for line {line:?}",
							con.0.len(),
							con.1.len()
						);
						}
						err => {
							return Err(err.join(" "));
						}
					}
				}
				Format::Opb => {
					if line.starts_with('*') {
						continue;
					}
					match line
						.to_lowercase()
						.split_whitespace()
						.collect::<Vec<_>>()
						.as_slice()
					{
						[] => continue,
						line => {
							for token in line {
								match *token {
									">=" => {
										cmp = Some(Comparator::GreaterEq);
									}
									"<=" => {
										cmp = Some(Comparator::LessEq);
									}
									"=" => {
										cmp = Some(Comparator::Equal);
									}
									";" => {}
									token => {
										if token.chars().next().unwrap().is_alphabetic()
											|| token.starts_with('x')
										{
											let var = token.to_string();
											set_bounds(&var, "0", "1", &mut vars);
											con.0.push(var);

										// if we didn't see a coefficient, it should be +/- 1
										// if il.1.len() == il.0.len() - 1 {
										//     // il.1.push(if is_positive { 1 } else { -1 });
										//     // il.1.push(if is_positive { 1 } else { -1 });
										//     // is_positive = true;
										// }
										} else {
											// let is_positive = token.starts_with('+');
											let coef = token.parse::<C>().map_err(|_| {
												format!("Failed parsing to integer on {token}")
											})?;
											if cmp.is_some() {
												k = Some(coef);
											} else {
												// il.1.push(if is_positive { coef } else { -coef });
												con.1.push(coef);
											}
										}
									}
								}
							}

							cons.push((
								con,
								cmp.unwrap(),
								k.unwrap(),
								Some(lbl.unwrap_or_else(|| i.to_string()).to_string()),
							));
							con = (vec![], vec![]);
							lbl = None;
							cmp = None;
							k = None;
						}
					}
				}
			}
		}

		let mut model = Model::default();

		let vars = vars
			.into_iter()
			.sorted()
			.map(|(lp_id, (lb, ub))| {
				let dom = num::iter::range_inclusive(lb, ub).collect::<Vec<_>>();
				(lp_id, model.new_var(&dom, true))
			})
			.collect::<HashMap<_, _>>();

		let to_ilp_exp = |(int_vars, coefs): &ParseLinExp<C>| LinExp {
			terms: coefs
				.iter()
				.zip(int_vars.iter().flat_map(|lp_id| {
					vars.get(lp_id)
						.ok_or(format!("Unbounded variable {lp_id}"))
						.map(Rc::clone)
				}))
				.map(|(c, x)| Term::new(*c, x))
				.collect(),
		};

		for (lin, cmp, k, lbl) in cons {
			model
				.add_constraint(Lin {
					exp: to_ilp_exp(&lin),
					cmp,
					k,
					// lbl,
				})
				.map_err(|_| {
					format!(
						"LP was trivially unsatisfiable fo rconstraint {:?}: {:?}",
						lbl, lin,
					)
				})?;
		}

		let obj = match obj {
			ParseObj::Maximize(lin) => Obj::Maximize(to_ilp_exp(&lin)),
			ParseObj::Minimize(lin) => Obj::Minimize(to_ilp_exp(&lin)),
			ParseObj::Satisfy => Obj::Satisfy,
		};

		model.obj = match obj {
			Obj::Minimize(lin) | Obj::Maximize(lin)
				if {
					lin.terms.iter().all(|term| term.c == C::zero())
						|| lin
							.terms
							.iter()
							.all(|term| term.x.borrow().dom().count() == 1)
				} =>
			{
				Obj::Satisfy
			}
			_ => obj,
		};

		Ok(model)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{Cnf, Model};

	#[test]
	fn test_from_opb() {
		let mut model = Model::<i32, i32>::from_string(
			String::from(
				"
* comment
+1 x1 +2 x2 +2 x3 +3 x4 = 2 ;
+1 x1 +1 x2 +2 x3 <= 2 ;
+1 x3 +1 x4 +3 x2 <= 3 ;
",
			),
			Format::Opb,
		)
		.unwrap();
		let mut cnf = Cnf::new(0);
		model.encode(&mut cnf, None).unwrap();
	}

	#[test]
	fn test_from_lp() {
		let mut model = Model::<i32, i32>::from_string(
			String::from(
				"
Maximize
  x + y + z
Subject To
  c1: 2 x + 3 y + 5 z <= 6
Binary
  x
  y
  z
End
",
				// 2 * x {0,1,2} + 3 * x2 { 0,1} .. <= 6
				//  x {0,2,4} + x2 { 0,3} .. <= 6
				// x {0,2,4 } + y1 { .. } <= y2 ...
			),
			Format::Lp,
		)
		.unwrap();

		// c0: x + y = 1
		let mut cnf = Cnf::new(0);
		println!("model = {model}");

		model.encode(&mut cnf, None).unwrap();
	}
}
