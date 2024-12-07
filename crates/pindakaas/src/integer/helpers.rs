use crate::integer::enc::IntVarEnc;
use crate::integer::Lin;
use crate::integer::LinExp;
use crate::integer::Model;
use crate::integer::Term;
use std::{
	fs::File,
	io::{BufReader, Read},
	path::PathBuf,
};

use bzip2::read::BzDecoder;
use flate2::bufread::GzDecoder;
use itertools::Itertools;

use crate::{bool_linear::Comparator, integer::Dom, Coeff, Lit};

#[derive(Debug)]
pub enum Format {
	Lp,
	Opb,
}

/// Number of required bits for unsigned Binary encoding with range 0..(ub-lb)
pub(crate) fn required_lits(dom: &Dom) -> usize {
	let cardinality = dom.ub() - dom.lb();
	if cardinality == 0 {
		0
	} else {
		(cardinality.ilog2() + 1) as usize
	}
}

impl Model {
	pub fn to_text(&self, format: Format) -> String {
		match format {
			Format::Lp => {
				format!(
					"Subject To
{}
Bounds
{}
End
",
					self.cons
						.iter()
						.map(|con| format!(
							"\t{}: {} {} {}",
							con.lbl,
							con.exp
								.terms
								.iter()
								.map(|term| format!(
									"{} {} {}",
									if term.c.is_positive() { "+" } else { "-" },
									term.c.abs(),
									term.x.borrow().lbl
								))
								.join(" "),
							match con.cmp {
								Comparator::LessEq => "<=",
								Comparator::Equal => "=",
								Comparator::GreaterEq => ">=",
							},
							con.k
						))
						.join("\n"),
					self.vars()
						.sorted_by_key(|x| x.borrow().id)
						.map(|x| {
							let x = x.borrow();
							format!("  {} <= {} <= {}", x.lb(), x.lbl(), x.ub())
						})
						.join("\n")
				)
			}
			Format::Opb => {
				let vars = self.vars().unique_by(|x| x.borrow().id).count();

				format!(
					"* #variable= {} #constraint= {}
{} 
                   ",
					vars,
					self.cons.len(),
					self.cons
						.iter()
						.map(|con| format!(
							"{} {} {}",
							con.exp
								.terms
								.iter()
								.map(|term| format!("{:+} {}", term.c, term.x.borrow().lbl(),))
								.join(" "),
							match con.cmp {
								Comparator::LessEq => "<=",
								Comparator::Equal => "=",
								Comparator::GreaterEq => ">=",
							},
							con.k
						))
						.join(";\n")
				)
			}
		}
	}
	pub fn from_file(path: PathBuf) -> Result<Self, String> {
		let ext = path.extension().unwrap().to_str().unwrap();
		let file = File::open(path.clone())
			.map_err(|e| format!("File::open({}) failed: {e}", path.display()))
			.unwrap();
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

		Model::from_string(&s, format)
	}

	/// Superset of LP format:
	/// allow anonymous constraints (w/o label) by `: ...` (they will be internally labelled still)
	/// allow Doms section for domain with gaps
	/// variables without domains default to 01
	pub fn from_string(s: &str, format: Format) -> Result<Self, String> {
		#[derive(PartialEq)]
		enum State {
			SubjectTo,
			Binary,
			Bounds,
			Doms,
			Minimize,
			Maximize,
			Encs,
		}

		let mut state = State::SubjectTo;
		let mut cmp: Option<Comparator> = None;
		let mut c: Option<Coeff> = None;
		let mut is_positive = true;

		let mut model = Model::default();

		let set_dom = |model: &mut Model, name: &str, dom: Dom| {
			if let Some(x) = model.var_by_lbl(name) {
				x.borrow_mut().dom = dom;
			} else {
				println!("Trying to set domain for unconstrained variable {}", name);
			}
		};

		for line in s.lines() {
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
							// match state {
							// 	State::Minimize => {
							// 		obj = ParseObj::Minimize(con);
							// 	}
							// 	State::Maximize => {
							// 		obj = ParseObj::Maximize(con);
							// 	}
							// 	_ => {
							// 		obj = ParseObj::Satisfy;
							// 	}
							// }
							cmp = None;
							// k = None;
							// con = (vec![], vec![]);
							// is_positive = true;
							state = State::SubjectTo;
							// lbl = None;
						}
						["binary" | "binaries" | "bin"] => {
							state = State::Binary;
						}
						["bounds"] => {
							state = State::Bounds;
						}
						["doms"] => {
							state = State::Doms;
						}
						["encs"] => {
							state = State::Encs;
						}
						["generals" | "general" | "gen" | "semi-continuous" | "semis" | "semi"] => {
							return Err(String::from(
								"Generals/semi-continuous sections not supported",
							));
						}
						["minimize" | "minimum" | "min"] => state = State::Minimize,
						["maximize" | "maximum" | "max"] => state = State::Maximize,
						[name, "=", val] if state == State::Bounds => {
							set_dom(&mut model, name, Dom::constant(val.parse().unwrap()));
						}
						[name, "in", dom] if state == State::Doms => {
							set_dom(
								&mut model,
								name,
								Dom::new(dom.split(',').map(|c| {
									c.parse::<Coeff>()
										.unwrap_or_else(|_| panic!("Could not parse dom value {c}"))
								})),
							);
						}
						[lb, "<=", name, "<=", ub] if state == State::Bounds => {
							set_dom(
								&mut model,
								name,
								Dom::from_bounds(lb.parse().unwrap(), ub.parse().unwrap()),
							);
						}
						[name, ">=", lb] if state == State::Bounds => {
							return Err(format!(
								"Unsupported single bound setting for {name}>={lb}"
							));
						}
						xs if state == State::Binary => {
							xs.iter().for_each(|name| {
								set_dom(&mut model, name, Dom::pb());
							});
						}

						[name, enc, ..] if state == State::Encs => {
							let enc = match *enc {
								"b" => IntVarEnc::Bin(None),
								"o" => IntVarEnc::Ord(None),
								e => panic!("Unknown encoding spec {e}"),
							};
							model.var_by_lbl(name).unwrap().borrow_mut().e = Some(enc);
							if line.chars().nth(2) == Some('!') {
								model.var_by_lbl(name).unwrap().borrow_mut().add_consistency =
									false;
							}
						}
						_ if matches!(state, State::Minimize | State::Maximize) => todo!(),
						line if matches!(state, State::SubjectTo) => {
							for token in line {
								match *token {
									"->" => {
										return Err("Indicator variables not supported".to_owned());
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
											model
												.add_constraint(Lin {
													exp: LinExp { terms: vec![] },
													cmp: Comparator::LessEq,
													k: 0,
													lbl: if next_lbl.is_empty() {
														format!("c_{}", model.cons.len() + 1)
													} else {
														next_lbl.to_owned()
													},
												})
												.unwrap();
										} else if token.chars().next().unwrap().is_alphabetic()
											|| token.starts_with('_')
										{
											let x = model.var_by_lbl(token).unwrap_or_else(|| {
												model
													.new_aux_var(
														Dom::pb(),
														true,
														None,
														token.to_owned(),
													)
													.unwrap()
											});

											// con.1.push(if is_positive { 1 } else { -1 });
											model.cons.last_mut().unwrap().exp.terms.push(
												Term::new(
													c.unwrap_or(if is_positive { 1 } else { -1 }),
													x,
												),
											);
											c = None;
										} else {
											let coef = token.parse::<Coeff>().map_err(|_| {
												format!("Failed parsing to integer on {token}")
											})?;
											if cmp.is_some() {
												model.cons.last_mut().unwrap().cmp = cmp.unwrap();
												cmp = None;
												model.cons.last_mut().unwrap().k = coef;
											} else {
												c = Some(if is_positive { coef } else { -coef });
												is_positive = true;
											}
										}
									}
								}
							}

							// // push last constraint/obj if exists
							// if let (Some(curr_cmp), Some(curr_k)) = (cmp, k) {
							// 	cons.push((con, curr_cmp, curr_k, Some(lbl.unwrap().to_owned())));
							// 	lbl = None;
							// 	cmp = None;
							// 	k = None;
							// 	con = (vec![], vec![]);
							// 	is_positive = true;
							// }
						}
						err => {
							return Err(err.join(" "));
						}
					}
				}
				Format::Opb => {
					let mut cmp = None;
					let mut c = None;

					if line.starts_with('*') {
						continue;
					}

					model
						.add_constraint(Lin {
							exp: LinExp { terms: vec![] },
							cmp: Comparator::LessEq,
							k: 0,
							lbl: format!("c_{}", model.cons.len()),
						})
						.unwrap(); // assuming one line per constraint
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
											let x = model.var_by_lbl(token).unwrap_or_else(|| {
												model
													.new_aux_var(
														Dom::pb(),
														true,
														None,
														token.to_owned(),
													)
													.unwrap()
											});
											model
												.cons
												.last_mut()
												.unwrap()
												.exp
												.terms
												.push(Term::new(c.unwrap(), x));
											c = None;
										} else {
											let coef = token.parse::<Coeff>().map_err(|_| {
												format!("Failed parsing to integer on {token}")
											})?;
											if let Some(cmp) = cmp {
												model.cons.last_mut().unwrap().cmp = cmp;
												model.cons.last_mut().unwrap().k = coef;
											} else {
												c = Some(if is_positive { coef } else { -coef });
												is_positive = true;
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
		Ok(model)
	}
}

pub(crate) fn display_cnf(cnf: &[Vec<Lit>]) -> String {
	cnf.iter()
		.map(|c| c.iter().join(", "))
		.join("\n")
		.to_owned()
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::Cnf;

	#[test]
	fn test_from_opb() {
		let mut model = Model::from_string(
			"* comment
+2 x1 +3 x2 +5 x3 <= 6 ;
",
			Format::Opb,
		)
		.unwrap();
		let mut cnf = Cnf::default();
		model.encode_internal(&mut cnf, true).unwrap();
	}

	#[test]
	fn test_from_lp() {
		let lp = r"
\ comment
Subject To
  c1: - x + 3 y + 5 z <= 10
  c2: 3 x + 5 y >= 5
Binary
  x
Doms
  y in 0,2
Bounds
  0 <= z <= 3
Encs
  x O
  y b
  z b !
End
";
		let model = Model::from_string(lp, Format::Lp).unwrap();
		println!("MODEL = {}", model);
		// model.encode_internal(&mut cnf, true).unwrap();
	}

	// TODO to be used in future with Binary encoding
	fn nearest_power_of_two(k: Coeff, up: bool) -> Coeff {
		// find next power of one if up (or previous if going down)
		if k == 0 {
			0
		} else {
			Coeff::from(1).rotate_right(if up {
				(k - 1).leading_zeros() // rotate one less to get next power of two
			} else {
				k.leading_zeros() + 1 // rotate one more to get previous power of two
			})
		}
	}

	#[test]
	fn test_required_lits() {
		assert_eq!(required_lits(&Dom::from_bounds(0, 6)), 3);
		assert_eq!(required_lits(&Dom::from_bounds(2, 8)), 3);
		assert_eq!(required_lits(&Dom::from_bounds(0, 0)), 0);
		assert_eq!(required_lits(&Dom::from_bounds(0, 0)), 0);
	}

	#[test]
	fn test_nearest_power_of_two() {
		assert_eq!(nearest_power_of_two(0, true), 0);
		assert_eq!(nearest_power_of_two(1, true), 1);
		assert_eq!(nearest_power_of_two(2, true), 2);
		assert_eq!(nearest_power_of_two(3, true), 4);
		assert_eq!(nearest_power_of_two(4, true), 4);
		assert_eq!(nearest_power_of_two(5, true), 8);
		assert_eq!(nearest_power_of_two(6, true), 8);

		assert_eq!(nearest_power_of_two(0, false), 0);
		assert_eq!(nearest_power_of_two(1, false), 1);
		assert_eq!(nearest_power_of_two(2, false), 2);
		assert_eq!(nearest_power_of_two(3, false), 2);
		assert_eq!(nearest_power_of_two(4, false), 4);
		assert_eq!(nearest_power_of_two(5, false), 4);
		assert_eq!(nearest_power_of_two(6, false), 4);
		assert_eq!(nearest_power_of_two(8, false), 8);
		assert_eq!(nearest_power_of_two(9, false), 8);
	}
}
