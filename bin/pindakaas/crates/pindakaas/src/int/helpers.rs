use std::{
	collections::HashMap,
	fs::File,
	io::{BufReader, Read},
	path::PathBuf,
	rc::Rc,
};

use bzip2::read::BzDecoder;

use crate::{
	int::enc::GROUND_BINARY_AT_LB,
	int::model::{LinExp, Obj, Term},
	Coefficient, Comparator, Lin, Literal, Model,
};
use flate2::bufread::GzDecoder;
use itertools::Itertools;

pub enum Format {
	Lp,
	Opb,
}

/// Number of required (non-fixed) lits for IntVarBin
pub(crate) fn required_lits<C: Coefficient>(lb: C, ub: C) -> usize {
	(if GROUND_BINARY_AT_LB {
		C::zero().leading_zeros() - ((ub - lb).leading_zeros())
	} else if !lb.is_negative() {
		C::zero().leading_zeros() - ub.leading_zeros()
	} else {
		let lb_two_comp = -(lb + C::one());
		std::cmp::max(
			C::zero().leading_zeros() - lb_two_comp.leading_zeros() + 1,
			C::zero().leading_zeros() - ub.leading_zeros() + 1,
		)
	}) as usize
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	pub fn to_text(&self, format: Format) -> String {
		match format {
			Format::Lp => {
				// let mut output = String::new();
				format!(
					"Subject To
{}
Bounds
{}
End
",
					self.cons
						.iter()
						.enumerate()
						.map(|(i, con)| format!(
							"  {}: {} {} {}",
							con.lbl.clone().unwrap_or_else(|| format!("c{}", i)),
							con.exp
								.terms
								.iter()
								.map(|term| format!(
									"{} {} {}",
									if term.c.is_positive() { "+" } else { "-" },
									term.c.abs(),
									term.x.borrow().lbl()
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
						.into_iter()
						.sorted_by_key(|x| x.borrow().lbl())
						.map(|x| {
							let x = x.borrow();
							format!("  {} <= {} <= {}", x.lb(), x.lbl(), x.ub())
						})
						.join("\n")
				)
			}
			Format::Opb => {
				println!("Write OPB");

				// let mut output = File::create(path)?;

				// use std::io::Write;
				//let pbs = self.pbs.iter().map(|pb| pb.into::<())
				let vars = self.vars().iter().unique_by(|x| x.borrow().id).count();

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
			Doms,
			Minimize,
			Maximize,
			// Satisfy,
		}

		let mut vars: HashMap<String, Vec<C>> = HashMap::new();

		let mut cons: Vec<(ParseLinExp<C>, Comparator, C, Option<String>)> = vec![];

		let set_doms = |var: &str, dom: &[C], vars: &mut HashMap<String, Vec<C>>| {
			//let id = var[1..].parse::<usize>().unwrap();
			let dom = dom.to_vec();
			vars.entry(var.to_string())
				.and_modify(|var| *var = dom.clone())
				.or_insert(dom);
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
						["doms"] => {
							state = State::Doms;
						}
						["generals" | "general" | "gen" | "semi-continuous" | "semis" | "semi"] => {
							return Err(String::from(
								"Generals/semi-continuous sections not supported",
							));
						}
						["minimize" | "minimum" | "min"] => state = State::Minimize,
						["maximize" | "maximum" | "max"] => state = State::Maximize,
						[var, "=", val] if state == State::Bounds => {
							set_doms(
								var,
								&[val
									.parse::<C>()
									.unwrap_or_else(|_| panic!("Could not = {val}"))],
								&mut vars,
							);
						}
						[var, "in", dom] if state == State::Doms => {
							let dom = dom
								.split(',')
								.map(|c| {
									c.parse::<C>()
										.unwrap_or_else(|_| panic!("Could not parse dom value {c}"))
								})
								.collect::<Vec<_>>();
							set_doms(var, &dom, &mut vars);
						}
						[lb, "<=", var, "<=", ub] if state == State::Bounds => {
							let dom = num::iter::range_inclusive(
								lb.parse::<C>()
									.unwrap_or_else(|_| panic!("Could not parse lb {lb}")),
								ub.parse::<C>()
									.unwrap_or_else(|_| panic!("Could not parse ub {ub}")),
							)
							.collect::<Vec<_>>();
							set_doms(var, &dom, &mut vars);
						}
						[var, ">=", lb] if state == State::Bounds => {
							return Err(format!(
								"Unsupported single bound setting for {var}>={lb}"
							));
						}
						xs if state == State::Binary => {
							xs.iter().for_each(|x| {
								set_doms(x, &[C::zero(), C::one()], &mut vars);
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
											set_doms(&var, &[C::zero(), C::one()], &mut vars);
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
			.flat_map(|(lp_id, dom)| {
				model
					.new_var(&dom, true, None, Some(lp_id.clone()))
					.map(|x| (lp_id, x))
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
					lbl: lbl.clone(),
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
							.all(|term| term.x.borrow().dom.size() == C::one())
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
+2 x1 +3 x2 +5 x3 <= 6 ;
",
			),
			Format::Opb,
		)
		.unwrap();
		let mut cnf = Cnf::new(0);
		model.encode(&mut cnf).unwrap();
		println!("opb = {}", model.to_text(Format::Opb));
	}

	#[test]
	fn test_from_lp() {
		let lp = r"
\ comment
Subject To
  c1: 2 x + 3 y + 5 z <= 6
Binary
  x
  y
Bounds
  0 <= z <= 1
End
";
		let mut model = Model::<i32, i32>::from_string(lp.into(), Format::Lp).unwrap();
		let mut cnf = Cnf::new(0);
		println!("model = {model}");

		model.encode(&mut cnf).unwrap();
		println!("lp = {}", model.to_text(Format::Lp));
		// assert_eq!(lp, model.to_text(Format::Lp));
	}
}
