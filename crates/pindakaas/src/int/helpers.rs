use crate::Term;
use std::{
	collections::{hash_map::Entry, HashMap},
	fs::File,
	io::{BufReader, Read},
	path::PathBuf,
	rc::Rc,
};

use bzip2::read::BzDecoder;

use crate::{
	helpers::{as_binary, two_comp_bounds},
	int::model::Obj,
	int::LinExp,
	int::{enc::GROUND_BINARY_AT_LB, IntVarEnc},
	Coefficient, Comparator, Lin, Literal, Model,
};
use flate2::bufread::GzDecoder;
use itertools::Itertools;

use super::LitOrConst;

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
		let lb_two_comp = C::zero().leading_zeros() - lb_two_comp.leading_zeros() + 1;
		if ub.is_negative() {
			lb_two_comp
		} else {
			std::cmp::max(
				lb_two_comp,
				C::zero().leading_zeros() - ub.leading_zeros() + 1,
			)
		}
	}) as usize
}

pub(crate) fn nearest_power_of_two<C: Coefficient>(k: C, up: bool) -> C {
	// find next power of one if up (or previous if going down)
	if k.is_zero() {
		C::zero()
	} else {
		C::one().rotate_right(if up {
			(k - C::one()).leading_zeros() // rotate one less to get next power of two
		} else {
			k.leading_zeros() + 1 // rotate one more to get previous power of two
		})
	}
}

/// Return a linear expression of non-fixed literals and their coefficient, and a constant `add` resulting from the fixed literals
pub(crate) fn filter_fixed<Lit: Literal, C: Coefficient>(
	xs: &[LitOrConst<Lit>],
) -> (Vec<(Lit, C)>, C) {
	let mut add = C::zero(); // resulting from fixed terms

	let offset = two_comp_bounds(xs.len()).0;
	(
		xs.iter()
			.enumerate()
			.filter_map(|(k, x)| match x {
				LitOrConst::Lit(l) => Some((l.clone(), C::one().shl(k))),
				LitOrConst::Const(true) => {
					add += C::one().shl(k);
					None
				}
				LitOrConst::Const(false) => None,
			})
			.collect::<Vec<_>>(),
		add + offset,
	)
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
						.sorted_by_key(|x| x.borrow().id)
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
			Encs,
			// Satisfy,
		}

		let mut vars: HashMap<String, Vec<C>> = HashMap::new();
		let mut encs: HashMap<String, IntVarEnc<Lit, C>> = HashMap::new();

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
						[var, enc] if state == State::Encs => {
							let enc = match *enc {
								"b" => IntVarEnc::Bin(None),
								"o" => IntVarEnc::Ord(None),
								e => panic!("Unknown encoding spec {e}"),
							};
							encs.entry(var.to_string())
								.and_modify(|e| *e = enc.clone())
								.or_insert(enc);
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
								Some(lbl.unwrap_or_else(|| format!("c{}", cons.len()))),
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

		let add_var = |model: &mut Model<Lit, C>, lp_id: &str, dom: &[C]| {
			let lp_id = lp_id.to_string();
			model
				.new_var(dom, true, encs.get(&lp_id).cloned(), Some(lp_id.clone()))
				.map(|x| (lp_id, x))
		};

		let mut vars = vars
			.into_iter()
			.sorted()
			.flat_map(|(lp_id, dom)| add_var(&mut model, &lp_id, &dom))
			.collect::<HashMap<_, _>>();

		const DEFAULT_01: bool = false;
		let mut to_ilp_exp =
			|model: &mut Model<Lit, C>, (int_vars, coefs): &ParseLinExp<C>| LinExp {
				terms: coefs
					.iter()
					.zip(
						int_vars
							.iter()
							.flat_map(|lp_id| match vars.entry(lp_id.clone()) {
								Entry::Occupied(e) => Some(Rc::clone(e.get())),
								Entry::Vacant(e) => {
									if DEFAULT_01 {
										eprintln!("WARNING: unbounded variable's {lp_id} domain set to Binary");
										let x = add_var(model, lp_id, &[C::zero(), C::one()])
											.unwrap()
											.1;
										e.insert(x.clone());
										Some(x)
									} else {
										None
									}
								}
							}),
					)
					.map(|(c, x)| Term::new(*c, x))
					.collect(),
			};

		for (lin, cmp, k, lbl) in cons {
			let con = Lin {
				exp: to_ilp_exp(&mut model, &lin),
				cmp,
				k,
				lbl: lbl.clone(),
			};
			model.add_constraint(con).map_err(|_| {
				format!(
					"LP was trivially unsatisfiable for constraint {:?}: {:?}",
					lbl, lin,
				)
			})?;
		}

		let obj = match obj {
			ParseObj::Maximize(lin) => Obj::Maximize(to_ilp_exp(&mut model, &lin)),
			ParseObj::Minimize(lin) => Obj::Minimize(to_ilp_exp(&mut model, &lin)),
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

pub(crate) fn to_lex_bits<C: Coefficient>(k: C, bits: usize, two_comp: bool) -> Vec<bool> {
	// first, get k represented as 2-comp in the min. number of bits
	// assert!(bits >= required_lits(k, k));
	let ks = if !k.is_negative() {
		// 2-comp for non-negative x = unsigned(x) ++ [false sign bit]
		as_binary(k.into(), None)
			.into_iter()
			.chain([false]) // sign bit
			.collect()
	} else {
		// 2-comp for negative x = negate(unsigned(|x|) ) + one
		// Ex. negate(unsigned(|-2|)) + one = negate(0+10) + one = 101 + one = 110 = -4+2+0 = -2
		as_binary((k.abs() - C::one()).into(), None)
			.into_iter()
			.chain([false])
			.map(|b| !b)
			.collect::<Vec<_>>()
	};
	let ks = ks[..ks.len() - 1]
		.iter()
		.copied()
		// First, sign-extend to get the required number of bits
		.chain(vec![*ks.last().unwrap(); bits.saturating_sub(ks.len())])
		// and add/negate just the last bit to get two-comp/lexicographic binary
		.chain([{
			let last = *ks.last().unwrap();
			if two_comp {
				last
			} else {
				!last
			}
		}])
		.collect::<Vec<_>>();

	// debug_assert_eq!(
	// 	filter_fixed::<i32, C>(
	// 		&ks.iter()
	// 			.cloned()
	// 			.map(|b| LitOrConst::from(b))
	// 			.collect_vec()
	// 	)
	// 	.1,
	// 	k,
	// 	"Computed lex-binary {ks:?} is not equivalent to {k}"
	// );

	ks
}

pub(crate) fn sign_extend<Lit: Literal>(
	ks: &[LitOrConst<Lit>],
	s: LitOrConst<Lit>,
	n: usize,
) -> Vec<LitOrConst<Lit>> {
	ks[..ks.len() - 1]
		.iter()
		.cloned()
		.chain(vec![s; n.saturating_sub(ks.len())])
		.chain([ks.last().unwrap().clone()])
		.collect()
}

pub(crate) fn display_cnf<Lit: Literal>(cnf: &[Vec<Lit>]) -> String {
	cnf.iter()
		.map(|c| c.iter().join(", "))
		.join("\n")
		.to_string()
}

// pub(crate) fn filter_cnf<Lit: Literal>(cnf: &[Vec<Lit>], given: &Vec<Vec<Lit>>) -> Vec<Vec<Lit>> {
// 	if given.is_empty() {
// 		cnf
// 	} else {
// 		cnf.into_iter()
// 			.filter(|clause| {
// 				// remove clause
// 				!given // if not redundant; if any given clause
// 					.iter()
// 					.any(|given_clause| is_clause_redundant(given_clause, clause))
// 			})
// 			.collect()
// 	}
// }

/// is clause a subset of b
pub(crate) fn is_clause_redundant<Lit: Literal>(a: &[Lit], b: &[Lit]) -> bool {
	a.iter().all(|l| b.contains(l))
}

pub(crate) fn remove_red<Lit: Literal>(cnf: Vec<Vec<Lit>>) -> Vec<Vec<Lit>> {
	const REMOVE_RED: bool = true;
	if REMOVE_RED {
		let mut last: Option<Vec<Lit>> = None;
		cnf.into_iter()
			.flat_map(|clause| match last.as_ref() {
				Some(last) if is_clause_redundant(last, &clause) => None,
				_ => {
					last = Some(clause.clone());
					Some(clause)
				}
			})
			.collect()
	} else {
		cnf
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
		model.encode(&mut cnf, true).unwrap();
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
Doms
  y in 0,1
Bounds
  0 <= z <= 1
Encs
  x O
End
";
		let mut model = Model::<i32, i32>::from_string(lp.into(), Format::Lp).unwrap();
		let mut cnf = Cnf::new(0);
		println!("model = {model}");

		model.encode(&mut cnf, true).unwrap();
		println!("lp = {}", model.to_text(Format::Lp));
		// assert_eq!(lp, model.to_text(Format::Lp));
	}

	#[test]
	fn test_to_bits() {
		assert_eq!(to_lex_bits(-3, 3, false), &[true, false, false]);
		assert_eq!(to_lex_bits(-4, 3, false), &[false, false, false]);
		assert_eq!(to_lex_bits(1, 2, true), &[true, false]);
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

	// #[test]
	// fn test_filter_cnf() {
	// 	// assert_eq!(
	// 	// 	filter_cnf(vec![vec![4, 6]], &vec![vec![2, 3, 5]]),
	// 	// 	vec![vec![4, 6]]
	// 	// );

	// 	// assert_eq!(
	// 	// 	filter_cnf(vec![vec![4, 5]], &vec![vec![1, 4, 5]]),
	// 	// Vec::<Vec<_>>::new()
	// 	// );

	// 	// a \/ b \/ c <= a \/ b
	// 	assert_eq!(
	// 		filter_cnf(vec![vec![1, 2, 3]], &vec![vec![1, 2], vec![4]]),
	// 		Vec::<Vec<_>>::new()
	// 	);
	// }
}
