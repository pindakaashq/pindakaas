// use crate::int::res::SCM;
use crate::int::res::SCM;
use crate::{
	helpers::as_binary,
	int::{
		model::{USE_CHANNEL, USE_CSE},
		Cse, LitOrConst,
	},
	Coefficient, Comparator, IntLinExp as LinExp, IntVar, IntVarRef, Lin, Literal, Model, Scm,
};
use itertools::Itertools;
use std::{collections::HashMap, ops::Mul};

use super::{bin::BinEnc, Dom, IntVarEnc};

#[derive(Debug, Clone)]
pub struct Term<Lit: Literal, C: Coefficient> {
	pub c: C,
	pub x: IntVarRef<Lit, C>,
}

impl<Lit: Literal, C: Coefficient> Mul<C> for Term<Lit, C> {
	type Output = Self;
	fn mul(self, rhs: C) -> Self {
		Self {
			x: self.x,
			c: self.c * rhs,
		}
	}
}

impl<Lit: Literal, C: Coefficient> From<IntVarRef<Lit, C>> for Term<Lit, C> {
	fn from(value: IntVarRef<Lit, C>) -> Self {
		Term::new(C::one(), value)
	}
}

impl<Lit: Literal, C: Coefficient> TryInto<IntVarRef<Lit, C>> for Term<Lit, C> {
	type Error = ();

	fn try_into(self) -> Result<IntVarRef<Lit, C>, Self::Error> {
		self.c.is_one().then_some(self.x).ok_or(())
	}
}

impl<Lit: Literal, C: Coefficient> Term<Lit, C> {
	pub fn new(c: C, x: IntVarRef<Lit, C>) -> Self {
		Self { c, x }
	}

	pub(crate) fn encode_bin(
		self,
		mut model: Option<&mut Model<Lit, C>>,
		cmp: Comparator,
		con_lbl: Option<String>,
	) -> crate::Result<Self> {
		if USE_CSE {
			if let Some(model) = &model {
				// println!("CSE: {}", model.cse);
				if let Some(t) = model.cse.0.get(&(self.x.borrow().id, self.c, cmp)) {
					println!("HIT: ({self}) -> {t}");
					return Ok(t.clone());
				}
			}
		}

		// TODO refactor
		// let cse = match model
		// 	.cse
		// 	.entry((self.x.borrow().id, self.c))
		// {
		// 	Entry::Occupied(t) => return Ok(t.get().clone()),
		// 	Entry::Vacant(e) => e,
		// };

		let e = self.x.borrow().e.clone();
		let lit_to_bin_enc = |a: C, _cmp: Comparator, lit: Lit, dom: &[C]| {
			assert!(self.c.is_positive(), "TODO neg scm");
			let c = a.abs() * self.c.abs();
			let bin_enc = BinEnc::from_lits(
				&as_binary(c.into(), None)
					.into_iter()
					.map(|bit| LitOrConst::from(bit.then_some(lit.clone()))) // if true, return Lit(lit), if false, return Const(false)
					.collect_vec(),
			);

			let y = IntVar::from_dom_as_ref(
				0,
				Dom::from_slice(dom),
				false,
				Some(IntVarEnc::Bin(Some(bin_enc))),
				Some(format!("scm-{}·{}", self.c, self.x.borrow().lbl())),
			);

			Ok(Term::from(y))
		};
		let dom = self.dom().iter().sorted().copied().collect_vec();
		let t = match e {
			Some(IntVarEnc::Bin(_)) if self.c.is_zero() => {
				return Ok(Term::from(IntVar::from_dom_as_ref(
					0,
					Dom::from_slice(&[C::zero()]),
					false,
					None,
					None,
				)));
			}
			Some(IntVarEnc::Bin(_)) if self.c.is_one() => {
				return Ok(self);
			}
			Some(IntVarEnc::Bin(Some(x_bin))) if (-self.c).is_one() => {
				Ok(Term::from(IntVar::from_dom_as_ref(
					0,
					// See unit test for example -1 * (x in 2..6[..9]) == y in [-9..]-6..-2
					Dom::from_bounds(
						-(self.x.borrow().lb() + x_bin.range::<C>().1),
						-self.x.borrow().lb(),
					),
					false,
					Some(IntVarEnc::Bin(Some(BinEnc::from_lits(
						&x_bin.xs().into_iter().map(|l| -l).collect_vec(),
					)))),
					Some(format!("-{}", self.x.borrow().lbl())),
				)))
			}
			Some(IntVarEnc::Bin(Some(x_bin))) if x_bin.x.len() == 1 => {
				if let [LitOrConst::Lit(lit)] = &x_bin.x.clone()[..] {
					lit_to_bin_enc(C::one(), cmp, lit.clone(), &dom)
				} else {
					unreachable!()
				}
			}
			Some(IntVarEnc::Ord(Some(x_ord))) if x_ord.x.len() <= 1 => {
				if let &[lit] = &x_ord.iter().take(2).collect_vec()[..] {
					// also pass in normalized value of the one literal
					lit_to_bin_enc(
						self.x.borrow().ub() - self.x.borrow().lb(),
						cmp,
						lit.clone(),
						&dom,
					)
				} else {
					unreachable!()
				}
			}
			Some(IntVarEnc::Ord(None)) => {
				/// Couple terms means coupling a*x:O <= y:B i/o x:O <= y:B (and using SCM later for a*y:B)
				const COUPLE_TERM: bool = true;
				let couple_term = USE_CHANNEL || COUPLE_TERM;

				let model = model.as_mut().unwrap();
				// FCreate
				// Create y:O <= x:B
				let up = self.c.is_positive();
				let dom = if couple_term {
					Dom::from_slice(
						&dom.into_iter()
							.map(|d| if up { d } else { -d })
							.sorted()
							.collect_vec(),
					)
				} else {
					self.x.borrow().dom.clone()
				};
				let y = model.new_var_from_dom(
					dom,
					false,
					Some(IntVarEnc::Bin(None)), // y:B
					self.x
						.borrow()
						.lbl
						.clone()
						.map(|lbl| format!("couple-{lbl}")),
				)?;

				// coupling constraint
				model.add_constraint(Lin {
					exp: LinExp {
						terms: vec![
							// Term::new(self.c.abs(), self.x.clone()),
							Term::new(
								if couple_term {
									if up {
										self.c
									} else {
										-self.c
									}
								} else {
									C::one()
								},
								self.x.clone(),
							),
							Term::new(-C::one(), y.clone()),
						],
					},
					cmp: if USE_CHANNEL {
						Comparator::Equal
					} else if up {
						cmp
					} else {
						cmp.reverse()
					},
					k: C::zero(),
					lbl: con_lbl.clone().map(|lbl| format!("couple-{lbl}")),
				})?;

				Ok(Term::new(
					if couple_term {
						if up {
							C::one()
						} else {
							-C::one()
						}
					} else {
						self.c
					},
					y,
				))
			}
			Some(IntVarEnc::Bin(Some(x_bin))) => {
				// assert!(self.c.is_multiple_of(&C::from(2).unwrap()));
				let sh = self.c.trailing_zeros() as usize;
				return Ok(Term::new(
					self.c.shr(sh),
					IntVar::from_dom_as_ref(
						0,
						Dom::from_slice(&dom),
						false, // view never needs consistency
						Some(IntVarEnc::Bin(Some(BinEnc::from_lits(
							&(0..sh)
								.map(|_| LitOrConst::Const(false))
								.chain(x_bin.xs().iter().cloned())
								.collect_vec(),
						)))),
						Some(format!("scm-{}·{}", self.c, self.x.borrow().lbl())),
					),
				));
			}
			Some(IntVarEnc::Bin(None)) if self.c.trailing_zeros() > 0 => {
				let sh = self.c.trailing_zeros();
				return Ok(Term::new(self.c.shr(sh as usize), self.x.clone())
					.encode_bin(model, cmp, con_lbl)?
					* C::one().shl(sh as usize));
			}
			Some(IntVarEnc::Bin(None)) => {
				assert!(self.c.trailing_zeros() == 0);
				let model = model.as_mut().unwrap();
				match model.config.scm {
					Scm::Rca | Scm::Add => {
						let lits = if model.config.scm == Scm::Add {
							BinEnc::<Lit>::required_lits(&self.x.borrow().dom)
						} else {
							0
						};
						let c = self.c;
						let scm = SCM
							.iter()
							.find_map(|(bits, mul, scm)| {
								(*bits == lits && C::from(*mul).unwrap() == c).then_some(scm)
							})
							.unwrap_or_else(|| {
								panic!("Cannot find scm recipe for c={c},lits={lits}")
							})
							.to_vec();

						let mut ys = [(0, C::one())].into_iter().collect::<HashMap<_, _>>();

						let get_and_shift =
							|ys: &HashMap<usize, C>, cse: &Cse<Lit, C>, i: usize, sh: usize| {
								let c = ys[&i];
								let x = if c.is_one() {
									Term::from(self.x.clone())
								} else {
									cse.0[&(self.x.borrow().id, c, Comparator::Equal)].clone()
								};
								(c.shl(sh), x * C::one().shl(sh))
							};

						for rca in scm {
							let (z_i, i1, sh1, i2, sh2) = (rca.i, rca.i1, rca.sh1, rca.i2, rca.sh2);

							let ((c_x, t_x), (c_y, t_y)) = (
								get_and_shift(&ys, &model.cse, i1, sh1),
								get_and_shift(&ys, &model.cse, i2, sh2),
							);
							let (c_y, t_y) = if rca.add {
								(c_y, t_y.clone())
							} else {
								(-c_y, t_y * -C::one())
							};

							let c = c_x + c_y;
							let z = model.new_var_from_dom(
								if rca.add {
									Dom::from_bounds(t_x.lb() + t_y.lb(), t_x.ub() + t_y.ub())
								} else {
									Dom::from_bounds(C::zero(), t_x.ub() + t_y.lb())
								},
								false,
								Some(IntVarEnc::Bin(None)),
								Some(format!("{c}*{}", self.x.borrow().lbl())),
							)?;

							ys.insert(z_i, c);
							model.add_constraint(Lin {
								exp: LinExp {
									terms: vec![t_x, t_y, Term::new(-C::one(), z.clone())],
								},
								cmp: Comparator::Equal,
								k: C::zero(),
								lbl: Some(String::from("scm")),
							})?;
							let key = (self.x.borrow().id, c, Comparator::Equal);
							model.cse.0.insert(key, Term::from(z));
						}
						Ok(model.cse.0[&(self.x.borrow().id, self.c, Comparator::Equal)].clone())
					}
					Scm::Pow => todo!(),
					Scm::Dnf => {
						let y = model
							.new_var(
								&dom,
								false,
								Some(IntVarEnc::Bin(None)), // annotate to use BinEnc
								Some(format!("scm-{}·{}", self.c, self.x.borrow().lbl())),
							)
							.unwrap();

						model
							.add_constraint(Lin {
								exp: LinExp {
									terms: vec![self.clone(), Term::new(-C::one(), y.clone())],
								},
								cmp: Comparator::Equal,
								k: C::zero(),
								lbl: con_lbl.clone().map(|lbl| (format!("scm-{}", lbl))),
							})
							.unwrap();
						Ok(Term::from(y))
					}
				}
			}
			_ => return Ok(self),
		}?;

		if USE_CSE {
			if let Some(model) = model.as_mut() {
				model
					.cse
					.0
					.insert((self.x.borrow().id, self.c, cmp), t.clone());
			}
		}

		Ok(t)
	}

	pub fn ineqs(&self, up: bool) -> Vec<(C, Vec<Lit>, C)> {
		self.x.borrow().ineqs(up)
	}

	pub fn lb(&self) -> C {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().ub()
			} else {
				self.x.borrow().lb()
			})
	}

	pub(crate) fn ub(&self) -> C {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().lb()
			} else {
				self.x.borrow().ub()
			})
	}

	// TODO [?] correct way to return an iter with this if-else which returns different iter types?
	pub(crate) fn dom(&self) -> Vec<C> {
		if self.c.is_zero() {
			vec![C::zero()]
		} else {
			self.x.borrow().dom.iter().map(|d| self.c * d).collect_vec()
		}
	}

	pub(crate) fn size(&self) -> C {
		self.x.borrow().size()
	}
}

#[cfg(test)]
mod tests {
	type Lit = i32;
	type C = i64;

	use crate::{helpers::tests::TestDB, Unsatisfiable};

	use super::*;
	#[test]
	fn term_test() {
		((|| {
			let mut db = TestDB::new(0);
			let mut model = Model::<Lit, C>::default();
			let x = Term::new(
				-1,
				model.new_var_from_dom(
					Dom::from_bounds(2, 6),
					true,
					Some(IntVarEnc::Bin(None)),
					None,
				)?,
			);
			x.x.borrow_mut().encode_bin(&mut db)?;
			let y = x.encode_bin(None, Comparator::Equal, None)?;

			// -x in 2..6[..9]
			//  y in [-9..]-6..-2
			// ALL FALSE -> x000=2 -> y111=-2 = -9 + 7 :)
			// ALL FALSE -> x111=7 -> y000=-9
			// ALL FALSE -> x101=5 -> y010=-5

			assert_eq!(y.x.borrow().dom, Dom::from_bounds(-9, -2));
			Ok::<(), Unsatisfiable>(())
		})())
		.unwrap()
	}
}
/*
   OLD SCM
	// TODO move enc into Term ?
	// TODO clippy
	#[allow(clippy::type_complexity)]
	pub(crate) fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		config: &ModelConfig<C>,
	) -> Result<(Vec<IntVarEnc<DB::Lit, C>>, C), Unsatisfiable> {
		let enc = self.x.borrow().e.as_ref().unwrap().clone();
		if self.c == C::zero() {
			Ok((vec![IntVarEnc::Const(C::zero())], C::zero()))
		} else if self.c == C::one() {
			Ok((vec![enc.clone()], C::zero()))
		} else {
			match enc {
				IntVarEnc::Ord(o) => Ok((vec![IntVarEnc::Ord(o.mul(db, self.c))], C::zero())),
				IntVarEnc::Bin(x_enc) => {
					// handle negative coefficient
					let (mut c, xs, k, dom) = if !self.c.is_negative() {
						(
							self.c,
							x_enc.xs(false),
							C::zero(),
							Dom::from_slice(
								&self
									.x
									.borrow()
									.dom
									.iter()
									.map(|d| self.c * d)
									.sorted()
									.collect::<Vec<_>>(),
							),
						)
					} else {
						(
							-self.c,
							x_enc.xs(false).into_iter().map(|x| -x).collect(), // 2-comp
							-self.c, // return constant addition `-c` because `-c*x = c* -x = c* (1-~x) = c - c*~x`
							Dom::from_slice(
								&self
									.x
									.borrow()
									.dom
									.iter()
									.map(|d| self.c * d + self.c)
									// -1 * {0,1} = {-1,0} = {-2,-1} + 1
									// [b,F] in {0,1} = [!b,T] in {-2,-1}
									.sorted()
									.collect::<Vec<_>>(),
							),
						)
					};

					// TODO shift by zeroes..
					let mut sh = 0;

					while c.is_even() {
						sh += 1;
						c = c.div(C::one() + C::one());
					}

					let lits = match config.scm {
						Scm::Add | Scm::Dnf => x_enc.lits(),
						Scm::Rca | Scm::Pow => 0,
					};

					let scm = match config.scm {
						_ if c.is_one() => Some(vec![]),
						Scm::Add | Scm::Rca => SCM
							.iter()
							.find_map(|(bits, mul, scm)| {
								(*bits == lits && C::from(*mul).unwrap() == c).then_some(scm)
							})
							.map(|v| v.to_vec()),
						Scm::Pow => None,
						Scm::Dnf => {
							let cnf = Cnf::<DB::Lit>::from_file(&PathBuf::from(format!(
								"{}/res/ecm/{lits}_{c}.dimacs",
								env!("CARGO_MANIFEST_DIR")
							)))
							.unwrap_or_else(|_| {
								panic!("Could not find Dnf method cnf for {lits}_{c}")
							});
							let map = cnf
								.vars()
								.zip(
									xs.iter()
										.flat_map(|x| match x {
											LitOrConst::Lit(l) => Some(l.clone()),
											_ => None,
										})
										.chain(
											(0..(cnf.variables() - lits))
												.map(|_i| {
													new_var!(
														db,
														format!(
															"{}_y_{}",
															self.x.borrow().lbl(),
															_i
														)
													)
												})
												.collect::<Vec<_>>(),
										),
								)
								.collect::<HashMap<_, _>>();
							cnf.iter().try_for_each(|clause| {
								emit_clause!(
									db,
									&clause
										.iter()
										.map(|x| {
											let lit = &map[&x.var()];
											if x.is_negated() {
												lit.negate()
											} else {
												lit.clone()
											}
										})
										.collect::<Vec<_>>()
								)
							})?;
							return Ok((
								vec![IntVarEnc::Bin(IntVarBin::from_lits(
									&num::iter::range(C::zero(), C::from(sh).unwrap())
										.map(|_| LitOrConst::Const(false))
										.chain(
											map.values()
												.sorted()
												.skip(lits)
												.cloned()
												.map(LitOrConst::from),
										)
										.collect::<Vec<_>>(),
									dom,
									format!("{}*{}", self.c.clone(), self.x.borrow().lbl()),
								))],
								k,
							));
						}
					};

					// if we have no recipe for this particular (b,c) key, in which case we fallback to Pow
					let scm = if let Some(scm) = scm {
						scm
					} else {
						assert!(
							matches!(config.scm, Scm::Pow),
							"Current SCM DB is complete but could not find {c} for {lits}"
						);
						return Ok((
							as_binary(c.into(), None)
								.into_iter()
								.enumerate()
								.filter_map(|(shift, b)| b.then_some(sh + shift))
								.map(|sh| {
									let xs = num::iter::range(C::zero(), C::from(sh).unwrap())
										.map(|_| LitOrConst::Const(false))
										.chain(xs.clone())
										.collect::<Vec<_>>();
									IntVarEnc::Bin(IntVarBin::from_lits(
										&xs,
										x_enc.dom.clone().mul(C::one().shl(sh)),
										format!("{}<<{}", self.x.borrow().lbl(), sh.clone()),
									))
								})
								.collect(),
							k,
						));
					};

					// TODO store `c` value i/o of node index
					let mut ys = [(C::zero(), xs)].into_iter().collect::<HashMap<_, _>>();

					let get_and_shift =
						|ys: &HashMap<C, Vec<LitOrConst<DB::Lit>>>, i: C, sh: usize| {
							(0..sh)
								.map(|_| LitOrConst::Const(false))
								.chain(
									ys.get(&i)
										.unwrap_or_else(|| {
											panic!("ys[{i}] does not exist in {ys:?} when encoding SCM {c}*x of {lits} lits")
										})
										.clone(),
								)
								.collect::<Vec<_>>()
						};

					for rca in scm {
						let (i, i1, sh1, i2, sh2) = (
							C::from(rca.i).unwrap(),
							C::from(rca.i1).unwrap(),
							rca.sh1 as usize,
							C::from(rca.i2).unwrap(),
							rca.sh2 as usize,
						);
						let (z_i, x, add, y) = (
							i,
							get_and_shift(&ys, i1, sh1),
							rca.add,
							get_and_shift(&ys, i2, sh2),
						);

						// If subtracting, use 2-comp of y and set initial carry to true
						let (y, c) = if add {
							(y, false)
						} else {
							(y.into_iter().map(|l| -l).collect(), true)
						};

						let z = log_enc_add_fn(db, &x, &y, &Comparator::Equal, c.into(), None)?;
						ys.insert(z_i, z);
					}

					let xs = get_and_shift(&ys, *ys.keys().max().unwrap(), sh);
					Ok((
						vec![IntVarEnc::Bin(IntVarBin::from_lits(
							&xs,
							dom,
							format!("{}*{}", self.c, self.x.borrow().lbl()),
						))],
						k,
					))
				}
				IntVarEnc::Const(c) => Ok((vec![IntVarEnc::Const(c * self.c)], C::zero())),
			}
		}
	}
*/
