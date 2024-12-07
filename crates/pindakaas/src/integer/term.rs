use std::ops::{Mul, Shl};

use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::{bin::BinEnc, enc::IntVarEnc, model::Scm, Dom, Model};
use crate::{
	bool_linear::{Comparator, PosCoeff},
	helpers::{as_binary, div_ceil, div_floor},
	integer::{
		enc::LitOrConst,
		helpers::required_lits,
		model::{Cse, USE_CHANNEL, USE_CSE},
		res::SCM,
		IntVar, IntVarRef, Lin, LinExp,
	},
	log, Coeff, Lit, Unsatisfiable,
};

/// A linear term (constant times integer variable)
#[derive(Debug, Clone)]
pub struct Term {
	pub c: Coeff,
	pub x: IntVarRef,
}

impl Mul<Coeff> for Term {
	type Output = Self;
	fn mul(self, rhs: Coeff) -> Self {
		Self {
			x: self.x,
			c: self.c * rhs,
		}
	}
}

impl Shl<u32> for Term {
	type Output = Self;
	fn shl(self, rhs: u32) -> Self {
		Self {
			x: self.x,
			c: self.c << rhs,
		}
	}
}

impl From<IntVarRef> for Term {
	fn from(value: IntVarRef) -> Self {
		Term::new(1, value)
	}
}

impl From<Coeff> for Term {
	fn from(c: Coeff) -> Self {
		Term::from(IntVar::new_constant(c))
	}
}

impl TryFrom<IntVar> for Coeff {
	type Error = ();
	fn try_from(val: IntVar) -> Result<Self, Self::Error> {
		val.dom.clone().try_into()
	}
}

impl TryFrom<Term> for IntVarRef {
	type Error = ();

	fn try_from(value: Term) -> Result<Self, Self::Error> {
		// TODO bad so long as dom() is bad
		if let Ok(c) = Coeff::try_from(Dom::new(value.dom())) {
			Ok(IntVar::new_constant(c))
		} else {
			(value.c == 1).then_some(value.x).ok_or(())
		}
	}
}

impl Term {
	pub fn new(c: Coeff, x: IntVarRef) -> Self {
		Self { c, x }
	}

	pub fn lbl(&self) -> String {
		format!("{}*{}", self.c, self.x.borrow().lbl)
	}

	pub(crate) fn encode_bin(
		self,
		mut model: Option<&mut Model>,
		cmp: Comparator,
		con_lbl: &str,
	) -> crate::Result<Self> {
		if USE_CSE {
			if let Some(model) = &model {
				log!("CSE: {}", model.cse);
				if let Some(t) = model.cse.0.get(&(self.x.borrow().id, self.c, cmp)) {
					log!("HIT: ({self}) -> {t}");
					return Ok(t.clone());
				}
			}
		}

		// TODO [!] refactor using entry
		// let cse = match model
		// 	.cse
		// 	.entry((self.x.borrow().id, self.c))
		// {
		// 	Entry::Occupied(t) => return Ok(t.get().clone()),
		// 	Entry::Vacant(e) => e,
		// };

		let e = self.x.borrow().e.clone();
		let lit_to_bin_enc = |a: Coeff, _cmp: Comparator, lit: Lit, dom: &[Coeff]| {
			let c = a.abs() * self.c.abs();
			let bin_enc = BinEnc::from_lits(
				&as_binary(PosCoeff::new(c), None)
					.into_iter()
					.map(|bit| LitOrConst::from(bit.then_some(lit))) // if true, return Lit(lit), if false, return Const(false)
					.collect_vec(),
			);

			let y = IntVar::from_dom_as_ref(
				0,
				Dom::new(dom.into_iter().cloned()),
				false,
				Some(IntVarEnc::Bin(Some(bin_enc))),
				format!("{con_lbl}-scm-{}·{}", self.c, self.x.borrow().lbl()),
			);

			Ok(Term::from(y))
		};
		// TODO [!] remove
		let dom = self.dom().iter().sorted().copied().collect_vec();
		let t = match e {
			Some(IntVarEnc::Bin(_)) if self.c == 0 => {
				return Ok(Term::from(IntVar::new_constant(0)));
			}
			Some(IntVarEnc::Bin(_)) if self.c == 1 => {
				return Ok(self);
			}
			Some(IntVarEnc::Bin(Some(x_bin))) if x_bin.x.len() == 1 && self.c.is_positive() => {
				// TODO generalize for neg. c
				if let [LitOrConst::Lit(lit)] = &x_bin.x.clone()[..] {
					lit_to_bin_enc(1, cmp, *lit, &dom)
				} else {
					unreachable!()
				}
			}
			Some(IntVarEnc::Ord(Some(x_ord))) if x_ord.x.len() <= 1 && self.c.is_positive() => {
				if let &[lit] = &x_ord.iter().take(2).collect_vec()[..] {
					// also pass in normalized value of the one literal
					lit_to_bin_enc(self.x.borrow().ub() - self.x.borrow().lb(), cmp, *lit, &dom)
				} else {
					unreachable!()
				}
			}
			Some(IntVarEnc::Bin(Some(x_bin))) if self.c.is_negative() => {
				let (_, range_ub) = x_bin.range();
				return Term::new(
					-self.c,
					IntVar::from_dom_as_ref(
						0,
						// See unit test for example -1 * (x in 2..6[..9]) == y in [-9..]-6..-2
						Dom::from_bounds(
							-(self.x.borrow().lb() + range_ub),
							-self.x.borrow().lb(), // TODO might be ground i/o lb
						),
						false,
						Some(IntVarEnc::Bin(Some(x_bin.clone().complement()))),
						format!("{con_lbl}-scm-b-{}", self.x.borrow().lbl()),
					),
				)
				.encode_bin(model, cmp, con_lbl);
			}
			Some(IntVarEnc::Bin(Some(x_bin))) if self.c.trailing_zeros() > 0 => {
				let sh = self.c.trailing_zeros() as usize;
				return Term::new(
					self.c >> sh,
					IntVar::from_dom_as_ref(
						0,
						Dom::new(dom.into_iter()), // TODO just use bounds
						false,                     // view never needs consistency
						Some(IntVarEnc::Bin(Some(BinEnc::from_lits(
							&(0..sh)
								.map(|_| LitOrConst::Const(self.c.is_negative()))
								.chain(x_bin.xs().iter().cloned())
								.collect_vec(),
						)))),
						format!("{con_lbl}-scm-{}·{}", self.c, self.x.borrow().lbl()),
					),
				)
				.encode_bin(model, cmp, con_lbl);
			}
			Some(IntVarEnc::Ord(None)) => {
				/// Couple terms means coupling a*x:O <= y:B i/o x:O <= y:B (and using SCM later for a*y:B)
				const COUPLE_TERM: bool = true;
				let couple_term = USE_CHANNEL || COUPLE_TERM;

				let model = model.as_mut().unwrap();
				// Create y:O <= x:B
				let up = self.c.is_positive();
				let dom = if couple_term {
					Dom::new(dom.into_iter().map(|d| if up { d } else { -d }))
				} else {
					self.x.borrow().dom.clone()
				};
				let y = model.new_aux_var(
					dom,
					false,
					Some(IntVarEnc::Bin(None)), // y:B
					format!("{con_lbl}-cpl_{}", self.x.borrow().lbl),
				)?;

				// coupling constraint
				model.add_constraint(Lin {
					exp: LinExp {
						terms: vec![
							Term::new(
								if couple_term {
									if up {
										self.c
									} else {
										-self.c
									}
								} else {
									1
								},
								self.x.clone(),
							),
							Term::new(-1, y.clone()),
						],
					},
					cmp: if USE_CHANNEL {
						Comparator::Equal
					} else if up {
						cmp
					} else {
						cmp.reverse()
					},
					k: 0,
					lbl: format!("{con_lbl}-cpl"),
				})?;

				Ok(Term::new(
					if couple_term {
						if up {
							1
						} else {
							-1
						}
					} else {
						self.c
					},
					y,
				))
			}
			Some(IntVarEnc::Bin(None))
				if self.c.is_negative()
					&& model
						.as_ref()
						.map(|model| model.config.scm != Scm::Dnf)
						.unwrap_or_default() =>
			{
				let model = model.as_mut().unwrap();

				// c = -5, x in -3..0
				// -5*(x in -3..0)
				// take care of negative sign: -x = y in -3..0
				let y = model.new_aux_var(
					Dom::from_bounds(-self.x.borrow().ub(), -self.x.borrow().lb()),
					false,
					Some(IntVarEnc::Bin(None)),
					format!("{con_lbl}-scm_neg_{}", self.x.borrow().lbl),
				)?;

				// -x = y
				model.add_constraint(Lin {
					exp: LinExp {
						terms: vec![
							Term::new(-1, self.x.clone()),
							Term::from(0), // force to use RCA, reconciling the offset
							Term::new(-1, y.clone()),
						],
					},
					cmp: Comparator::Equal,
					k: 0,
					lbl: format!("{con_lbl}-scm_neg"),
				})?;

				// z is -c times y: z = 5*(y in -3..0)
				// take care of multiplication
				let z = Term::new(-self.c, y.clone()).encode_bin(Some(model), cmp, con_lbl)?;

				Ok(z)
			}
			Some(IntVarEnc::Bin(None)) if self.c.trailing_zeros() > 0 => {
				let sh = self.c.trailing_zeros();
				return Ok(Term::new(self.c >> sh, self.x.clone())
					.encode_bin(model, cmp, con_lbl)?
					<< sh);
			}
			Some(IntVarEnc::Bin(None)) => {
				assert!(self.c.trailing_zeros() == 0);
				let model = model.as_mut().unwrap();
				match model.config.scm {
					Scm::Rca | Scm::Add => {
						let lits = if model.config.scm == Scm::Add {
							required_lits(&self.x.borrow().dom)
						} else {
							0
						};
						let c = self.c;
						let scm = SCM
							.iter()
							.find_map(|(bits, mul, scm)| {
								(*bits == lits && mul == &c).then_some(scm)
							})
							.unwrap_or_else(|| {
								panic!("Cannot find scm recipe for c={c},lits={lits}")
							})
							.to_vec();

						let mut ys = [(0, 1)].into_iter().collect::<FxHashMap<_, _>>();

						let get_and_shift =
							|ys: &FxHashMap<usize, Coeff>, cse: &Cse, i: usize, sh: u32| {
								let c = ys[&i];
								let x = if c == 1 {
									Term::from(self.x.clone())
								} else {
									cse.0[&(self.x.borrow().id, c, Comparator::Equal)].clone()
								};
								(c << sh, x << sh)
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
								(-c_y, t_y * -1)
							};

							let c = c_x + c_y;
							let z = model.new_aux_var(
								// z's represents c*x, so its domain can be directly calculated from c*dom(x)
								Dom::from_bounds(
									c * self.x.borrow().lb(),
									c * self.x.borrow().ub(),
								),
								false,
								Some(IntVarEnc::Bin(None)),
								format!("{}-{c}·{}", cmp, self.x.borrow().lbl()),
							)?;

							ys.insert(z_i, c);
							model.add_constraint(Lin {
								exp: LinExp {
									terms: vec![t_x, t_y, Term::new(-1, z.clone())],
								},
								cmp: Comparator::Equal,
								k: 0,
								lbl: format!("{con_lbl}-scm-{z_i}"),
							})?;
							let key = (self.x.borrow().id, c, Comparator::Equal);
							model.cse.0.insert(key, Term::from(z));
						}
						Ok(model.cse.0[&(self.x.borrow().id, self.c, Comparator::Equal)].clone())
					}
					Scm::Dnf => {
						let y = model
							.new_aux_var(
								Dom::new(dom.into_iter()),
								false,
								Some(IntVarEnc::Bin(None)), // annotate to use BinEnc
								format!("{con_lbl}_{}_scm_dnf", self.lbl()),
							)
							.unwrap();

						model
							.add_constraint(Lin {
								exp: LinExp {
									terms: vec![self.clone(), Term::new(-1, y.clone())],
								},
								cmp: Comparator::Equal,
								k: 0,
								lbl: format!("{con_lbl}-{}_scm_dnf", self.lbl()),
							})
							.unwrap();
						Ok(Term::from(y))
					}
					_ => todo!(),
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

	pub(crate) fn ineqs(&self, up: bool) -> Vec<(Coeff, Vec<Lit>, Coeff)> {
		self.x.borrow().ineqs(up)
	}

	/// c*x >=k
	pub(crate) fn ineq(&self, k: Coeff, up: bool, _: Option<Coeff>) -> Vec<Vec<Lit>> {
		let k_ = if up {
			div_ceil(k, self.c)
		} else {
			div_floor(k, self.c) + 1
		};

		let (_, cnf) = self.x.borrow().ineq(k_, up, None);
		cnf
	}

	pub(crate) fn lb(&self) -> Coeff {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().ub()
			} else {
				self.x.borrow().lb()
			})
	}

	pub(crate) fn ub(&self) -> Coeff {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().lb()
			} else {
				self.x.borrow().ub()
			})
	}

	// TODO [?] correct way to return an iter with this if-else which returns different iter types?
	// TODO return Dom?
	pub(crate) fn dom(&self) -> Vec<Coeff> {
		if self.c == 0 {
			vec![0]
		} else {
			self.x.borrow().dom.iter().map(|d| self.c * d).collect_vec()
		}
	}

	pub(crate) fn bounds(&self) -> Dom {
		if !self.c.is_positive() {
			Dom::from_bounds(self.c * self.x.borrow().ub(), self.c * self.x.borrow().lb())
		} else {
			Dom::from_bounds(self.c * self.x.borrow().lb(), self.c * self.x.borrow().ub())
		}
	}

	pub(crate) fn size(&self) -> Coeff {
		self.x.borrow().size()
	}

	pub(crate) fn _add(&self, other: Self, model: &mut Model) -> Result<Self, Unsatisfiable> {
		let (x, y) = (self, other);
		let z = Term::from(model.new_aux_var(
			Dom::from_bounds(x.lb() + y.lb(), x.ub() + y.ub()),
			false,
			Some(IntVarEnc::Bin(None)),
			format!("{}+{}", x.lbl(), y.lbl()),
		)?);

		model.add_constraint(Lin {
			exp: LinExp {
				terms: vec![x.clone(), y.clone(), z.clone() * -1],
			},
			cmp: Comparator::Equal,
			k: 0,
			lbl: format!("add-{}", z.lbl()),
		})?;
		Ok(z)
	}
}

#[cfg(test)]
mod tests {
	use crate::Cnf;

	use super::*;

	#[test]
	fn term_test() {
		let mut db = Cnf::default();
		let mut model = Model::default();
		let x = Term::new(
			-1,
			model
				.new_aux_var(
					Dom::from_bounds(2, 6),
					true,
					Some(IntVarEnc::Bin(None)),
					"x1".to_owned(),
				)
				.unwrap(),
		);
		x.x.borrow_mut().encode_bin(&mut db).unwrap();
		let y = x.encode_bin(None, Comparator::Equal, "c1").unwrap();

		// -x in 2..6[..9]
		//  y in [-9..]-6..-2
		// ALL FALSE -> x000=2 -> y111=-2 = -9 + 7 :)
		// ALL FALSE -> x111=7 -> y000=-9
		// ALL FALSE -> x101=5 -> y010=-5

		assert_eq!(y.x.borrow().dom, Dom::from_bounds(-9, -2));
	}
}
