use crate::{
	helpers::{as_binary, unsigned_binary_range},
	int::LitOrConst,
	ClauseDatabase, Coefficient, IntVarRef, Literal,
};
use itertools::Itertools;
use std::ops::Mul;

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

impl<Lit: Literal, C: Coefficient> Term<Lit, C> {
	pub fn new(c: C, x: IntVarRef<Lit, C>) -> Self {
		Self { c, x }
	}

	pub(crate) fn encode_bin<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
	) -> crate::Result<BinEnc<Lit>> {
		let e = self.x.borrow().e.clone();
		let lit_to_bin_enc = |lit: DB::Lit| {
			assert!(self.c.is_positive(), "TODO neg scm");
			BinEnc::from_lits(
				&as_binary(self.c.abs().into(), None)
					.into_iter()
					.map(|bit| LitOrConst::from(bit.then_some(lit.clone()))) // if true, return Lit(lit), if false, return Const(false)
					.collect_vec(),
			)
		};
		match e {
			Some(IntVarEnc::Ord(Some(x_ord))) => {
				if let &[lit] = &x_ord.iter().take(2).collect_vec()[..] {
					Ok(lit_to_bin_enc(lit.clone()))
				} else {
					todo!("Need full scm for {self}: {self:?}")
				}
			}
			Some(IntVarEnc::Bin(Some(x_bin))) if x_bin.x.len() == 1 => {
				if let [LitOrConst::Lit(lit)] = &x_bin.x.clone()[..] {
					Ok(lit_to_bin_enc(lit.clone()))
				} else {
					unreachable!()
				}
			}
			_ if self.c.is_one() => self.x.borrow_mut().encode_bin(db),
			_ => todo!("{self}: {self:?}"),
		}
	}

	pub fn ineqs(&self, up: bool) -> Vec<(C, Vec<Lit>, bool)> {
		let ineqs = |es: Vec<Vec<Lit>>, dom: Dom<C>, up: bool| {
			// go through False lit first
			let es: Vec<_> = if up {
				std::iter::once(vec![]) // x>=ub(x)+1
					.chain(
						// x>=ub(x), x>=ub(x)-1, .., x>=lb(x)+1
						es.into_iter().rev(),
					)
					.collect()
			} else {
				std::iter::once(vec![]) // x<lb(x)
					.chain(
						// x<lb(x)+1, x<lb(x)+2, .., x<ub(x)
						es.into_iter()
							.map(|clause| clause.into_iter().map(|l| l.negate()).collect()),
					)
					.collect()
			};

			let ds: Vec<_> = if up {
				dom.iter().collect_vec().into_iter().rev().collect()
			} else {
				dom.iter().collect()
			};
			ds.into_iter().zip(es)
		};
		match self
			.x
			.borrow()
			.e
			.as_ref()
			.unwrap_or_else(|| panic!("{} was not encoded", self.x.borrow()))
		{
			IntVarEnc::Ord(Some(x_ord)) => ineqs(
				x_ord.x.clone().into_iter().map(|l| vec![l]).collect(),
				self.x.borrow().dom.clone(),
				up,
			)
			.map(|(c, cnf)| (c, cnf, self.x.borrow().add_consistency))
			.collect(),
			IntVarEnc::Bin(Some(x_bin)) => {
				// TODO not (particularly) optimized for the domain of x, but this is tricky as the domain values go outside the binary encoding ranges
				let (range_lb, range_ub) = unsigned_binary_range::<C>(x_bin.bits());

				ineqs(
					num::iter::range_inclusive(range_lb, range_ub - C::one())
						.map(|k| x_bin.geq(if up { range_ub - k } else { k + C::one() }))
						.collect(),
					Dom::from_bounds(range_lb, range_ub).add(self.x.borrow().lb()), // denormalize
					up,
				)
				.map(|(c, cnf)| (c, cnf, self.x.borrow().add_consistency))
				.collect()
			}
			_ => unreachable!(),
		}
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
