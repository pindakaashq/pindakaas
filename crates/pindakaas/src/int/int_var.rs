use itertools::Itertools;
use rustc_hash::FxHashMap;
use std::{
	cell::RefCell,
	collections::{HashMap, HashSet},
	fmt::Display,
	hash::BuildHasherDefault,
	rc::Rc,
};

use crate::{
	helpers::{negate_cnf, two_comp_bounds, unsigned_binary_range},
	int::display::SHOW_IDS,
	linear::Part,
	trace::{emit_clause, new_var},
	CheckError, ClauseDatabase, Coefficient, Literal, Model, PosCoeff, Result, Unsatisfiable,
};

use super::{
	bin::BinEnc, enc::GROUND_BINARY_AT_LB, model::PRINT_COUPLING, ord::OrdEnc, required_lits, Dom,
	IntVarEnc,
};

#[derive(Hash, Copy, Clone, Debug, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct IntVarId(pub usize);

pub type IntVarRef<Lit, C> = Rc<RefCell<IntVar<Lit, C>>>;

impl Display for IntVarId {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}
// TODO perhaps id can be used by replacing vars HashMap to just vec
// TODO why can't we derive Default without impl. for Lit (since it's in Option?)
#[derive(Debug, Clone)]
pub struct IntVar<Lit: Literal, C: Coefficient> {
	pub id: IntVarId,
	pub dom: Dom<C>,
	pub(crate) add_consistency: bool,
	pub(crate) views: HashMap<C, (IntVarId, C)>,
	pub(crate) e: Option<IntVarEnc<Lit, C>>,
	// pub(crate) x: OrdEnc<Lit>,
	lbl: Option<String>,
}

// TODO implement Eq so we don't compare .e

impl<Lit: Literal, C: Coefficient> IntVar<Lit, C> {
	/*
	pub(crate) fn new(
		id: usize,
		dom: &[C],
		add_consistency: bool,
		e: Option<IntVarEnc<Lit, C>>,
		lbl: Option<String>,
	) -> Self {
		Self::from_dom(id, Dom::from_slice(dom), add_consistency, e, lbl)
	}

	fn into_ref(self) -> IntVarRef<Lit, C> {
		Rc::new(RefCell::new(self))
	}

	// TODO should not be C i/o &C?
	fn fix(&mut self, q: &C) -> Result {
		if self.dom.contains(*q) {
			self.dom = Dom::from_slice(&[*q]);
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}

	*/

	pub(crate) fn from_dom(
		id: usize,
		dom: Dom<C>,
		add_consistency: bool,
		e: Option<IntVarEnc<Lit, C>>,
		lbl: Option<String>,
	) -> Self {
		Self {
			id: IntVarId(id),
			dom,
			add_consistency,
			views: HashMap::default(),
			e,
			// x: OrdEnc::default(),
			lbl,
		}
	}

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "consistency", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub(crate) fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		self.e
			.as_ref()
			.map(|e| e.consistent(db, &self.dom))
			.unwrap_or(Ok(()))
	}

	pub fn ineqs(&self, up: bool) -> Vec<(C, Vec<Lit>, C)> {
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
			.e
			.as_ref()
			.unwrap_or_else(|| panic!("{} was not encoded", self))
		{
			IntVarEnc::Ord(Some(x_ord)) => ineqs(
				x_ord.x.clone().into_iter().map(|l| vec![l]).collect(),
				self.dom.clone(),
				up,
			)
			.map(|(c, cnf)| {
				(
					c,
					cnf,
					if self.add_consistency {
						self.lb()
					// if up {
					// 	self.lb()
					// } else {
					// 	self.ub()
					// }
					} else {
						c
					},
				)
			})
			.collect(),
			IntVarEnc::Bin(Some(x_bin)) => {
				// TODO not (particularly) optimized for the domain of x, but this is tricky as the domain values go outside the binary encoding ranges
				let (range_lb, range_ub) = unsigned_binary_range::<C>(x_bin.bits());

				ineqs(
					num::iter::range_inclusive(range_lb, range_ub - C::one())
						.map(|k| x_bin.geq(if up { range_ub - k } else { k + C::one() }))
						.collect(),
					Dom::from_bounds(range_lb, range_ub).add(self.lb()), // denormalize
					up,
				)
				.map(|(c, cnf)| {
					(c, cnf, {
						let k = if up { range_ub - c } else { c };
						// let k = range_ub - c;
						let k = x_bin.normalize(k, &self.dom);
						let a = x_bin.geq_implies(k);
						let k = if up { c - a } else { c + a };
						x_bin.denormalize(k, &self.dom)
					})
				})
				.collect()
			}
			_ => unreachable!(),
		}
	}

	/// Return x>=k (given x>=a)
	pub fn ineq(&self, k: C, up: bool, a: Option<C>) -> (Option<C>, Vec<Vec<Lit>>) {
		// TODO move into IntVar since self.c is taken care off?
		match self.e.as_ref().unwrap() {
			IntVarEnc::Ord(Some(o)) => {
				// TODO make use of a?
				let pos = self.dom.geq(k);
				if PRINT_COUPLING {
					print!(" = d_{pos:?}");
				}
				let d = if let Some(pos) = pos {
					let pos = if up {
						Some(pos) // if larger than self.dom.size, then self.dom.d will return None
					} else {
						pos.checked_sub(1)
					};
					pos.and_then(|next_pos| self.dom.d(next_pos))
				} else {
					// TODO not sure if this should be ub/lb or None. This makes most sense looking at the test ineq_ord
					if up {
						None
					} else {
						Some(self.dom.ub())
					}
				};
				let geq = o.geq(pos);
				(d, if up { geq } else { negate_cnf(geq) })
			}
			IntVarEnc::Bin(Some(x_bin)) => {
				// x>=k == ¬(x<k) == ¬(x<=k-1) (or x<=k == ¬(x>k) == ¬(x>=k+1))
				// or: x>=k == x>=(2^bits - k)
				// returns Dnf e.q. (x1 \/ x0 /\ x0)
				// x1 /\ x0 -> x>=3 -> x0 \/ x2

				let (range_lb, range_ub) = unsigned_binary_range::<C>(x_bin.bits());
				let (k, a) = (
					x_bin.normalize(k, &self.dom),
					a.map(|a| x_bin.normalize(a, &self.dom)).unwrap_or(range_ub),
				);
				let (r_a, r_b) = if up {
					// x>=k \/ x>=k+1 \/ .. \/ x>=r_b
					(range_ub + C::one() - k, a)
				} else {
					(range_lb + k, a)
				};

				// TODO replace by ineqs..?
				let dnf = x_bin.geqs(r_a, r_b);

				let dnf = if up {
					dnf
				} else {
					// negate dnf
					if dnf.contains(&vec![]) {
						vec![vec![]]
					} else if dnf.is_empty() {
						vec![]
					} else {
						dnf.into_iter()
							.flat_map(|conjunct| negate_cnf(vec![conjunct]))
							.collect()
					}
				};
				(None, dnf)
			}
			IntVarEnc::Const(_) => todo!(),

			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}

	pub(crate) fn as_lin_exp(&self) -> crate::linear::LinExp<Lit, C> {
		match self.e.as_ref().unwrap() {
			IntVarEnc::Ord(Some(o)) => {
				crate::linear::LinExp::new()
					.add_chain(
						&self
							.dom
							.iter()
							.zip(o.ineqs(true))
							.tuple_windows()
							// Every lit adds the difference
							.map(|((prev, (_, _)), (v, (cnf, _)))| (cnf[0][0].clone(), v - prev))
							.collect::<Vec<_>>(),
					)
					.add_constant(self.lb())
			}
			IntVarEnc::Bin(Some(b)) => {
				let (terms, add) = b.as_lin_exp::<C>();
				// The offset and the fixed value `add` are added to the constant
				let add = if GROUND_BINARY_AT_LB {
					add + self.lb()
				} else if !self.dom.lb().is_negative() {
					add
				} else {
					add.checked_add(&two_comp_bounds::<C>(b.bits()).0).unwrap()
				};

				let (lb, ub) = if GROUND_BINARY_AT_LB {
					(C::zero() + add, self.ub() - self.lb() + add)
				} else {
					(self.lb() - add, self.ub() - add)
				};

				let lin_exp = crate::linear::LinExp::<Lit, C>::new().add_bounded_log_encoding(
					terms.as_slice(),
					// The Domain constraint bounds only account for the unfixed part of the offset binary notation
					lb,
					ub,
				);

				lin_exp.add_constant(add)
			}
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
			IntVarEnc::Const(c) => crate::linear::LinExp::new().add_constant(*c),
		}
	}

	pub fn assign(&self, a: &[Lit]) -> Result<C, CheckError<Lit>> {
		crate::linear::LinExp::from(self).assign(a)
		// match  {
		// 	IntVarEnc::Ord(o) => LinExp::from(o).assign
		// 	IntVarEnc::Bin(_) => todo!(),
		// 	IntVarEnc::Const(c) => Ok(*c),
		// }

		// .assign(a)
	}
	pub fn is_constant(&self) -> bool {
		self.size() == C::one()
	}

	pub(crate) fn lits(&self) -> HashSet<Lit> {
		self.e.as_ref().map(|e| e.lits()).unwrap_or_default()
	}

	pub(crate) fn encode_bin<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
	) -> Result<BinEnc<Lit>, Unsatisfiable> {
		self.encode(db, None).map(|e| match e {
			IntVarEnc::Bin(Some(b)) => b,
			_ => unreachable!(),
		})
	}

	pub(crate) fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		_views: Option<&mut HashMap<(IntVarId, C), Lit>>,
	) -> Result<IntVarEnc<Lit, C>, Unsatisfiable> {
		// cache instantiated encoding
		let e = match self.e {
			Some(IntVarEnc::Ord(Some(_))) | Some(IntVarEnc::Bin(Some(_))) => {
				return Ok(self.e.as_ref().unwrap().clone());
			}
			Some(IntVarEnc::Ord(_)) | None => {
				IntVarEnc::Ord(Some(OrdEnc::new(db, &self.dom, self.lbl.as_ref())))
			}
			Some(IntVarEnc::Bin(_)) => IntVarEnc::Bin(Some(BinEnc::new(
				db,
				required_lits::<C>(self.dom.lb(), self.dom.ub()),
				self.lbl.clone(),
			))),
			Some(IntVarEnc::Const(_)) => todo!(),
		};

		self.e = Some(e.clone());

		if self.add_consistency {
			self.consistent(db)?;
		}

		Ok(e)
	}

	pub(crate) fn ge(&mut self, bound: &C) {
		self.dom.ge(*bound);
	}

	pub(crate) fn le(&mut self, bound: &C) {
		self.dom.le(*bound);
	}

	pub(crate) fn size(&self) -> C {
		self.dom.size()
	}

	pub fn lb(&self) -> C {
		self.dom.lb()
	}

	pub fn ub(&self) -> C {
		self.dom.ub()
	}

	pub(crate) fn decide_encoding(&mut self, cutoff: Option<C>) -> IntVarEnc<Lit, C> {
		if let Some(e) = self.e.as_ref() {
			return e.clone();
		}
		self.e = Some(match cutoff {
			None => IntVarEnc::Ord(None),
			Some(cutoff) if cutoff == C::zero() => IntVarEnc::Bin(None),
			Some(cutoff) => {
				if self.dom.size() <= cutoff {
					IntVarEnc::Ord(None)
				} else {
					IntVarEnc::Bin(None)
				}
			}
		});
		self.e.clone().unwrap()
	}

	pub fn lbl(&self) -> String {
		if let Some(lbl) = self.lbl.as_ref() {
			format!(
				"{}{}",
				lbl,
				SHOW_IDS
					.then(|| format!("#{}", self.id))
					.unwrap_or_default()
			)
		} else {
			format!("x#{}", self.id)
		}
	}

	/// Constructs (one or more) IntVar `ys` for linear expression `xs` so that ∑ xs ≦ ∑ ys
	#[allow(private_interfaces)]
	pub fn from_part<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		model: &mut Model<DB::Lit, C>,
		xs: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
		lbl: String,
	) -> Result<IntVarRef<Lit, C>, Unsatisfiable> {
		match xs {
			Part::Amo(terms) => {
				let terms: Vec<(PosCoeff<C>, Lit)> = terms
					.iter()
					.map(|(lit, coef)| (coef.clone(), lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: FxHashMap<C, Vec<Lit>> =
					FxHashMap::with_capacity_and_hasher(terms.len(), BuildHasherDefault::default());
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(*coef).or_default().push(lit);
				}

				let (dom, lits): (Vec<_>, Vec<_>) = h
					.into_iter()
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					// .tuple_windows()
					// .map(|((prev, _), (coef, lits))| {
					.map(|(coef, lits)| {
						// let interval = (prev + C::one())..(coef + C::one());
						if lits.is_empty() {
							(coef, None)
						} else if lits.len() == 1 {
							(coef, Some(lits[0].clone()))
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								emit_clause!(db, &[lit.negate(), o.clone()]).unwrap();
							}
							(coef, Some(o))
						}
					})
					.unzip();
				model.new_var(
					&[C::zero()].into_iter().chain(dom).collect_vec(),
					false,
					Some(IntVarEnc::Ord(Some(OrdEnc::from_lits(
						&lits.iter().flatten().cloned().collect_vec(),
					)))),
					Some(lbl),
				)
				// Ok(model)
				// let x = IntVar::<Lit, C>::new(1, &[2, 5, 6, 7, 9], true, None, Some(String::from("x")))
				// vec![IntVarEnc::Ord(OrdEnc::from_views(db, dom, lbl))]
				// vec![IntVar::new()]
			}
			// Leaves built from Ic/Dom groups are guaranteed to have unique values
			Part::Ic(_terms) => {
				todo!();
				/*
				let mut acc = C::zero(); // running sum
				let (dom, lits): (Vec<_>, Vec<_>) =
					std::iter::once(&(terms[0].0.clone(), C::zero().into()))
						.chain(terms.iter())
						.map(|(lit, coef)| {
							acc += **coef;
							debug_assert!(acc <= *ub);
							(acc, lit.clone())
						})
						.tuple_windows()
						.map(|((prev, _), (coef, lit))| {
							// ((prev + C::one())..(coef + C::one()), Some(lit))
							(coef, Some(lit))
						})
						.unzip();
				model.new_var(
					&dom,
					false,
					Some(IntVarEnc::Ord(Some(OrdEnc::from_lits(
						&lits.iter().flatten().cloned().collect_vec(),
					)))),
					Some(lbl),
				)
				// Ok(model)
				// vec![IntVarEnc::Ord(IntVarOrd::from_views(db, dom, lbl))]
				*/
			}
			Part::Dom(_terms, _l, _u) => {
				todo!();
				// TODO account for bounds (or even better, create IntVarBin)
				/*
				const COUPLE_DOM_PART_TO_ORD: bool = false;
				if COUPLE_DOM_PART_TO_ORD {
					// TODO old method (which at least respected bounds)
					let x_bin = IntVarBin::from_terms(
						terms.to_vec(),
						l.clone(),
						u.clone(),
						String::from("x"),
					);
					let x_ord = IntVarEnc::Ord(IntVarOrd::from_bounds(
						db,
						x_bin.lb(),
						x_bin.ub(),
						String::from("x"),
					));

					TernLeEncoder::default()
						.encode(
							db,
							&TernLeConstraint::new(
								&x_ord,
								&IntVarEnc::Const(C::zero()),
								&Comparator::LessEq,
								&x_bin.into(),
							),
						)
						.unwrap();
					vec![x_ord]
				} else {
					terms
						.iter()
						.enumerate()
						.map(|(i, (lit, coef))| {
							IntVarEnc::Ord(IntVarOrd::from_views(
								db,
								interval_map! { C::one()..(**coef+C::one()) => Some(lit.clone()) },
								format!("{lbl}^{i}"),
							))
						})
						.collect()
				}
				*/
			} // TODO Not so easy to transfer a binary encoded int var
			  // Part::Dom(terms, l, u) => {
			  // let coef = (terms[0].1);
			  // let false_ if (coef > 1).then(|| let false_ = Some(new_var!(db)); emit_clause!(&[-false_]); false_ });
			  // let terms = (1..coef).map(|_| false_.clone()).chain(terms.to_vec());

			  // IntVarEnc::Bin(IntVarBin::from_terms(
			  // 	terms.to_vec(),
			  // 	l.clone(),
			  // 	u.clone(),
			  // 	String::from("x"),
			  // ))},
		}
	}
}

#[cfg(test)]
mod tests {
	type Lit = i32;
	type C = i32;

	use super::*;

	use crate::helpers::tests::TestDB;

	#[test]
	fn test_ineq_ord() {
		(|| {
			let mut db = TestDB::new(0);
			let mut x = IntVar::<Lit, C>::from_dom(
				0,
				Dom::from_slice(&[5, 7, 8]),
				true,
				Some(IntVarEnc::Ord(None)),
				Some(String::from("x")),
			);
			x.encode(&mut db, None)?;
			assert_eq!(x.ineq(3, true, None), (Some(5), vec![]));
			assert_eq!(x.ineq(5, true, None), (Some(5), vec![]));
			assert_eq!(x.ineq(6, true, None), (Some(7), vec![vec![1]]));
			assert_eq!(x.ineq(8, true, None), (Some(8), vec![vec![2]]));
			assert_eq!(x.ineq(12, true, None), (None, vec![vec![]]));

			// x < k
			assert_eq!(x.ineq(3, false, None), (None, vec![vec![]]));
			assert_eq!(x.ineq(5, false, None), (None, vec![vec![]]));
			assert_eq!(x.ineq(6, false, None), (Some(5), vec![vec![-1]]));
			assert_eq!(x.ineq(7, false, None), (Some(5), vec![vec![-1]]));
			assert_eq!(x.ineq(8, false, None), (Some(7), vec![vec![-2]]));
			assert_eq!(x.ineq(12, false, None), (Some(8), vec![]));
			Ok::<_, Unsatisfiable>(())
		})()
		.unwrap();
	}

	#[test]
	fn test_ineqs_bin() {
		(|| {
			let mut db = TestDB::new(0);
			let mut x = IntVar::<Lit, C>::from_dom(
				0,
				Dom::from_slice(&[0, 1, 2, 3, 4, 5, 6, 7]),
				true,
				Some(IntVarEnc::Bin(None)),
				Some(String::from("x")),
			);
			x.encode(&mut db, None)?;
			assert_eq!(
				x.ineqs(true),
				vec![
					(7, vec![], 7),        // +0
					(6, vec![1], 6),       // +0
					(5, vec![2], 4),       // +1
					(4, vec![1, 2], 4),    // +0
					(3, vec![3], 0),       // +3
					(2, vec![1, 3], 2),    // +0
					(1, vec![2, 3], 0),    // +0
					(0, vec![1, 2, 3], 0)  // +0
				]
			);

			assert_eq!(
				x.ineqs(false),
				vec![
					(0, vec![], 0),           // +0
					(1, vec![-1], 1),         // +0
					(2, vec![-2], 3),         // +0
					(3, vec![-1, -2], 3),     // +3
					(4, vec![-3], 7),         // +0
					(5, vec![-1, -3], 5),     // +1
					(6, vec![-2, -3], 7),     // +0
					(7, vec![-1, -2, -3], 7), // +0
				]
			);
			Ok::<_, Unsatisfiable>(())
		})()
		.unwrap();
	}

}
