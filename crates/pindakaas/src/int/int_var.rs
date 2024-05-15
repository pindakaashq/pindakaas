use std::{
	cell::RefCell,
	collections::{HashMap, HashSet},
	fmt::Display,
	hash::BuildHasherDefault,
	rc::Rc,
};

use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::{bin::BinEnc, model::PRINT_COUPLING, ord::OrdEnc, required_lits, Dom, IntVarEnc};
use crate::{
	helpers::negate_cnf,
	int::display::SHOW_IDS,
	linear::{Part, PosCoeff},
	trace::{emit_clause, new_var},
	CheckError, ClauseDatabase, Coeff, Lit, Model, Result, Unsatisfiable, Valuation, Var,
};

#[derive(Hash, Copy, Clone, Debug, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct IntVarId(pub usize);

pub type IntVarRef = Rc<RefCell<IntVar>>;

impl Display for IntVarId {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}
// TODO perhaps id can be used by replacing vars HashMap to just vec
// TODO why can't we derive Default without impl. for Lit (since it's in Option?)
#[derive(Debug, Clone)]
pub struct IntVar {
	pub id: IntVarId,
	pub dom: Dom,
	pub(crate) add_consistency: bool,
	pub(crate) views: HashMap<Coeff, (IntVarId, Coeff)>,
	pub(crate) e: Option<IntVarEnc>,
	pub(crate) lbl: Option<String>,
}

// TODO implement Eq so we don't compare .e

impl IntVar {
	pub(crate) fn from_dom_as_ref(
		id: usize,
		dom: Dom,
		add_consistency: bool,
		e: Option<IntVarEnc>,
		lbl: Option<String>,
	) -> IntVarRef {
		Rc::new(RefCell::new(Self::from_dom(
			id,
			dom,
			add_consistency,
			e,
			lbl,
		)))
	}

	pub(crate) fn from_dom(
		id: usize,
		dom: Dom,
		add_consistency: bool,
		e: Option<IntVarEnc>,
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
	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB) -> Result {
		self.e
			.as_ref()
			.map(|e| e.consistent(db, &self.dom))
			.unwrap_or(Ok(()))
	}

	pub fn ineqs(&self, up: bool) -> Vec<(Coeff, Vec<Lit>, Coeff)> {
		let ineqs = |es: Vec<Vec<Lit>>, dom: Dom, up: bool| {
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
							.map(|clause| clause.into_iter().map(|l| !l).collect()),
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
						if up {
							self.lb()
						} else {
							self.ub()
						}
					} else {
						c
					},
				)
			})
			.collect(),
			IntVarEnc::Bin(Some(x_bin)) => {
				// TODO not (particularly) optimized for the domain of x, but this is tricky as the domain values go outside the binary encoding ranges
				let (range_lb, range_ub) = x_bin.range();

				ineqs(
					(range_lb..=(range_ub - 1))
						.map(|k| x_bin.geq(if up { range_ub - k } else { k + 1 }))
						.collect(),
					Dom::from_bounds(range_lb, range_ub).add(self.lb()), // denormalize
					up,
				)
				.map(|(c, cnf)| {
					(c, cnf, {
						let k = if up { range_ub - c } else { c };
						// let k = range_ub - c;
						let k = x_bin.normalize(k, &self.dom);
						let a = x_bin.geq_implies(*k);
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
	pub fn ineq(&self, k: Coeff, up: bool, a: Option<Coeff>) -> (Option<Coeff>, Vec<Vec<Lit>>) {
		// TODO move into IntVar since self.c is taken care off?
		match self.e.as_ref().unwrap() {
			IntVarEnc::Ord(Some(o)) => {
				// TODO make use of a?
				let pos = self.dom.geq(k);
				if PRINT_COUPLING >= 2 {
					print!(" = d_{pos:?}");
				}
				let d = if let Some((pos, v)) = pos {
					if up {
						// Some(pos) // if larger than self.dom.size, then self.dom.d will return None
						Some(v)
					} else {
						pos.checked_sub(1).and_then(|next_pos| self.dom.d(next_pos))
					}
				// pos.and_then(|next_pos| self.dom.d(next_pos))
				} else {
					// TODO not sure if this should be ub/lb or None. This makes most sense looking at the test ineq_ord
					if up {
						None
					} else {
						Some(self.dom.ub())
					}
				};
				let geq = o.geq(pos.map(|(pos, _)| pos));
				(d, if up { geq } else { negate_cnf(geq) })
			}
			IntVarEnc::Bin(Some(x_bin)) => {
				// x>=k == ¬(x<k) == ¬(x<=k-1) (or x<=k == ¬(x>k) == ¬(x>=k+1))
				// or: x>=k == x>=(2^bits - k)
				// returns Dnf e.q. (x1 \/ x0 /\ x0)
				// x1 /\ x0 -> x>=3 -> x0 \/ x2

				let (range_lb, range_ub) = x_bin.range();
				let (k, a) = (
					*x_bin.normalize(k, &self.dom),
					a.map(|a| *x_bin.normalize(a, &self.dom))
						.unwrap_or(range_ub),
				);
				let (r_a, r_b) = if up {
					// x>=k \/ x>=k+1 \/ .. \/ x>=r_b
					(range_ub + 1 - k, a)
				} else {
					(range_lb + k, a)
				};

				if PRINT_COUPLING >= 2 {
					print!("{r_a}..{r_b} ");
				}
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

			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}

	pub(crate) fn as_lin_exp(&self) -> crate::linear::LinExp {
		match self
			.e
			.as_ref()
			.unwrap_or_else(|| panic!("Expected {self} to be encoded"))
		{
			IntVarEnc::Ord(Some(o)) => {
				crate::linear::LinExp::default()
					.add_chain(
						&self
							.dom
							.iter()
							.zip(o.ineqs(true))
							.tuple_windows()
							// Every lit adds the difference
							.map(|((prev, (_, _)), (v, (cnf, _)))| (cnf[0][0], v - prev))
							.collect::<Vec<_>>(),
					)
					.add_constant(self.lb())
			}
			IntVarEnc::Bin(Some(b)) => {
				let (terms, add) = b.as_lin_exp();
				// The offset and the fixed value `add` are added to the constant
				let add = add + self.lb();
				let (lb, ub) = (add, self.ub() - self.lb() + add);

				let lin_exp = crate::linear::LinExp::default().add_bounded_log_encoding(
					terms.as_slice(),
					// The Domain constraint bounds only account for the unfixed part of the offset binary notation
					lb,
					ub,
				);
				lin_exp.add_constant(add)
			}
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}

	pub fn assign<F: Valuation + ?Sized>(&self, a: &F) -> Result<Coeff, CheckError> {
		let assignment = crate::linear::LinExp::from(self).assign(a)?;
		if self.add_consistency && !self.dom.contains(assignment) {
			Err(CheckError::Fail(format!(
				"Inconsistent var assignment on consistent var: {} -> {:?}",
				self, assignment
			)))
		} else {
			Ok(assignment)
		}
	}

	pub fn is_constant(&self) -> bool {
		self.size() == 1
	}

	pub(crate) fn lits(&self) -> HashSet<Var> {
		self.e.as_ref().map(|e| e.lits()).unwrap_or_default()
	}

	pub(crate) fn encode_ord<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
	) -> Result<OrdEnc, Unsatisfiable> {
		self.encode(db).map(|e| match e {
			IntVarEnc::Ord(Some(o)) => o,
			_ if self.is_constant() => OrdEnc::from_lits(&[]),
			_ => panic!("encode_ord called without binary encoding for {self}"),
		})
	}

	pub(crate) fn encode_bin<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
	) -> Result<BinEnc, Unsatisfiable> {
		self.encode(db).map(|e| match e {
			IntVarEnc::Bin(Some(b)) => b,
			_ if self.is_constant() => BinEnc::from_lits(&[]),
			_ => panic!("encode_bin called without binary encoding for {self}"),
		})
	}

	// pub(crate) fn constant(k: Coeff) -> Int{
	// 	OrdEnc::from_lits(&[])
	// }

	pub(crate) fn encode<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
	) -> Result<IntVarEnc, Unsatisfiable> {
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
				required_lits(self.dom.lb(), self.dom.ub()),
				self.lbl.clone(),
			))),
		};

		self.e = Some(e.clone());

		if self.add_consistency {
			self.consistent(db)?;
		}

		Ok(e)
	}

	pub(crate) fn ge(&mut self, bound: Coeff) {
		self.dom.ge(bound);
	}

	pub(crate) fn le(&mut self, bound: Coeff) {
		self.dom.le(bound);
	}

	pub(crate) fn size(&self) -> Coeff {
		self.dom.size()
	}

	pub fn lb(&self) -> Coeff {
		self.dom.lb()
	}

	pub fn ub(&self) -> Coeff {
		self.dom.ub()
	}

	pub(crate) fn decide_encoding(&mut self, cutoff: Option<Coeff>) -> IntVarEnc {
		if let Some(e) = self.e.as_ref() {
			return e.clone();
		}
		self.e = Some(match cutoff {
			None => IntVarEnc::Ord(None),
			Some(0) => IntVarEnc::Bin(None),
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
	pub(crate) fn from_part<DB: ClauseDatabase>(
		db: &mut DB,
		model: &mut Model,
		xs: &Part,
		ub: PosCoeff,
		lbl: String,
	) -> Result<IntVarRef, Unsatisfiable> {
		match xs {
			Part::Amo(terms) => {
				let terms = terms.iter().map(|(lit, coef)| (*coef, *lit)).collect_vec();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: FxHashMap<PosCoeff, Vec<Lit>> =
					FxHashMap::with_capacity_and_hasher(terms.len(), BuildHasherDefault::default());
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(coef).or_default().push(lit);
				}

				let (dom, lits): (Vec<_>, Vec<_>) = h
					.into_iter()
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					// .tuple_windows()
					// .map(|((prev, _), (coef, lits))| {
					.map(|(coef, lits)| {
						// let interval = (prev + C::one())..(coef + C::one());
						let coef = *coef; // dom uses Coeff
						if lits.is_empty() {
							(coef, None)
						} else if lits.len() == 1 {
							(coef, Some(lits[0]))
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								emit_clause!(db, [!lit, o]).unwrap();
							}
							(coef, Some(o))
						}
					})
					.unzip();
				model.new_var(
					&[0].into_iter().chain(dom).collect_vec(),
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
				let mut acc = 0; // running sum
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
							// ((prev + 1)..(coef + 1), Some(lit))
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
								interval_map! { 1..(**coef+1) => Some(lit.clone()) },
								format!("{lbl}^{i}"),
							))
						})
						.collect()
				}
				*/
			} // TODO Not so easy to transfer a binary encoded int var
			  // Part::Dom(terms, l, u) => {
			  // let coef = (terms[0].1);
			  // let false_ if (coef > 1).then(|| let false_ = Some(new_var!(db)); emit_clause!([-false_]); false_ });
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
	use super::*;
	use crate::helpers::tests::{lits, TestDB};

	#[test]
	fn test_ineq_ord() {
		(|| {
			let mut db = TestDB::new(0);
			let mut x = IntVar::from_dom(
				0,
				Dom::from_slice(&[5, 7, 8]),
				true,
				Some(IntVarEnc::Ord(None)),
				Some(String::from("x")),
			);
			x.encode(&mut db)?;

			assert_eq!(x.ineq(3, true, None), (Some(5), vec![]));
			assert_eq!(x.ineq(5, true, None), (Some(5), vec![]));
			assert_eq!(x.ineq(6, true, None), (Some(7), vec![lits![1]]));
			assert_eq!(x.ineq(8, true, None), (Some(8), vec![lits![2]]));
			assert_eq!(x.ineq(12, true, None), (None, vec![lits![]]));

			// // x < k
			assert_eq!(x.ineq(3, false, None), (None, vec![vec![]]));
			assert_eq!(x.ineq(5, false, None), (None, vec![vec![]]));
			assert_eq!(x.ineq(6, false, None), (Some(5), vec![lits![-1]]));
			assert_eq!(x.ineq(7, false, None), (Some(5), vec![lits![-1]]));
			assert_eq!(x.ineq(8, false, None), (Some(7), vec![lits![-2]]));
			assert_eq!(x.ineq(12, false, None), (Some(8), vec![]));
			Ok::<_, Unsatisfiable>(())
		})()
		.unwrap();
	}

	#[test]
	fn test_ineqs_bin() {
		(|| {
			let mut db = TestDB::new(0);
			let mut x = IntVar::from_dom(
				0,
				Dom::from_slice(&[0, 1, 2, 3, 4, 5, 6, 7]),
				true,
				Some(IntVarEnc::Bin(None)),
				Some(String::from("x")),
			);
			x.encode(&mut db)?;
			assert_eq!(
				x.ineqs(true),
				vec![
					(7, lits![], 7),        // +0
					(6, lits![1], 6),       // +0
					(5, lits![2], 4),       // +1
					(4, lits![1, 2], 4),    // +0
					(3, lits![3], 0),       // +3
					(2, lits![1, 3], 2),    // +0
					(1, lits![2, 3], 0),    // +0
					(0, lits![1, 2, 3], 0)  // +0
				]
			);

			assert_eq!(
				x.ineqs(false),
				vec![
					(0, lits![], 0),           // +0
					(1, lits![-1], 1),         // +0
					(2, lits![-2], 3),         // +0
					(3, lits![-1, -2], 3),     // +3
					(4, lits![-3], 7),         // +0
					(5, lits![-1, -3], 5),     // +1
					(6, lits![-2, -3], 7),     // +0
					(7, lits![-1, -2, -3], 7), // +0
				]
			);
			Ok::<_, Unsatisfiable>(())
		})()
		.unwrap();
	}
}
