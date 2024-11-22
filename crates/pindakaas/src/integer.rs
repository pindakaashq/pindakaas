use crate::bool_linear::BoolLinExp;
use crate::bool_linear::Part;
use crate::bool_linear::PosCoeff;
use crate::helpers::as_binary;
use crate::helpers::emit_clause;
use crate::helpers::emit_filtered_clause;
use crate::helpers::new_var;
use crate::int::enc::IntVarEnc;
use crate::int::required_lits;
use crate::int::Dom;
use crate::int::LitOrConst;
use crate::int::Model;
use crate::int::{BinEnc, OrdEnc};
use crate::CheckError;

use itertools::Itertools;
use rustc_hash::FxBuildHasher;
use rustc_hash::FxHashMap;

use crate::{
	helpers::negate_cnf, int::display::SHOW_IDS, ClauseDatabase, Coeff, Lit, Result, Unsatisfiable,
	Valuation, Var,
};

use std::{cell::RefCell, collections::BTreeSet, fmt::Display, rc::Rc};

pub type IntVarRef = Rc<RefCell<IntVar>>;

impl Display for IntVarId {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

#[derive(Hash, Copy, Clone, Debug, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct IntVarId(pub usize);

#[derive(Debug, Clone, Default)]
pub struct IntVar {
	pub id: IntVarId,
	pub dom: Dom,
	pub(crate) add_consistency: bool,
	pub(crate) e: Option<IntVarEnc>,
	pub(crate) lbl: Option<String>,
}

// TODO implement Eq so we don't compare .e

impl IntVar {
	pub(crate) fn new_constant(c: Coeff) -> IntVarRef {
		Self::from_dom_as_ref(0, Dom::constant(c), true, Some(IntVarEnc::Bin(None)), None)
	}

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
			e,
			lbl,
		}
	}

	#[cfg_attr(
		feature = "tracing",
		tracing::instrument(name = "consistency", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB) -> Result {
		self.e
			.as_ref()
			.map(|e| e.consistent(db, &self.dom))
			.unwrap_or(Ok(()))
	}

	/// Returns (d,cnf,c) where cnf encodes x>=d, which implies up to x>=c,x>=c+1,..,x>=d
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
		match self.e.as_ref().unwrap() {
			IntVarEnc::Ord(Some(o)) => {
				let pos = self.dom.geq(k);
				println!(" = d_{pos:?}");
				let d = if let Some((pos, v)) = pos {
					if up {
						Some(v)
					} else {
						pos.checked_sub(1).and_then(|next_pos| self.dom.d(next_pos))
					}
				} else if up {
					None
				} else {
					Some(self.dom.ub())
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

				println!("{r_a}..{r_b} ");
				let dnf = x_bin.geqs(r_a, r_b);

				let dnf = if up {
					dnf
				} else {
					// negate dnf
					// TODO Move dnf/cnf: Vec<Vec<Lit>> functions into Cnf
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

	pub(crate) fn as_lin_exp(&self) -> BoolLinExp {
		match self
			.e
			.as_ref()
			.unwrap_or_else(|| panic!("Expected {self} to be encoded"))
		{
			IntVarEnc::Ord(Some(o)) => {
				BoolLinExp::default()
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

				let lin_exp = BoolLinExp::default().add_bounded_log_encoding(
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
		let assignment = BoolLinExp::from(self).assign(a)?;
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

	pub(crate) fn lits(&self) -> BTreeSet<Var> {
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

	// TODO [!] only updated for Amo
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
					FxHashMap::with_capacity_and_hasher(terms.len(), FxBuildHasher);
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(coef).or_default().push(lit);
				}

				let (dom, lits): (Vec<_>, Vec<_>) = h
					.into_iter()
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					.map(|(coef, lits)| {
						let coef = *coef;
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
				model.new_aux_var(
					Dom::from_slice(&[0].into_iter().chain(dom).collect_vec()),
					false,
					Some(IntVarEnc::Ord(Some(OrdEnc::from_lits(
						&lits.iter().flatten().cloned().collect_vec(),
					)))),
					Some(lbl),
				)
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

/// Uses lexicographic constraint to constrain x:B ≦ k
#[cfg_attr(
	feature = "tracing",
	tracing::instrument(name = "lex_leq_const", skip_all, fields(constraint = format!("{x:?} <= {k}")))
)]
pub(crate) fn lex_leq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	k: PosCoeff,
	bits: usize,
) -> Result {
	// For every zero bit in k:
	// - either the `x` bit is also zero, or
	// - a higher `x` bit is zero that was one in k.
	let k = as_binary(k, Some(bits));

	(0..bits)
		.filter(|i| !k.get(*i).unwrap_or(&false))
		.try_for_each(|i| {
			emit_filtered_clause(
				db,
				(i..bits)
					.filter(|j| (*j == i || *k.get(*j).unwrap_or(&false)))
					.map(|j| !x[j])
					.collect_vec(),
			)
		})
}

/// Uses lexicographic constraint to constrain x:B >= k
#[cfg_attr(
	feature = "tracing",
	tracing::instrument(name = "lex_geq_const", skip_all, fields(constraint = format!("{x:?} >= {k} over {bits} bits")))
)]
pub(crate) fn lex_geq_const<DB: ClauseDatabase>(
	db: &mut DB,
	x: &[LitOrConst],
	k: PosCoeff,
	bits: usize,
) -> Result {
	let k = as_binary(k, Some(bits));

	(0..bits)
		.filter(|i| *k.get(*i).unwrap_or(&false))
		.try_for_each(|i| {
			emit_filtered_clause(
				db,
				(i..bits)
					.filter(|j| (*j == i || !k.get(*j).unwrap_or(&false)))
					.map(|j| x[j])
					.collect_vec(),
			)
		})
}

// TODO implement for given false carry
#[cfg_attr(feature = "tracing", tracing::instrument(name = "carry", skip_all, fields(constraint = format!("{xs:?} >= 2"))))]
fn carry<DB: ClauseDatabase>(db: &mut DB, xs: &[LitOrConst], _lbl: String) -> Result<LitOrConst> {
	// The carry is true iff at least 2 out of 3 `xs` are true
	let (xs, trues) = filter_fixed_sum(xs);
	let carry = match &xs[..] {
		[] => (trues >= 2).into(), // trues is {0,1,2,3}
		[x] => match trues {
			0 => false.into(),
			1 => (*x).into(),
			2 => true.into(),
			_ => unreachable!(),
		},
		[x, y] => match trues {
			0 => {
				let and = new_var!(db, _lbl);
				emit_clause!(db, [!x, !y, and])?;
				emit_clause!(db, [*x, !and])?;
				emit_clause!(db, [*y, !and])?;
				and.into()
			}
			1 => {
				let or = new_var!(db, _lbl);
				emit_clause!(db, [*x, *y, !or])?;
				emit_clause!(db, [!x, or])?;
				emit_clause!(db, [!y, or])?;
				or.into()
			}
			_ => unreachable!(),
		},
		[x, y, z] => {
			assert!(trues == 0);
			let carry = new_var!(db, _lbl);

			emit_clause!(db, [*x, *y, !carry])?; // 2 false -> ~carry
			emit_clause!(db, [*x, *z, !carry])?; // " ..
			emit_clause!(db, [*y, *z, !carry])?;

			emit_clause!(db, [!x, !y, carry])?; // 2 true -> carry
			emit_clause!(db, [!x, !z, carry])?; // " ..
			emit_clause!(db, [!y, !z, carry])?;
			carry.into()
		}
		_ => unreachable!(),
	};
	Ok(carry)
}

fn filter_fixed_sum(xs: &[LitOrConst]) -> (Vec<Lit>, usize) {
	let mut trues = 0;
	(
		xs.iter()
			.filter_map(|x| match x {
				LitOrConst::Lit(l) => Some(*l),
				LitOrConst::Const(true) => {
					trues += 1;
					None
				}
				LitOrConst::Const(false) => None,
			})
			.collect(),
		trues,
	)
}

#[cfg_attr(feature = "tracing", tracing::instrument(name = "xor", skip_all, fields(constraint = format!("(+) {xs:?}"))))]
fn xor<DB: ClauseDatabase>(db: &mut DB, xs: &[LitOrConst], _lbl: String) -> Result<LitOrConst> {
	let (xs, trues) = filter_fixed_sum(xs);

	let is_even = match &xs[..] {
		[] => LitOrConst::Const(false), // TODO why not `true`?
		[x] => LitOrConst::Lit(*x),
		[x, y] => {
			assert!(trues <= 1);
			let is_even = new_var!(db, _lbl);

			emit_clause!(db, [*x, *y, !is_even])?; // 0
			emit_clause!(db, [!x, !y, !is_even])?; // 2

			emit_clause!(db, [!x, *y, is_even])?; // 1
			emit_clause!(db, [*x, !y, is_even])?; // 1
			LitOrConst::Lit(is_even)
		}
		[x, y, z] => {
			assert!(trues == 0);
			let is_even = new_var!(db, _lbl);

			emit_clause!(db, [*x, *y, *z, !is_even])?; // 0
			emit_clause!(db, [*x, !y, !z, !is_even])?; // 2
			emit_clause!(db, [!x, *y, !z, !is_even])?; // 2
			emit_clause!(db, [!x, !y, *z, !is_even])?; // 2

			emit_clause!(db, [!x, !y, !z, is_even])?; // 3
			emit_clause!(db, [!x, *y, *z, is_even])?; // 1
			emit_clause!(db, [*x, !y, *z, is_even])?; // 1
			emit_clause!(db, [*x, *y, !z, is_even])?; // 1
			LitOrConst::Lit(is_even)
		}
		_ => unimplemented!(),
	};

	// If trues is odd, negate sum
	Ok(if trues % 2 == 0 { is_even } else { !is_even })
}

// TODO [?] functional version has duplication with relational version
#[cfg_attr(feature = "tracing", tracing::instrument(name = "log_enc_add", skip_all, fields(constraint = format!("[{}] + [{}] = ", xs.iter().rev().map(|x| format!("{x}")).collect_vec().join(","), ys.iter().rev().map(|x| format!("{x}")).collect_vec().join(",")))))]
pub(crate) fn log_enc_add_fn<DB: ClauseDatabase>(
	db: &mut DB,
	xs: &[LitOrConst],
	ys: &[LitOrConst],
	bits: Option<usize>,
) -> Result<Vec<LitOrConst>> {
	let max_bits = itertools::max([xs.len(), ys.len()]).unwrap() + 1;
	let bits = bits.unwrap_or(max_bits);
	let mut c = LitOrConst::Const(false);

	let zs = (0..bits)
		.map(|i| {
			let (x, y) = (bit(xs, i), bit(ys, i));
			let z = xor(db, &[x, y, c], format!("z_{}", i)); // sum
			c = carry(db, &[x, y, c], format!("c_{}", i + 1))?; // carry
			z
		})
		.collect::<Result<Vec<_>>>()?;

	// TODO avoid c being created by constraining (x+y+c >= 2 ) <-> false in last iteration if bits<max_bits
	// prevent overflow;
	// TODO this should just happen for all c_i's for bits < i <= max_bits
	if bits < max_bits {
		if let LitOrConst::Lit(c) = c {
			emit_clause!(db, [!c])?;
		}
	}

	// TODO If lasts lits are equal, it could mean they can be truncated (at least true for 2-comp)? But then they might return unexpected number of bits in some cases. Needs thinking.
	Ok(zs)
}

fn bit(x: &[LitOrConst], i: usize) -> LitOrConst {
	*x.get(i).unwrap_or(&LitOrConst::Const(false))
}
