#![allow(unused_imports, unused_variables, dead_code)]
use std::{
	collections::HashSet,
	fmt,
	fmt::Display,
	hash::BuildHasherDefault,
	ops::{Not, Range},
};

use iset::{interval_map, interval_set, IntervalMap, IntervalSet};
use itertools::Itertools;
use rustc_hash::FxHashMap;

use super::{bin::BinEnc, ord::OrdEnc};
use crate::{
	helpers::{as_binary, is_powers_of_two, negate_cnf},
	int::{
		helpers::{filter_fixed, required_lits},
		Dom, IntVar,
	},
	linear::{lex_geq_const, lex_leq_const, LinExp, Part, PosCoeff},
	trace::{emit_clause, new_var},
	CheckError, Checker, ClauseDatabase, Cnf, Coeff, Encoder, Lit, Result, Unsatisfiable,
	Valuation, Var,
};

#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum LitOrConst {
	Lit(Lit),
	Const(bool),
}

impl From<LitOrConst> for Vec<Vec<Lit>> {
	fn from(a: LitOrConst) -> Vec<Vec<Lit>> {
		match a {
			LitOrConst::Lit(l) => vec![vec![l]],
			LitOrConst::Const(true) => vec![],
			LitOrConst::Const(false) => vec![vec![]],
		}
	}
}

impl From<Option<Lit>> for LitOrConst {
	fn from(item: Option<Lit>) -> Self {
		match item {
			Some(l) => LitOrConst::Lit(l),
			None => LitOrConst::Const(false),
		}
	}
}

impl From<Lit> for LitOrConst {
	fn from(item: Lit) -> Self {
		LitOrConst::Lit(item)
	}
}

impl From<bool> for LitOrConst {
	fn from(item: bool) -> Self {
		LitOrConst::Const(item)
	}
}

impl TryFrom<LitOrConst> for bool {
	type Error = ();
	fn try_from(item: LitOrConst) -> Result<Self, Self::Error> {
		match item {
			LitOrConst::Const(b) => Ok(b),
			_ => Err(()),
		}
	}
}

impl Display for LitOrConst {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			LitOrConst::Const(b) => write!(f, "{}", if *b { "T" } else { "F" }),
			LitOrConst::Lit(l) => write!(f, "{l:?}"),
		}
	}
}

impl Not for LitOrConst {
	type Output = LitOrConst;
	fn not(self) -> Self::Output {
		match self {
			LitOrConst::Lit(l) => (!l).into(),
			LitOrConst::Const(b) => (!b).into(),
		}
	}
}

#[derive(Debug, Clone)]
pub enum IntVarEnc {
	Ord(Option<OrdEnc>),
	Bin(Option<BinEnc>),
}

// pub(crate) enum IntVarEnc {
// 	Ord(IntVarOrd),
// 	Bin(IntVarBin),
// }

const COUPLE_DOM_PART_TO_ORD: bool = false;

impl IntVarEnc {
	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB, dom: &Dom) -> Result {
		match self {
			IntVarEnc::Ord(Some(o)) => o.consistent(db),
			IntVarEnc::Bin(Some(b)) => b.consistent(db, dom),
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}
	// pub(crate) fn constant(k: Coeff) -> Self {
	// 	IntVarEnc::Ord(Some(OrdEnc::from_lits(&[])))
	// }

	/*
		/// Constructs (one or more) IntVar `ys` for linear expression `xs` so that ∑ xs ≦ ∑ ys
		pub fn from_part<DB: ClauseDatabase>(
			db: &mut DB,
			xs: &Part,
			ub: PosCoeff,
			lbl: String,
		) -> Vec<Self> {
			match xs {
				Part::Amo(terms) => {
					let terms: Vec<(Coeff, Lit)> = terms
						.iter()
						.copied()
						.map(|(lit, coef)| (*coef, lit))
						.collect();
					// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
					let mut h: FxHashMap<Coeff, Vec<Lit>> =
						FxHashMap::with_capacity_and_hasher(terms.len(), BuildHasherDefault::default());
					for (coef, lit) in terms {
						debug_assert!(coef <= *ub);
						h.entry(coef).or_default().push(lit);
					}

					let dom = std::iter::once((0, vec![]))
						.chain(h)
						.sorted_by(|(a, _), (b, _)| a.cmp(b))
						.tuple_windows()
						.map(|((prev, _), (coef, lits))| {
							let interval = (prev + 1)..(coef + 1);
							if lits.len() == 1 {
								(interval, Some(lits[0]))
							} else {
								let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
								for lit in lits {
									emit_clause!(db, [!lit, o]).unwrap();
								}
								(interval, Some(o))
							}
						})
						.collect::<IntervalMap<_, _>>();
					vec![IntVarEnc::Ord(IntVarOrd::from_views(db, dom, lbl))]
				}
				// Leaves built from Ic/Dom groups are guaranteed to have unique values
				Part::Ic(terms) => {
					let mut acc = 0; // running sum
					let dom = std::iter::once(&(terms[0].0, PosCoeff::new(0)))
						.chain(terms.iter())
						.map(|&(lit, coef)| {
							acc += *coef;
							debug_assert!(acc <= *ub);
							(acc, lit)
						})
						.tuple_windows()
						.map(|((prev, _), (coef, lit))| ((prev + 1)..(coef + 1), Some(lit)))
						.collect::<IntervalMap<_, _>>();
					vec![IntVarEnc::Ord(IntVarOrd::from_views(db, dom, lbl))]
				}
				Part::Dom(terms, l, u) => {
					// TODO account for bounds (or even better, create IntVarBin)
					// TODO old method (which at least respected bounds)
					if COUPLE_DOM_PART_TO_ORD {
						let x_bin = IntVarBin::from_terms(terms.to_vec(), *l, *u, String::from("x"));
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
									&IntVarEnc::Const(0),
									LimitComp::LessEq,
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
									interval_map! { 1..(**coef+1) => Some(*lit) },
									format!("{lbl}^{i}"),
								))
							})
							.collect()
					}
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

	*/

	/// Return set of lits in encoding
	pub(crate) fn lits(&self) -> HashSet<Var> {
		match self {
			IntVarEnc::Ord(Some(o)) => o.lits(),
			IntVarEnc::Bin(Some(b)) => b.lits(),
			_ => HashSet::default(),
		}
	}
}

impl From<BinEnc> for IntVarEnc {
	fn from(b: BinEnc) -> Self {
		Self::Bin(Some(b))
	}
}

impl From<OrdEnc> for IntVarEnc {
	fn from(o: OrdEnc) -> Self {
		Self::Ord(Some(o))
	}
}

// impl From<&IntVarEnc> for LinExp {
// 	fn from(value: &IntVarEnc) -> Self {
// 		match value {
// 			IntVarEnc::Ord(o) => o.into(),
// 			IntVarEnc::Bin(b) => b.into(),
// 		}
// 	}
// }

impl fmt::Display for IntVarEnc {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			IntVarEnc::Ord(Some(o)) => o.fmt(f),
			IntVarEnc::Bin(Some(b)) => b.fmt(f),
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}
}
pub(crate) fn ord_plus_ord_le_ord_sparse_dom(
	a: Vec<Coeff>,
	b: Vec<Coeff>,
	l: Coeff,
	u: Coeff,
) -> IntervalSet<Coeff> {
	// TODO optimize by dedup (if already sorted?)
	HashSet::<Coeff>::from_iter(a.iter().flat_map(|a| {
		b.iter().filter_map(move |b| {
			// TODO refactor: use then_some when stabilized
			if *a + *b >= l && *a + *b <= u {
				Some(*a + *b)
			} else {
				None
			}
		})
	}))
	.into_iter()
	.sorted()
	.tuple_windows()
	.map(|(a, b)| (a + 1)..(b + 1))
	.collect::<IntervalSet<_>>()
}
