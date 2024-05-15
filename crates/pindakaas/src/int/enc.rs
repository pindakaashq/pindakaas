#![allow(unused_imports, unused_variables, dead_code)]
use std::{
	collections::{BTreeSet, HashSet},
	fmt::{self, Display},
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

const COUPLE_DOM_PART_TO_ORD: bool = false;

impl IntVarEnc {
	pub(crate) fn consistent<DB: ClauseDatabase>(&self, db: &mut DB, dom: &Dom) -> Result {
		match self {
			IntVarEnc::Ord(Some(o)) => o.consistent(db),
			IntVarEnc::Bin(Some(b)) => b.consistent(db, dom),
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}

	/// Return set of lits in encoding
	pub(crate) fn lits(&self) -> BTreeSet<Var> {
		match self {
			IntVarEnc::Ord(Some(o)) => o.lits(),
			IntVarEnc::Bin(Some(b)) => b.lits(),
			_ => BTreeSet::default(),
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

impl fmt::Display for IntVarEnc {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			IntVarEnc::Ord(Some(o)) => o.fmt(f),
			IntVarEnc::Bin(Some(b)) => b.fmt(f),
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}
}
