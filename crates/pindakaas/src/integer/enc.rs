use std::{
	collections::BTreeSet,
	fmt::{self, Display},
	ops::Not,
};

use super::{bin::BinEnc, ord::OrdEnc};
use crate::{integer::Dom, ClauseDatabase, Lit, Result, Var};

#[derive(Copy, Clone, Debug, PartialEq)]
#[allow(
	variant_size_differences,
	reason = "TODO this might be interesting to fix in the future if we can pack true/false into Lit"
)]
pub(crate) enum LitOrConst {
	Lit(Lit),
	Const(bool),
}

impl Default for LitOrConst {
	fn default() -> Self {
		Self::Const(false)
	}
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
			LitOrConst::Lit(l) => write!(f, "{}", l),
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
pub(crate) enum IntVarEnc {
	Ord(Option<OrdEnc>),
	Bin(Option<BinEnc>),
}

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

impl Display for IntVarEnc {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			IntVarEnc::Ord(Some(o)) => o.fmt(f),
			IntVarEnc::Bin(Some(b)) => b.fmt(f),
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
	}
}
