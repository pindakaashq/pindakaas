use std::str::FromStr;

use super::model::Scm;
use crate::Cnf;

include!(concat!(env!("OUT_DIR"), "/scm_db.rs"));

#[derive(Debug, Clone)]
pub(super) struct ScmNode {
	pub i: usize,
	pub i1: usize,
	pub sh1: u32,
	pub add: bool,
	pub i2: usize,
	pub sh2: u32,
}

// const SCM: ScmDB = ScmDB {
// 	scm: phf::Map::new(),
// 	ecm: phf::Map::new(),
// };

// TODO move to new scm.rs module
impl ScmDB {
	pub(crate) fn get(&self, lits: usize, c: i64, scm: &Scm) -> Option<&[ScmNode]> {
		match scm {
			#[cfg(feature = "scm")]
			Scm::Add => self.scm.get(&format!("{lits}_{c}")).cloned(),
			#[cfg(feature = "scm")]
			Scm::Rca => self.scm.get(&format!("0_{c}")).cloned(),
			#[allow(unreachable_patterns, reason = "reachable if scm enabled")]
			_ => unreachable!(),
		}
	}
	// TODO merge with above
	pub(crate) fn ecm(&self, lits: usize, c: i64) -> Option<Cnf> {
		self.ecm
			.get(&format!("{lits}_{c}"))
			.map(|s| Cnf::from_str(s).unwrap())
	}
}

#[derive(Debug, Default)]
pub(crate) struct ScmDB {
	pub(crate) scm: phf::Map<&'static str, &'static [ScmNode]>,
	pub(crate) ecm: phf::Map<&'static str, &'static str>,
}
