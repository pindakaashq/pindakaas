use std::{collections::HashMap, num::NonZeroI32, path::PathBuf, process::Command};

use rand::{distributions::Alphanumeric, thread_rng, Rng};

use super::{SolveResult, Solver};
use crate::{ClauseDatabase, Cnf, ConditionalDatabase, Lit, Valuation, Var};

struct CmdlineSolver {
	cnf: Cnf,
}

pub(crate) struct MapSol(HashMap<Var, bool>);

impl From<Vec<Lit>> for MapSol {
	fn from(value: Vec<Lit>) -> Self {
		Self(
			value
				.into_iter()
				.map(|lit| (lit.var(), !lit.is_negated()))
				.collect::<HashMap<_, _>>(),
		)
	}
}

impl Valuation for MapSol {
	fn value(&self, lit: Lit) -> Option<bool> {
		self.0
			.get(&lit.var())
			.copied()
			.map(|a| if lit.is_negated() { !a } else { a })
	}
}

impl ClauseDatabase for CmdlineSolver {
	fn new_var(&mut self) -> Var {
		self.cnf.new_var()
	}

	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, cl: I) -> crate::Result {
		self.cnf.add_clause(cl)
	}

	type CondDB = Self;

	fn with_conditions(&mut self, _conditions: Vec<Lit>) -> ConditionalDatabase<Self::CondDB> {
		todo!()
	}
}
impl Solver for CmdlineSolver {
	type ValueFn = MapSol;

	fn signature(&self) -> &str {
		"cadical"
	}
	fn solve<SolCb: FnOnce(&Self::ValueFn)>(&mut self, on_sol: SolCb) -> SolveResult {
		const REMOVE_DIMACS: bool = true;
		let mut status: Option<SolveResult> = None;

		let dimacs = {
			let rng = thread_rng();
			let dimacs = PathBuf::from(format!(
				"{}/tmp/{}.dimacs",
				env!("CARGO_MANIFEST_DIR"),
				rng.sample_iter(&Alphanumeric)
					.take(7)
					.map(char::from)
					.collect::<String>()
			));
			std::fs::write(&dimacs, format!("{}", self.cnf)).unwrap();
			dimacs
		};

		// TODO [!] remove
		let output = Command::new("../../../cadical/build/cadical")
			.arg(&dimacs)
			.arg("-t")
			.arg("10")
			.output()
			.unwrap();

		if REMOVE_DIMACS {
			std::fs::remove_file(dimacs).unwrap();
		}

		let out = String::from_utf8(output.stdout.clone()).unwrap();
		let err = String::from_utf8(output.stderr.clone()).unwrap();
		if output.status.code().unwrap_or(-1) == -1 {
			panic!("CADICAL {}\n{}\n", out, err);
		}

		let mut sol = Vec::new();

		for line in String::from_utf8(output.stdout.clone()).unwrap().lines() {
			let mut tokens = line.split_whitespace();
			match tokens.next() {
				None | Some("c") => {
					if let Some("UNKNOWN") = tokens.next() {
						panic!("CADICAL unknown!")
					} else {
						continue;
					}
				}
				Some("s") => match tokens.next() {
					Some("SATISFIABLE") => {
						status = Some(SolveResult::Sat);
					}
					Some("UNSATISFIABLE") => {
						status = Some(SolveResult::Unsat);
					}
					Some("UNKNOWN") | Some("INDETERMINATE") => {
						status = Some(SolveResult::Unknown);
					}
					status => panic!("CADICAL Unknown status: {status:?}"),
				},
				Some("v") => {
					tokens
						.take_while(|t| *t != "0") // skip 0 delimiter
						.for_each(|t| {
							assert!(status == Some(SolveResult::Sat));
							sol.push(Lit(t.parse::<NonZeroI32>().unwrap()));
						})
					// TODO no error from solve?
				}
				line => panic!("CADICAL Unexpected slv output: {:?}", line),
			}
		}
		let status = status.unwrap_or_else(|| {
			panic!(
				"CADICAL No status set in SAT output:\n{}\n{}",
				String::from_utf8(output.stdout).unwrap(),
				String::from_utf8(output.stderr).unwrap(),
			)
		});
		on_sol(&MapSol::from(sol));
		status
	}
}

// pub fn cadical(&mut self) -> SolverResult {
// }
