use crate::bool_linear::Comparator;
use crate::helpers::is_unique;
use crate::integer::enc::IntVarEnc;
use crate::integer::term::Term;
use crate::integer::var::IntVarId;
use crate::integer::var::IntVarRef;
use crate::integer::Lin;
use crate::CheckError;
use std::collections::BTreeSet;
use std::time::Duration;
use std::time::Instant;

use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::{
	integer::IntVar,
	integer::{
		decompose::{Decompose, ModelDecomposer},
		Assignment, Dom, LinExp,
	},
	Checker, ClauseDatabase, Result, Unsatisfiable, Valuation, Var,
};

// TODO needs experiment to find out which is better
/// Replace unary constraints by coupling
pub(crate) const USE_COUPLING_IO_LEX: bool = false;

// TODO [?] this seemed like a feature, but we do not want to make it public
/// Use CSE for terms or not
pub(crate) const USE_CSE: bool = true;

// (const option because unstable implementation)
/// View coupling
pub(crate) const VIEW_COUPLING: bool = true;
/// Use channelling
pub(crate) const USE_CHANNEL: bool = false;

/// SCM methods
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Scm {
	/// Use recipe that minimizes adders. Good for ≥12 bits
	Add,
	/// Use recipe that minimizes ripple-carry-adders
	Rca,
	/// Use recipe derived by Boolean minimization (min. variables). Good for <12 bits
	#[default]
	Dnf,
	/// Use base-line pow-of-2 approach
	Pow,
}

use crate::Coeff;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Decomposer {
	Gt,
	Swc,
	#[default]
	Bdd,
	Rca,
}

/// Mixed encoding cutoff
#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Mix {
	Binary,
	Mix(Coeff),
	#[default]
	Order,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ModelConfig {
	/// Which SCM method to use
	pub scm: Scm,
	pub cutoff: Mix,
	pub decomposer: Decomposer,
	/// Rewrites all but last equation x:B + y:B ≤ z:B to x:B + y:B = z:B
	pub equalize_ternaries: bool,
	pub add_consistency: bool,
	pub propagate: Consistency,
	/// Rewrites x:B + y:B ≤ z:B to x:B + y:B = z':B ∧ y:B ≤ z:B
	pub equalize_uniform_bin_ineqs: bool,
}

#[derive(Debug, Clone)]
pub struct Model {
	pub cons: Vec<Lin>,
	pub num_var: usize,
	pub obj: Obj,
	pub config: ModelConfig,
	pub cse: Cse,
}

impl From<Lin> for Model {
	fn from(con: Lin) -> Self {
		Model {
			cons: vec![con],
			..Model::default()
		}
	}
}

impl From<Vec<Lin>> for Model {
	fn from(cons: Vec<Lin>) -> Self {
		Model {
			cons,
			..Model::default()
		}
	}
}

#[derive(Default, Debug, Clone)]
pub struct Cse(pub FxHashMap<(IntVarId, Coeff, Comparator), Term>);

#[derive(Debug, Default, Clone, Copy, Ord, PartialOrd, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Consistency {
	#[default]
	None,
	Bounds,
	Domain,
}

#[derive(Default, Debug, Clone)]
pub enum Obj {
	#[default]
	Satisfy,
	Minimize(LinExp),
	Maximize(LinExp),
}

impl Obj {
	pub fn obj(&self) -> Option<&LinExp> {
		match self {
			Obj::Minimize(exp) | Obj::Maximize(exp) => Some(exp),
			Obj::Satisfy => None,
		}
	}

	pub fn is_satisfy(&self) -> bool {
		matches!(self, Obj::Satisfy)
	}

	pub fn is_maximize(&self) -> bool {
		matches!(self, Obj::Maximize(_))
	}
}

impl Extend<Model> for Model {
	fn extend<T: IntoIterator<Item = Model>>(&mut self, iter: T) {
		for model in iter {
			self.num_var = model.num_var;
			self.cons.extend(model.cons);
		}
	}
}

impl FromIterator<Model> for Model {
	fn from_iter<I: IntoIterator<Item = Model>>(iter: I) -> Self {
		let mut c = Model::default();

		for i in iter {
			c.extend(std::iter::once(i));
		}

		c
	}
}

impl Checker for Model {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<(), CheckError> {
		self.check_assignment(&self.assign(sol))
			.map_err(|errs| errs.into_iter().next().unwrap())
		// into_first() ?
	}
}

impl Default for Model {
	fn default() -> Self {
		Self {
			cons: vec![],
			num_var: 0,
			obj: Obj::Satisfy,
			config: ModelConfig::default(),
			cse: Cse::default(),
		}
	}
}

impl Model {
	/// New auxiliary variable (meaning it could be inconsistent, or already be encoded)
	pub fn var_by_lbl(&self, lbl: &str) -> Option<IntVarRef> {
		self.vars().find(|x| x.borrow().lbl == lbl)
	}

	/// New auxiliary variable (meaning it could be inconsistent, or already be encoded)
	pub(crate) fn new_aux_var(
		&mut self,
		dom: Dom,
		add_consistency: bool,
		e: Option<IntVarEnc>,
		lbl: String,
	) -> Result<IntVarRef, Unsatisfiable> {
		(!dom.is_empty())
			.then(|| {
				self.num_var += 1;
				IntVar::from_dom_as_ref(self.num_var, dom, add_consistency, e, lbl)
			})
			.ok_or(Unsatisfiable)
	}

	/// Creates new var
	pub fn new_var(
		&mut self,
		dom: &[Coeff],
		lbl: String, // TODO ensure unique and not optional!
	) -> Result<IntVarRef, Unsatisfiable> {
		debug_assert!(
			self.var_by_lbl(&lbl).is_none(),
			"Model already contains variable label {lbl}\n{self}"
		); // TODO using contains requires clone?
		self.new_aux_var(Dom::new(dom.into_iter().cloned()), true, None, lbl)
	}

	/// Add constraint to model
	pub fn add_constraint(&mut self, constraint: Lin) -> Result {
		// TODO call constrain.simplified?
		self.cons.push(constraint);
		Ok(())
	}

	pub(crate) fn new_constant(&mut self, c: Coeff) -> IntVarRef {
		self.new_aux_var(Dom::constant(c), false, None, format!("Const({c}"))
			.unwrap()
	}

	/// Decompose every constraint
	pub fn fold(self, decompose: impl Fn(Self) -> Result<Self>) -> Result<Model> {
		let Model {
			cons,
			num_var,
			obj,
			config,
			cse,
		} = self;

		cons.into_iter().try_fold(
			Model {
				cons: vec![],
				num_var,
				obj,
				config,
				cse,
			},
			|mut model, con| {
				model.extend(std::iter::once(decompose(model.branch(con))?));
				Ok(model)
			},
		)
	}

	pub(crate) fn decompose_with(
		self: Model,
		decomposer: Option<&(impl Decompose + std::fmt::Debug)>,
	) -> Result<Model, Unsatisfiable> {
		if let Some(decomposer) = decomposer {
			decomposer.decompose(self)
		} else {
			Ok(self)
		}
	}

	// TODO used for experiments, made private for release
	pub fn constraints(&'_ self) -> impl Iterator<Item = &'_ Lin> {
		self.cons.iter()
	}

	pub(crate) fn decompose(
		self,
		spec: Option<FxHashMap<IntVarId, IntVarEnc>>,
	) -> Result<Model, Unsatisfiable> {
		ModelDecomposer { spec }.decompose(self)
	}

	pub fn encode_vars<DB: ClauseDatabase>(&mut self, db: &mut DB) -> Result<(), Unsatisfiable> {
		// Encode (or retrieve encoded) variables (in order of id so lits line up more nicely with variable order)
		self.vars()
			.sorted_by_key(|var| var.borrow().id)
			.try_for_each(|var| {
				var.borrow_mut().decide_encoding(&self.config.cutoff);
				var.borrow_mut().encode(db).map(|_| ())
			})
	}

	/// Encode model into `db`
	pub fn encode_pub<DB: ClauseDatabase>(&mut self, db: &mut DB) -> Result<Self, Unsatisfiable> {
		self.encode_internal(db, true)
	}

	pub fn encode_internal<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
		decompose: bool,
	) -> Result<Self, Unsatisfiable> {
		let mut decomposition = if decompose {
			self.clone().decompose(None)?
		} else {
			self.clone()
		};

		decomposition.propagate(&self.config.propagate.clone())?;

		for con in &decomposition.cons {
			con.encode(db, &self.config)?;
		}

		Ok(decomposition)
	}

	pub fn propagate(&mut self, consistency: &Consistency) -> Result<(), Unsatisfiable> {
		// TODO for Gt/Bdd we actually know we can start propagation at the last constraint
		let mut queue = BTreeSet::from_iter(0..self.cons.len());
		if consistency == &Consistency::None {
			return Ok(());
		}
		while let Some(con) = queue.pop_last() {
			let changed = self.cons[con].propagate(consistency)?;
			queue.extend(self.cons.iter().enumerate().filter_map(|(i, con)| {
				con.exp
					.terms
					.iter()
					.any(|term| changed.contains(&term.x.borrow().id))
					.then_some(i)
			}));
		}
		Ok(())
	}

	/// Collect and return all variables (iterates over all constraints)
	pub fn vars(&self) -> impl Iterator<Item = IntVarRef> {
		self.cons
			.iter()
			.flat_map(|con| con.exp.terms.iter().map(|term| term.x.clone())) // don't use con.vars() since this will do redundant canonicalizing
			.unique_by(|x| x.borrow().id)
			.collect_vec()
			.into_iter()
	}

	/// Assign `sol` to model to yield its integer `Assignment`
	pub fn assign<F: Valuation + ?Sized>(&self, sol: &F) -> Assignment {
		Assignment::new(self.vars(), sol)
	}

	/// Checks correctness of total `assignment`
	pub fn check_assignment(&self, assignment: &Assignment) -> Result<(), Vec<CheckError>> {
		let errs = self
			.vars()
			.map(|x| x.borrow().check(assignment))
			.chain(self.cons.iter().map(|con| con.check(assignment)))
			.filter_map(|result| result.is_err().then(|| result.unwrap_err()))
			.collect_vec();
		errs.is_empty().then_some(()).ok_or(errs)
	}

	/// Brute-forces all solutions for given output variables (or all if None)
	pub(crate) fn generate_solutions(
		&self,
		vars: Option<Vec<IntVarRef>>,
	) -> (Vec<Assignment>, bool) {
		let vars = vars.unwrap_or_else(|| self.vars().collect_vec());
		assert!(
			is_unique(vars.iter().map(|x| x.borrow().lbl())),
			"Output variables do not have unique labels: {}",
			vars.iter().map(|x| x.borrow().lbl()).sorted().join(", ")
		);
		/// Limit brute force solve by seconds
		const BUDGET: Option<u64> = Some(20);
		let timer = Instant::now();
		let mut complete = true;

		(vars
                 .iter()
                 .map(|var| var.borrow().dom.clone().iter().collect_vec())
                 .multi_cartesian_product()
                 .map(|a| Assignment::from(vars.iter().cloned().zip(a).collect_vec()))
                 .filter(|a| self.check_assignment(a).is_ok())
                 .enumerate()
                 .map(|(i, a)| {
                     if let Some(budget) = BUDGET {
                         if timer.elapsed() > Duration::from_secs(budget) {
                             println!("Exceeded brute force solve budget of {budget} after finding #{i} solutions for model:\n{self}");
                             complete = false;
                         }
                     }
                     a
                 })
                 .sorted() // need to sort to make unique since HashMap cannot derive Hash
                 .dedup()
                 .collect(), complete)
	}

	/// Check that `actual_assignments` to contain all solutions this model
	pub fn check_assignments(
		&self,
		actual_assignments: &[Assignment],
		expected_assignments: Option<&(Vec<Assignment>, bool)>,
		brute_force_solve: bool,
		principals: &[IntVarRef],
	) -> Result<(), Vec<CheckError>> {
		assert!(
			is_unique(principals.iter().map(|x| x.borrow().lbl())),
			"Cannot check assignments if principal variables have different labels: {}",
			principals
				.iter()
				.map(|x| format!("{}", x.borrow()))
				.join(", ")
		);
		let errs = actual_assignments
			.iter()
			.map(|actual_assignment| self.check_assignment(actual_assignment))
			.filter_map(|result| result.is_err().then(|| result.unwrap_err()))
			.flatten() // collect
			.collect_vec();

		// Throw early if expected_assignments need to be computed
		if !brute_force_solve && expected_assignments.is_none() {
			if errs.is_empty() {
				println!(
					"Variables and constraints hold for actual assignments:\n{}",
					if actual_assignments.is_empty() {
						String::from("Unsat")
					} else {
						actual_assignments.iter().join("\n")
					}
				);
				return Ok(());
			} else {
				return Err(errs);
			}
		}

		let (expected_assignments, complete) = expected_assignments
			.cloned()
			.unwrap_or_else(|| self.generate_solutions(None));
		assert!(complete);

		let canonicalize = |a: &[Assignment]| a.iter().sorted().cloned().collect::<Vec<_>>();

		let check_unique = |a: &[Assignment], mess: &str| {
			assert!(
				a.iter().sorted().tuple_windows().all(|(a, b)| a != b),
				// is_unique(a.clone().iter().map(|a| a.clone().iter().sorted().collect_vec())),
				"Expected unique {mess} assignments but got:\n{}",
				a.iter().map(|a| format!("{}", a)).join("\n")
			);
		};

		let expected_assignments = canonicalize(&expected_assignments);
		check_unique(&expected_assignments, "expected");
		let actual_assignments = canonicalize(actual_assignments);

		// TODO unnecessary canonicalize?
		// The extra int assignments are the actual assignments of which are not contained by the expected assignments
		let extra_int_assignments = canonicalize(
			&actual_assignments
				.iter()
				.filter(|a| {
					//TODO
					// complete
					// 	&&
					!expected_assignments.iter().any(|e| {
						principals
							.iter()
							.all(|x| a.value(&x.borrow()) == e.value(&x.borrow()))
					})
				})
				.cloned()
				.collect::<Vec<_>>(),
		);

		// A missing int assignment si one which is not in the asc
		let missing_int_assignments = canonicalize(
			&expected_assignments
				.iter()
				.filter(|e| {
					!actual_assignments.iter().any(|a| {
						principals
							.iter()
							.all(|x| a.value(&x.borrow()) == e.value(&x.borrow()))
					})
				})
				.cloned()
				.collect::<Vec<_>>(),
		);

		if !extra_int_assignments.is_empty() || !missing_int_assignments.is_empty() {
			return Err(errs
				.into_iter()
				.chain([CheckError::Fail(format!(
					"
{:?}
Extra solutions ({}):
{}
Missing solutions ({}):
{}
Expected assignments ({}):
{}
Actual assignments ({}):
{}
",
					self.config,
					extra_int_assignments.len(),
					if actual_assignments.is_empty() {
						String::from("  Unsatisfiable")
					} else {
						extra_int_assignments
							.iter()
							.map(|a| format!("+ {}", a))
							.join("\n")
					},
					missing_int_assignments.len(),
					missing_int_assignments
						.iter()
						.map(|a| format!("- {}", a))
						.join("\n"),
					expected_assignments.len(),
					expected_assignments.iter().join("\n"),
					actual_assignments.len(),
					actual_assignments.iter().join("\n"),
				))])
				.collect());
		}

		// assert_eq!(actual_assignments.iter,
		// expected_assignments,
		// "It seems the actual and expected assignments are not identical sets:\nactual:\n{}\n expected:\n{}",
		// principal_actual_assignments.iter().join("\n"),
		// expected_assignments.iter().join("\n")
		// );

		println!(
			"Actual assignments are complete and matched against {} expected assignments:
Expected assignments:
{}
Actual assignments:
{}
",
			if complete { "complete" } else { "IMCOMPLETE" },
			expected_assignments.iter().join("\n"),
			actual_assignments.iter().join("\n"),
		);

		Ok(())
	}

	pub fn lits(&self) -> BTreeSet<Var> {
		self.vars().flat_map(|x| x.borrow().lits()).collect()
	}

	/// Configure model with `config`
	pub fn with_config(self, config: ModelConfig) -> Self {
		Model { config, ..self }
	}

	#[cfg(test)]
	pub(crate) fn deep_clone(&self) -> Self {
		// pff; cannot call deep_clone recursively on all the constraints, as it will deep_clone recurring variables multiple times

		use std::{cell::RefCell, rc::Rc};
		let vars = self
			.vars()
			.map(|x| (x.borrow().id, Rc::new(RefCell::new((*x.borrow()).clone()))))
			.collect::<FxHashMap<_, _>>();
		#[allow(clippy::needless_update, reason = "TODO unsure how to avoid")]
		Self {
			cons: self
				.cons
				.iter()
				.cloned()
				.map(|con| Lin {
					exp: LinExp {
						terms: con
							.exp
							.terms
							.into_iter()
							.map(|term| Term {
								x: vars[&term.x.borrow().id].clone(),
								..term
							})
							.collect(),
						..con.exp
					},
					..con
				})
				.collect(),
			..self.clone()
		}
	}

	pub(crate) fn branch(&self, con: Lin) -> Self {
		Model {
			cons: vec![con],
			num_var: self.num_var,
			config: self.config.clone(),
			..Model::default()
		}
	}
}

#[cfg(test)]
#[cfg(feature = "cadical")]
mod tests {
	use super::*;

	use crate::integer::Format;
	use crate::solver::cadical::Cadical;
	use crate::solver::Solver;
	use crate::{integer::decompose::LinDecomposer, Cnf};
	#[cfg(feature = "tracing")]
	use traced_test::test;

	use itertools::{iproduct, Itertools};
	use std::path::PathBuf;
	use std::sync::LazyLock;

	macro_rules! has_bool_flags {
		($flags:expr) => {{
			LazyLock::new(|| $flags.into_iter().any(|f| std::env::args().contains(f)))
		}};
	}

	macro_rules! get_int_flag {
		($flag:expr) => {{
			LazyLock::new(|| {
				std::env::args()
					.position(|x| x == $flag)
					.map(|p| std::env::args().nth(p + 1).unwrap().parse().unwrap())
			})
		}};
	}

	static TEST_CUTOFF: LazyLock<Option<i64>> = get_int_flag!("--mix");

	/// Which uniform (for now) integer encoding specifications to test
	static VAR_ENCS: LazyLock<Vec<Mix>> = LazyLock::new(|| {
		let encs = std::env::args()
			.map(|arg| match arg.as_str() {
				"--ord" => Some(Mix::Order),
				"--bin" => Some(Mix::Binary),
				_ => None,
			})
			.chain([TEST_CUTOFF.map(Mix::Mix)])
			.flatten()
			.collect_vec();
		encs.is_empty()
			.then_some(vec![Mix::Order, Mix::Binary, Mix::Mix(5)])
			.unwrap_or(encs)
	});
	// /// Test propagation extension
	// static TEST_CONSISTENCIES: LazyLock<Consistency> =
	// 	has_bool_flags!(&[String::from("--prop"), String::from("-tp")]);

	/// Generate solutions for expected models
	static BRUTE_FORCE_SOLVE: LazyLock<bool> =
		has_bool_flags!(&[String::from("--brute-force-solve"), String::from("-bfs")]);
	/// Check that the decomposition correctly encodes the model
	static CHECK_DECOMPOSITION: LazyLock<bool> =
		has_bool_flags!(&[String::from("--check-decomposition"), String::from("-cd")]);
	/// Check each constraint of the decomposition individually (unstable)
	static CHECK_CONSTRAINTS: LazyLock<bool> =
		has_bool_flags!(&[String::from("--check-constraints"), String::from("-cc")]);
	/// Show assignments to auxiliary variables as well (shows more detail, but also more (symmetrical) solutions)
	static SHOW_AUX: LazyLock<bool> =
		has_bool_flags!(&[String::from("--show-aux"), String::from("-a")]);

	static TEST_CONFIG_I: LazyLock<Option<usize>> = get_int_flag!("--test-config");
	// static TEST_DECOMP_I: LazyLock<Option<usize>> = get_int_flag!("--test-decomp");

	#[test]
	fn model_test() {
		// Instantiate model
		let mut model = Model::default().with_config(ModelConfig {
			scm: Scm::Add,
			..ModelConfig::default()
		});

		// Add variables using dom/slice with optional label
		let x1 = model.new_var(&[0, 2], "x1".to_owned()).unwrap();
		let x2 = model.new_var(&[0, 3], "x2".to_owned()).unwrap();
		let x3 = model.new_var(&[0, 5], "x3".to_owned()).unwrap();

		// Add (linear) constraint
		model
			.add_constraint(Lin::new(
				&[Term::new(1, x1), Term::new(1, x2), Term::new(1, x3)],
				Comparator::LessEq,
				6,
				String::from("c1"),
			))
			.unwrap();

		// Encode to ClauseDatabase
		let mut cnf = Cnf::default();
		model.encode_internal(&mut cnf, true).unwrap();
	}

	/// All possible currently stable (!) configurations
	fn get_model_configs() -> Vec<ModelConfig> {
		iproduct!(
			[Scm::Dnf],
			[
				Decomposer::Gt,
				// Decomposer::Swc, // TODO
				Decomposer::Bdd,
				// Decomposer::Rca
			],
			[Consistency::None],
			[false], // consistency
			// [true],          // equalize terns
			// [Some(0)], // cutoffs: [None, Some(0), Some(2)]
			(*VAR_ENCS).iter().cloned(),
			[false] // equalize_uniform_bin_ineqs
		)
		.map(
			|(
				scm,
				decomposer,
				propagate,
				add_consistency,
				// equalize_ternaries,
				cutoff,
				equalize_uniform_bin_ineqs,
			)| {
				ModelConfig {
					scm: scm.clone(),
					decomposer: decomposer.clone(),
					propagate,
					add_consistency,
					// equalize_ternaries: cutoff == Mix::Binary,
					equalize_ternaries: true,
					cutoff,
					equalize_uniform_bin_ineqs,
				}
			},
		)
		.collect()
	}

	fn test_lp_for_configs(lp: &str, configs: Option<Vec<ModelConfig>>) {
		test_model(
			Model::from_string(lp, Format::Lp).unwrap(),
			Some(configs.unwrap_or_else(get_model_configs)),
		);
	}

	/// Checks decomposition (without encoding)
	fn check_decomposition(
		model: &Model,
		decomposition: &Model,
		expected_assignments: Option<&(Vec<Assignment>, bool)>,
	) {
		if *BRUTE_FORCE_SOLVE {
			let (decomposition_actual_assignments, complete) =
				decomposition.generate_solutions(None);
			assert!(
				complete,
				"Cannot check decomposition if BFS sols are not complete"
			);
			if let Err(errs) = model.check_assignments(
				&decomposition_actual_assignments,
				expected_assignments,
				*BRUTE_FORCE_SOLVE,
				&model.vars().collect_vec(),
			) {
				for err in errs {
					println!("Decomposition error:\n{err}");
				}
				panic!(
					"Decomposition is incorrect. Test failed for {:?}\n{model}",
					model.config
				)
			}
		}
	}

	fn _expand_var_encs(
		var_encs: &[IntVarEnc],
		vars: Vec<IntVarRef>,
	) -> Vec<FxHashMap<IntVarId, IntVarEnc>> {
		if var_encs.is_empty() || TEST_CUTOFF.is_some() {
			return vec![FxHashMap::default()];
		}

		return var_encs
			.iter()
			// .chain((*TEST_CUTOFF).map(|e| IntVarEnc:)
			.map(|enc| {
				vars.iter()
					.sorted_by_key(|var| var.borrow().id)
					.filter(|x| x.borrow().e.is_none())
					.map(|x| (x.borrow().id, enc.clone()))
					.collect::<FxHashMap<_, _>>()
			})
			.filter(|encs| !encs.is_empty())
			.collect();

		/*
		   // TODO Comprehensive mixed encoding testing. Working but disabled for now
		let (var_enc_ids, var_enc_gens): (Vec<_>, Vec<_>) = vars
			.iter()
			.sorted_by_key(|var| var.borrow().id)
			// If not encoded and no encoding preference (e.g. scm), assign and encode
			// TODO maybe remove constants (although some bugs might arise from the different encodings of constants
			.filter(|x| x.borrow().e.is_none())
			.map(|x| {
				(
					x.borrow().id,
					if x.borrow().is_constant() {
						vec![IntVarEnc::Ord(None)]
					} else {
						VAR_ENCS.to_vec()
					},
				)
			})
			.unzip();

		assert!(
			var_enc_ids.len() <= 50,
			"Attempting to test many ({}) var enc specs ({:?})",
			var_enc_ids.len(),
			var_enc_ids
		);

		let var_encs_gen = var_enc_gens
			.into_iter()
			.multi_cartesian_product()
			.map(|var_encs| {
				var_enc_ids
					.iter()
					.cloned()
					.zip(var_encs.into_iter())
					.collect::<FxHashMap<_, _>>()
			})
			.collect_vec();

		if var_encs_gen.is_empty() {
			vec![FxHashMap::default()]
		} else {
			var_encs_gen
		}

		*/
	}

	fn test_model(model: Model, configs: Option<Vec<ModelConfig>>) {
		println!("model = {}", model);

		let expected_assignments = (*BRUTE_FORCE_SOLVE).then(|| model.generate_solutions(None));

		if Some((vec![], true)) == expected_assignments {
			println!("WARNING: brute force solver determined model UNSAT");
		}

		for (i, config) in {
			let configs = configs.unwrap_or_else(|| vec![model.config.clone()]);

			if let Some(i) = *TEST_CONFIG_I {
				vec![(
					i,
					configs
						.get(i)
						.expect("TEST_CONFIG_I is not set to None")
						.clone(),
				)]
			} else {
				configs.into_iter().enumerate().collect_vec()
			}
		} {
			let model = model.deep_clone().with_config(config.clone());

			for (j, _var_encs) in {
				let lin_decomp = model
					.clone()
					.decompose_with(Some(&LinDecomposer::default()))
					.unwrap();

				println!("lin_decomp = {}", lin_decomp);
				// check the linear decomposition as well
				// if CHECK_DECOMPOSITION {
				// 	check_decomposition(&model, &lin_decomp, expected_assignments.as_ref());
				// }

				// let var_encs_gen = expand_var_encs(
				// 	&(*VAR_ENCS).iter().cloned().collect_vec(),
				// 	lin_decomp.vars().collect(),
				// );
				// if let Some(j) = *TEST_DECOMP_I {
				// 	vec![(
				// 		j,
				// 		var_encs_gen
				// 			.get(j)
				// 			.expect("TEST_DECOMP_I is not set to None")
				// 			.clone(),
				// 	)]
				// } else if var_encs_gen.is_empty() {
				// 	vec![(0, FxHashMap::default())]
				// } else {
				// 	var_encs_gen.into_iter().enumerate().collect_vec()
				// }
				vec![(0, 0)]
			} {
				// let spec = if (*VAR_ENCS).is_empty() {
				// 	None
				// } else {
				// 	Some(var_encs)
				// };
				let spec = None;
				let decomposition = model.clone().decompose(spec).unwrap();

				println!("decomposition = {}", decomposition);

				if *CHECK_DECOMPOSITION {
					check_decomposition(&model, &decomposition, expected_assignments.as_ref());
				}

				for (decomposition, expected_assignments) in if *CHECK_CONSTRAINTS {
					decomposition
						.constraints()
						.map(|constraint| {
							(
								Model {
									cons: vec![constraint.clone()],
									num_var: constraint
										.exp
										.terms
										.iter()
										.map(|term| term.x.borrow().id.0)
										.max()
										.unwrap(),
									..decomposition.deep_clone()
								},
								None,
							)
						})
						.collect_vec()
				} else {
					vec![(decomposition.clone(), expected_assignments.as_ref())]
				} {
					println!(
						"checking config #{i} = {:?}\ndecomposition #{j} = {}",
						model.config, decomposition,
					);
					test_decomp(decomposition, &model, expected_assignments);
				}
			}
		}
	}

	impl IntVar {
		fn clear_encoding(&mut self) {
			self.e = match self.e.as_ref() {
				Some(IntVarEnc::Bin(Some(_))) => Some(IntVarEnc::Bin(None)),
				Some(IntVarEnc::Ord(Some(_))) => Some(IntVarEnc::Ord(None)),
				_ => return,
			};
		}
	}

	fn test_decomp(
		mut decomposition: Model,
		model: &Model,
		expected_assignments: Option<&(Vec<Assignment>, bool)>,
	) {
		let mut slv = Cadical::default();

		if *CHECK_CONSTRAINTS {
			decomposition
				.vars()
				.for_each(|x| x.borrow_mut().clear_encoding());
		}

		// for x in model.vars().collect_vec() {
		// 	x.borrow_mut().encode(&mut slv).unwrap();
		// }
		// println!("decomposition (principal vars encoded) = {}", decomposition);

		// encode and solve
		let lit_assignments = decomposition
			.encode_internal(&mut slv, false)
			.map(|_| {
				slv.solve_all(if *CHECK_CONSTRAINTS || *SHOW_AUX {
					decomposition.lits()
				} else {
					model.lits()
				})
			})
			.unwrap_or_else(|_| {
				println!("Warning: encoding decomposition lead to UNSAT");
				Vec::default()
			});

		println!("encoded = {}", decomposition);

		// The checker model depends on whether we are testing each individual constraint of the decomp or showing aux variables
		let checker = if *CHECK_CONSTRAINTS || *SHOW_AUX {
			decomposition.clone()
		} else {
			// create a checker model with the constraints of the principal model and the encodings of the encoded decomposition
			model.deep_clone()
		};

		let actual_assignments: Vec<_> = lit_assignments
			.iter()
			.map(|lit_assignment| checker.assign(lit_assignment))
			// .sorted()
			// .inspect(|(assignment, lit_assignment)| {
			// 	println!("{assignment} -> {lit_assignment}");
			// })
			.collect();
		// let (actual_assignments, _): (Vec<_>, Vec<_>) = assigns.into_iter().unzip();

		// assert!(
		// 	checker.vars()
		// 		.map(|x| x.borrow().lbl.clone().unwrap())
		// 		.unique()
		// 		.count() == checker.vars().count(),
		// 	"Cannot check assignments if principal variables have different labels: {}",
		// 	checker.vars()
		// 		.map(|x| format!("{}", x.borrow()))
		// 		.join(", ")
		// );

		let check = checker.check_assignments(
			&actual_assignments,
			expected_assignments,
			*BRUTE_FORCE_SOLVE,
			&model.vars().collect_vec(),
		);
		if let Err(errs) = check {
			for err in errs {
				println!("{err}");
			}
			panic!("Encoding is incorrect. Test failed for {:?}", model.config);
		}
	}

	#[test]
	fn test_lp_le_single() {
		test_lp_for_configs(
			r"
Subject To
c0: + 3 x1 <= 8
bounds
0 <= x1 <= 3
End
",
			None,
		);
	}

	#[test]
	fn test_lp_le_single_gaps() {
		test_lp_for_configs(
			r"
Subject To
  c0: + 1 x1 <= 6
\  c0: + 2 x1 <= 2
doms
  x1 in 0,2,3,5
End
",
			None,
		);
	}

	#[test]
	fn test_lp_ge_single() {
		test_lp_for_configs(
			r"
Subject To
c0: + 3 x1 >= 1
bounds
0 <= x1 <= 3
End
",
			None,
		);
	}

	#[test]
	fn test_lp_le_single_w_neg_dom() {
		test_lp_for_configs(
			r"
Subject To
c0: + 3 x1 <= 8
bounds
-2 <= x1 <= 3
End
",
			None,
		);
	}

	#[test]
	fn test_lp_le_single_with_shift() {
		test_lp_for_configs(
			r"
Subject To
c0: + 6 x1 <= 8
bounds
0 <= x1 <= 3
End
",
			None,
		);
	}

	#[test]
	fn test_int_lin_le_single() {
		test_lp_for_configs(
			r"
Subject To
c0: + x1 <= 0
Binary
x1
End
",
			None,
		);
	}

	// TODO some tests need to be evaluated, whole testing set-up may need some organization? Just a directory of lp's?

	#[test]
	fn test_reconcile_neg_coeff_for_rca() {
		test_lp_for_configs(
			r"
	Subject To
	c0: -5 x1 <= -1
	* c0: -1 x1 <= -1
    Bounds
	0 <= x1 <= 3
	End
	",
			None,
		);
	}

	#[test]
	fn test_lp_le_double_w_const() {
		test_lp_for_configs(
			r"
	Subject To
	c0: + 2 x1 + 3 x2 - 1 x3 <= 0
	bounds
	0 <= x1 <= 1
	0 <= x2 <= 1
	4 <= x3 <= 4
	End
	",
			None,
		);
	}

	#[test]
	fn test_int_lin_ge_single() {
		test_lp_for_configs(
			r"
Subject To
c0: + x1 >= 1
Binary
x1
End
",
			None,
		);
	}

	#[test]
	fn test_int_lin_binary_constraint_le() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 - 1 x2 <= 0
Bounds
0 <= x1 <= 3
0 <= x2 <= 3
Encs
    x1 B
    x2 B
End
",
			None,
		);
	}

	#[test]
	fn test_int_lin_binary_constraint_ge() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 - 1 x2 >= 0
Bounds
0 <= x1 <= 3
0 <= x2 <= 3
Encs
    x1 B
    x2 B
End
",
			None,
		);
	}

	fn test_lp(s: &str) {
		let p = PathBuf::from(if s.ends_with(".lp") {
			s.to_owned()
		} else {
			format!("./res/lps/{}.lp", s)
		});
		test_lp_for_configs(
			&std::fs::read_to_string(&p)
				.unwrap_or_else(|e| panic!("Error reading LP {}:\n{e}", p.display())),
			None,
		);
	}


	#[test]
	fn le_1() {
		test_lp("le_1");
	}

	#[test]
	fn le_mix() {
		test_lp("le_mix");
	}

	#[test]
	fn le_2() {
		test_lp("le_2");
	}

	#[test]
	fn eq_1() {
		test_lp("eq_1");
	}

	#[test]
	#[ignore]
	fn eq_2() {
		test_lp("eq_2");
	}

	#[test]
	fn eq_mix() {
		test_lp("eq_mix");
	}

	#[test]
	fn eq_mix_bug_1() {
		test_lp("eq_mix_bug_1");
	}


	#[test]
	fn couple_bug_1() {
		test_lp("couple_bug_1");
	}

	#[test]
	fn test_rca_ground() {
		test_lp("rca_ground");
	}

	#[test]
	fn eq_channel() {
		test_lp("eq_channel");
	}

	#[test]
	fn eq_channel_term() {
		test_lp("eq_channel_term");
	}

	#[test]
	fn le_unit_tern_1() {
		test_lp("le_unit_tern_1");
	}

	#[test]
	fn le_unit_tern_2() {
		test_lp("le_unit_tern_2");
	}

	#[ignore]
	#[test]
	fn le_unit_tern_3() {
		test_lp("le_unit_tern_3");
	}

	#[ignore]
	#[test]
	fn le_unit_tern_4() {
		test_lp("le_unit_tern_4");
	}

	// #[test]
	// fn test_model_by_lps() {
	// 	for lp in std::fs::read_dir("./src/integer/res/lps").unwrap() {
	// 		test_lp_for_configs(&std::fs::read_to_string(lp.unwrap().path()).unwrap(), None);
	// 	}
	// }

	// TODO this test needs to be profiled as it takes very long for unknown reason!
	// #[test]
	// fn test_int_lin_les() {
	// 	test_lp_for_configs(
	// 		r"
	// Subject To
	// c0: + 2 x1 + 3 x2 + 5 x3 <= 6
	// c1: + 4 x1 + 2 x2 + 6 x3 <= 6
	// Binary
	// x1
	// x2
	// x3
	// End
	// ",
	// 		None,
	// 	);
	// }

	#[test]
	fn test_int_lin_le_2() {
		test_lp_for_configs(
			r"
Subject To
c0: + 4 x1 + 1 x2 <= 4
Binary
x1
x2
End
",
			None,
		);
	}

	// TODO fix failing
	// #[test]
	fn _test_lp_le_2() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 + 2 x2 - 1 x3 <= 0
Bounds
0 <= x1 <= 2
0 <= x2 <= 2
0 <= x3 <= 2
End
",
			None,
		);
	}

	// Shows the problem for current binary ineq method
	#[test]
	fn test_int_lin_le_3() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 + 2 x2 <= 4
Bounds
0 <= x1 <= 3
0 <= x2 <= 1
End
",
			None,
		);
	}

	// TODO
	// #[test]
	fn _test_int_lin_le_4_unit_tern() {
		test_lp_for_configs(
			r"
Subject To
  c0: 4 x_1 + 1 x_2 - 1 x_3 = 0
  \ c0: 1 x_1 + 1 x_2 - 1 x_3 = 0
  \ c0: 3 x_1 + 1 x_2 = 0
Bounds
  0 <= x_1 <= 3
  0 <= x_2 <= 3
  0 <= x_3 <= 3
End
",
			None,
		);
	}

	// TODO
	// #[test]
	fn _test_int_lin_eq_1() {
		test_lp_for_configs(
			r"
Subject To
c0: + 2 x1 + 3 x2 = 5
Binary
x1
x2
End
",
			None,
		);
	}

	#[test]
	fn test_int_lin_eq_tmp() {
		test_lp_for_configs(
			r"
	Subject To
	c0: + 1 x1 - 1 x2 <= 0
	Bounds
	0 <= x1 <= 3
	0 <= x2 <= 3
	End
	",
			None,
		);
	}

	// #[test]
	fn _test_int_lin_eq_3() {
		test_lp_for_configs(
			r"
	Subject To
	c0: + 1 x1 + 1 x2 = 2
	Bounds
	0 <= x1 <= 1
	0 <= x2 <= 1
	End
	",
			None,
		);
	}

	#[test]
	fn test_int_lin_ge_1() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 + 1 x2 + 1 x3 >= 3
Binary
x1
x2
x3
End
",
			None,
		);
	}

	#[test]
	fn ge_1() {
		test_lp("ge_1");
	}

	#[test]
	fn dev() {
		test_lp("dev");
	}

	// #[test]
	fn _test_lp_ge_pb_neg_1() {
		test_lp_for_configs(
			r"
Subject To
c0: - 1 x1 >= 0
Bounds
0 <= x1 <= 1
End
",
			None,
		);
	}

	// #[test]
	fn _test_lp_ge_pb_neg_2() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 + 2 x2 - 1 x3 >= 0
Bounds
0 <= x1 <= 1
0 <= x2 <= 1
0 <= x3 <= 1
End
",
			None,
		);
	}

	#[test]
	fn _test_lp_ge_neg() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 + 2 x2 - 1 x3 >= 0
Bounds
0 <= x1 <= 3
0 <= x2 <= 4
0 <= x3 <= 5
End
",
			None,
		);
	}

	// TODO regression after avoid extra literal in adder
	/*
		#[test]
		fn test_lp_ge_neg_2() {
			test_lp_for_configs(
				r"
	Subject To
	c0: + 1 x1 + 2 x2 - 3 x3 >= 0
	Bounds
	-2 <= x1 <= 3
	-1 <= x2 <= 4
	-2 <= x3 <= 5
	End
	",
			None);
		}

		#[test]
		fn test_lp_le_neg_last() {
			test_lp_for_configs(
				r"
	Subject To
	c0: + 1 x1 + 2 x2 - 3 x3 <= 0
	Bounds
	-2 <= x1 <= 3
	-1 <= x2 <= 4
	-2 <= x3 <= 5
	End
	",
			None);
		}
		*/

	// #[test]
	fn _test_lp_le_3() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 + 1 x2 - 1 x3 <= 0
Doms
x1 in 0,2
x2 in 0,3
x3 in 0,2,3,5
End
",
			None,
		);
	}

	// TODO ! We are not handling >=/== correctly when decomposing as BDD; because the domain always uses the end of the interval; instead use start of interval if >=, and create 2 constraints for <= and >= if using ==
	#[test]
	fn test_lp_2() {
		test_lp_for_configs(
			r"
Subject To
c0: + 2 x1 + 3 x2 + 5 x3 >= 6
Binary
x1
x2
x3
End
",
			None,
		);
	}

	// #[test]
	fn _test_lp_3() {
		test_lp_for_configs(
			"
Subject To
c0: + 1 x1 - 1 x2 = 0
Bounds
0 <= x1 <= 1
0 <= x2 <= 1
End
",
			None,
		);
	}

	// #[test]
	fn _test_lp_4() {
		test_lp_for_configs(
			"
Subject To
c0: + 2 x1 - 3 x2 = 0
Bounds
0 <= x1 <= 3
0 <= x2 <= 5
End
",
			None,
		);
	}

	// #[test]
	fn _test_lp_4_xs() {
		test_lp_for_configs(
			"
Subject To
c0: + 2 x1 - 3 x2 + 2 x3 - 4 x4 <= 6
Bounds
0 <= x1 <= 1
0 <= x2 <= 1
0 <= x3 <= 1
0 <= x4 <= 1
End
	",
			None,
		);
	}

	#[test]
	fn test_lp_multiple_constraints() {
		test_lp_for_configs(
			r"
Subject To
c0: + 2 x1 + 3 x2 <= 6
* c1: + 2 x1 + 5 x3 >= 5
Binary
x1
x2
End
",
			None,
		);
	}

	#[test]
	fn test_lp_multiple_scms() {
		test_lp_for_configs(
			r"
Subject To
c0: + 3 x1 + 5 x2 <= 12
c1: + 3 x1 + 10 x2 >= 17
Bounds
0 <= x1 <= 3
0 <= x2 <= 3
Encs
x1 B
x2 B
End
",
			None,
		);
	}

	// #[test]
	fn _test_soh() {
		test_lp_for_configs(
			"
Subject To
c0: + 1 x1 - 1 x3 >= 0
c1: + 1 x2 - 1 x4 >= 0
c2: + 1 x1 + 1 x2 - 1 x3 - 1 x4 <= -1
Bounds
0 <= x1 <= 3
0 <= x2 <= 3
0 <= x3 <= 3
0 <= x4 <= 3
End
",
			None,
		);
	}

	// #[test]
	fn _test_lp_scm_1() {
		test_lp_for_configs(
			r"
Subject To
c0: x1 - 4 x2 = 0
Bounds
0 <= x1 <= 4
0 <= x2 <= 4
End
",
			None,
		);
	}

	#[test]
	#[ignore]
	fn test_lp_scm_2() {
		test_lp_for_configs(
			r"
Subject To
c0: 11 x1 - x2 = 0
Bounds
0 <= x1 <= 3
0 <= x2 <= 33
End
",
			None,
		);
	}

	// #[test]
	// fn test_lp_scm_3() {
	// 	test_lp(
	// 		r"
	// Subject To
	// c0: x1 - 43 x2 = 0
	// Bounds
	// 0 <= x1 <= 2000
	// 0 <= x2 <= 4
	// End
	// ",
	// 	);
	// }

	#[test]
	fn test_scm_7_0() {
		// Contains negative adder 7x = 8x-1x for Scm::Rca
		test_lp_for_configs(
			r"
	Subject To
	c0: 7 x_1 = 0
	Bounds
	0 <= x_1 <= 3
	End
	",
			None,
		);
	}

	#[test]
	fn test_scm_3_11() {
		test_lp_for_configs(
			r"
	Subject To
	c0: 11 x_1 = 0
	Bounds
	0 <= x_1 <= 15
	End
	",
			None,
		);
	}

	#[test]
	fn test_scm_3_43() {
		test_lp_for_configs(
			r"
	Subject To
	c0: 43 x_1 = 0
	Bounds
	0 <= x_1 <= 7
	End
	",
			None,
		);
	}

	#[test]
	fn test_scm_general() {
		let (l, u) = (0, 1);
		let cs = 1..=117;
		// let cs = [117];
		// TODO could generate custom expected solutions here, since brute force will be intractable
		for c in cs {
			let (x2l, x2u) = (c * l, c * u);
			test_lp_for_configs(
				&format!(
					"
	Subject To
	c0: {c} x_1 - 1 x_2 = 0
	Bounds
    {l} <= x_1 <= {u}
    {x2l} <= x_2 <= {x2u}
	End
	"
				),
				None,
			);
		}
	}

	#[test]
	fn test_scm_4_9() {
		test_lp_for_configs(
			r"
Subject To
  c0: 9 x_1 = 0
Bounds
  0 <= x_1 <= 7
End
",
			None,
		);
		// test_lp(lp, ModelConfig { scm_add: true });
	}

	#[test]
	fn test_scm_4_43() {
		test_lp_for_configs(
			r"
Subject To
  c0: 43 x_1 = 0
Bounds
  0 <= x_1 <= 7
End
",
			None,
		);
	}

	// TODO
	// #[test]
	// fn test_scm_4_neg_43() {
	// 	test_lp_for_configs(
	// 		r"
	// Subject To
	// c0: -43 x_1 = 0
	// Bounds
	// 0 <= x_1 <= 7
	// End
	// ",
	// 		None,
	// 	);
	// }

	#[test]
	fn test_incon() {
		// 59 * x_1=0 (=0) + 46 * x_2=7 (=322) + 132 * x_3=4 (=528) + 50 * x_4=4 (=200) + 7 * x_5=0 (=0) == 1050 !≤ 931
		test_lp_for_configs(
			r"
Subject To
  c0: 6 x_1 <= 11
Bounds
  0 <= x_1 <= 3
End
",
			None,
		);
	}

	#[test]
	fn test_lp_tmp() {
		// 59 * x_1=0 (=0) + 46 * x_2=7 (=322) + 132 * x_3=4 (=528) + 50 * x_4=4 (=200) + 7 * x_5=0 (=0) == 1050 !≤ 931
		test_lp_for_configs(
			r"
Subject To
  c0: 2 x_1 <= 200
Bounds
  0 <= x_1 <= 7
End
",
			None,
		);
	}

	// #[test]
	// fn test_two_neg() {
	// 	// - (x1:O ∈ |0..1| 1L) ≥ - (x2:O ∈ |0..1| 1L)
	// 	test_lp_for_configs(
	// 		r"
	// Subject To
	// c0: - x1 - x2 >= 0
	// \ c0: - x1 + x2 >= 0
	// \ c0: x1 - x2 <= 0
	// Binary
	// x1
	// x2
	// End
	// ",
	// 		None,
	// 	);
	// }

	#[test]
	fn test_couple_inconsistent() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		// Expected output only has 1 (!) clause (3, -4)
		test_lp_for_configs(
			r"
Subject To
    c0: x_1 + x_2 - x_3 <= 0
Doms
    x_1 in 0,1
    x_2 in 0,5
    x_3 in 0,1,5
Encs
    x_1 O
    x_2 O
    x_3 O
End
	",
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_couple_view() {
		let base = ModelConfig {
			scm: Scm::Dnf,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		// Expected output only has 1 (!) clause (3, -4)
		test_lp_for_configs(
			r"
Subject To
    c0: 2 x_1 + 3 x_2 <= 6
Doms
    x_1 in 0,1
    x_2 in 0,1
Encs
    x_1 O
    x_2 B
End
	",
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_couple_mid() {
		let base = ModelConfig {
			scm: Scm::Dnf,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		// Expected output only has 1 (!) clause (3, -4)

		for cmp in [
			// "=",
			"<=", ">=",
		] {
			for lp in [
				format!(
					"
Subject To
    c0: x - y {} 0
Doms
    x in 0,1
    y in 0,1
Encs
    x O
    y B
End
	",
					cmp
				),
				format!(
					"
Subject To
    c1: x - y {} 0
Doms
    x in 0,1,2,3
    y in 0,1,2,3
Encs
    x O
    y B
End
	",
					cmp
				),
				format!(
					"
Subject To
    c2: x - y {} 0
Doms
    x in 0,2,5,7
    y in 0,2,5,7
Encs
    x O
    y B
End
	",
					cmp
				),
				format!(
					"
Subject To
    c3: x - y {} 0
Doms
    x in 4,6
    y in 0,1,2,3,4,5,6
Encs
    x O
    y B
End
	",
					cmp
				),
				format!(
					"
				Subject To
				c4: x - y {} 0
				Doms
				x in 4,6
				y in 1,2,3,4,5,6,7
				Encs
				x O
				y B
				End
				",
					cmp
				),
				format!(
					"
				Subject To
				c5: x - y {} 0
				Doms
				x in 4,6
				y in 3,4,5,6,7
				Encs
				x O
				y B
				End
				",
					cmp
				),
			] {
				test_lp_for_configs(&lp, Some(vec![base.clone()]));
			}
		}
		// bdd_1_c0: 	(bdd_2:O ∈ |4,6| 0L) ≥ (couple-bdd_2:B ∈ |1..6| 0L)
	}

	#[test]
	fn test_tmp_red() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Mix(2),
			// cutoff: None,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		// Expected output only has 1 (!) clause (3, -4)
		test_lp_for_configs(
			r"
Subject To
    c0: x_1 - x_2 >= 0
Doms
    x_1 in 0,1,2,3
    x_2 in 0,3
Encs
    x_1 O
    x_2 O
End
	",
			Some(vec![base.clone()]),
		);

		test_lp_for_configs(
			r"
Subject To
    c0: x_1 - x_2 <= 0
Doms
    x_1 in 0,1,2,3
    x_2 in 0,3
Encs
    x_1 O
    x_2 O
End
	",
			Some(vec![base.clone()]),
		);
		test_lp_for_configs(
			r"
Subject To
    c0: x_1 + x_2 <= 3
Doms
    x_1 in 0,1,2,3
    x_2 in 0,3
Encs
    x_1 O
    x_2 O
End
	",
			Some(vec![base.clone()]),
		);
	}

	// #[test]
	fn _test_tmp_whiteboard() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
Subject To
    c0: x + y >= 10
Bounds
    0 <= x <= 15
Doms
    y in 0,5,7,9,10
Encs
    x B
    y O
End
	",
			Some(vec![base.clone()]),
		);
	}

	// >500 cls
	// #[test]
	fn _test_sugar() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
Subject To
  c0: 1 x1 + 2 x2 + 3 x3 + 4 x4 + 5 x5 <= 6
Bounds
  0 <= x1 <= 1
  0 <= x2 <= 1
  0 <= x3 <= 1
  0 <= x4 <= 1
  0 <= x5 <= 1
End
	",
			// None,
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_sugar_2() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
Subject To
  c0: 1 x1 + 1 x2 >= 1
Bounds
  0 <= x1 <= 2
  0 <= x2 <= 1
End
	",
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_sugar_4() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x + 1 y >= 0
	Bounds
	  0 <= x <= 2
	  -2 <= y <= 0
	End
	",
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_sugar_le() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 <= 0
	Bounds
	  0 <= x1 <= 1
	End
	",
			Some(vec![base.clone()]),
		);
	}

	// || 	bdd_3_c0: 	194·(x_27:O ∈ |0..1| 0L) + (bdd_3:O ∈ |0,195,229,236,424,431,465,660| 0L) ≤ (bdd_4:O ∈ |0,194,195,229,236,389,423,424,..,854| |16| 0L)

	// #[test]
	fn _test_bddpbc() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
	Subject To
	  c0: 194 x + y - z <= 0
  Doms
  x in 0,1
  y in 0,195,229,236,424,431,465,660
	End
	",
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_sugar_5() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 + 1 x2 >= 1
    Binary
      x1
      x2
	End
	",
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_sugar_6() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 + 1 x2 >= 2
    Binary
      x1
      x2
	End
	",
			Some(vec![base.clone()]),
		);
	}

	// over 500 cls
	// #[test]
	fn _test_sugar_pbc() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
Subject To
  c0: 5 x1 + 4 x2 + 3 x3 + 2 x4 + 1 x5 >= 6
Bounds
  0 <= x1 <= 1
  0 <= x2 <= 1
  0 <= x3 <= 1
  0 <= x4 <= 1
  0 <= x5 <= 1
End
	",
			Some(vec![base.clone()]),
		);
	}

	#[test]
	fn test_sugar_singles() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 >= 1
	Bounds
	  0 <= x1 <= 1
	End
	",
			Some(vec![base.clone()]),
		);

		// test_lp_for_configs(
		// 	r"
		// Subject To
		// c0: -1 x1 >= 0
		// Bounds
		// 0 <= x1 <= 1
		// End
		// ",
		// 	Some(vec![base.clone()]),
		// );

		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 <= 0
	Bounds
	  0 <= x1 <= 1
	End
	",
			Some(vec![base.clone()]),
		);

		// test_lp_for_configs(
		// 	r"
		// Subject To
		// c0: - 1 x1 <= -1
		// Bounds
		// 0 <= x1 <= 1
		// End
		// ",
		// 	Some(vec![base.clone()]),
		// );
	}

	#[test]
	fn test_sugar_singles_2() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Mix::Order,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 >= 2
	Bounds
	  0 <= x1 <= 3
	End
	",
			Some(vec![base.clone()]),
		);

		// test_lp_for_configs(
		// 	r"
		// Subject To
		// c0: -1 x1 >= -1
		// Bounds
		// 0 <= x1 <= 3
		// End
		// ",
		// 	Some(vec![base.clone()]),
		// );

		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 <= 2
	Bounds
	  0 <= x1 <= 3
	End
	",
			Some(vec![base.clone()]),
		);

		test_lp_for_configs(
			r"
	Subject To
	  c0: 1 x1 >= 3
	Bounds
	  0 <= x1 <= 3
	End
	",
			Some(vec![base.clone()]),
		);

		// test_lp_for_configs(
		// 	r"
		// Subject To
		// c0: - 1 x1 <= -3
		// Bounds
		// 0 <= x1 <= 3
		// End
		// ",
		// 	Some(vec![base.clone()]),
		// );
	}

	// #[test]
	fn _test_rca_subtract() {
		let mut model = Model::default();

		let dom = Dom::from_bounds(0, 1);
		let t1 = Term::new(
			32,
			model
				.new_aux_var(
					dom.clone(),
					true,
					Some(IntVarEnc::Bin(None)),
					String::from("x1"),
				)
				.unwrap(),
		);
		let t2 = Term::new(
			-7,
			model
				.new_aux_var(
					dom.clone(),
					true,
					Some(IntVarEnc::Bin(None)),
					String::from("x2"),
				)
				.unwrap(),
		);
		let dom = Dom::from_bounds(t1.lb() + t2.lb(), t1.ub() + t2.ub());
		let con = Lin {
			exp: LinExp {
				terms: vec![
					t1,
					t2,
					Term::new(
						-1,
						model
							.new_aux_var(
								dom,
								true,
								Some(IntVarEnc::Bin(None)),
								// None,
								String::from("x3"),
							)
							.unwrap(),
					),
				],
			},
			cmp: Comparator::Equal,
			k: 0,
			lbl: "c1".to_owned(),
		};
		model.add_constraint(con).unwrap();
		test_decomp(model.deep_clone(), &model, None);
	}
}
