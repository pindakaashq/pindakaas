#![allow(clippy::absurd_extreme_comparisons)]
use std::{
	cell::RefCell,
	cmp::Ordering,
	collections::{BTreeSet, HashMap, HashSet},
	ops::Index,
	rc::Rc,
};

use itertools::Itertools;

use crate::{
	int::{
		decompose::{Decompose, ModelDecomposer},
		Dom, IntVar, IntVarId, IntVarRef, LinExp,
	},
	CheckError, Checker, ClauseDatabase, Comparator, Lin, Result, Term, Unsatisfiable, Valuation,
	Var,
};

// TODO Refactor: move to tracing
#[cfg(feature = "trace")]
pub(crate) const PRINT_COUPLING: u32 = 1;
#[cfg(not(feature = "trace"))]
pub(crate) const PRINT_COUPLING: u32 = 0;

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
pub enum Scm {
	/// Use recipe that minimizes adders. Good for ≥12 bits
	Add,
	/// Use recipe that minimizes ripple-carry-adders
	Rca,
	/// Use recipe derived by Boolean minimization (min. variables). Good for <12 bits
	#[default]
	Dnf,
}

use super::IntVarEnc;
use crate::Coeff;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Decomposer {
	Gt(bool),
	Swc,
	#[default]
	Bdd,
	Rca,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModelConfig {
	/// Which SCM method to use
	pub scm: Scm,
	pub(crate) cutoff: Option<Coeff>,
	pub(crate) decomposer: Decomposer,
	/// Rewrites all but last equation x:B + y:B ≤ z:B to x:B + y:B = z:B
	pub(crate) equalize_ternaries: bool,
	pub(crate) add_consistency: bool,
	pub(crate) propagate: Consistency,
	/// Rewrites x:B + y:B ≤ z:B to x:B + y:B = z':B ∧ y:B ≤ z:B
	pub(crate) equalize_uniform_bin_ineqs: bool,
}

#[derive(Debug, Clone)]
pub struct Model {
	pub cons: Vec<Lin>,
	pub(crate) num_var: usize,
	pub obj: Obj,
	pub config: ModelConfig,
	pub(crate) cse: Cse,
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
pub(crate) struct Cse(pub(crate) HashMap<(IntVarId, Coeff, Comparator), Term>);

// TODO [?] equivalent of Valuation, could be merged?
/// A structure holding an integer assignment to `Model`
#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct Assignment(pub HashMap<IntVarId, (String, Coeff)>);

impl Ord for Assignment {
	fn cmp(&self, other: &Self) -> Ordering {
		self.0.iter().sorted().cmp(other.0.iter().sorted())
	}
}

impl PartialOrd for Assignment {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl Index<&IntVarId> for Assignment {
	type Output = (String, Coeff);

	fn index(&self, id: &IntVarId) -> &Self::Output {
		&self.0[id]
	}
}

impl Assignment {
	pub(crate) fn partialize(self, max_var: &IntVarId) -> Self {
		Self(self.0.into_iter().filter(|(k, _)| k <= max_var).collect())
	}
}

#[derive(Debug, Default, Clone, Copy, Ord, PartialOrd, PartialEq, Eq, Hash)]
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
			c.extend(std::iter::once(i))
		}

		c
	}
}

impl Checker for Model {
	fn check<F: Valuation + ?Sized>(&self, sol: &F) -> Result<(), CheckError> {
		let a = self.assign(sol)?;
		self.cons.iter().try_for_each(|con| con.check(&a))
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
	pub(crate) fn new_aux_var(
		&mut self,
		dom: Dom,
		add_consistency: bool,
		e: Option<IntVarEnc>,
		lbl: Option<String>,
	) -> Result<IntVarRef, Unsatisfiable> {
		(!dom.is_empty())
			.then(|| {
				self.num_var += 1;
				IntVar::from_dom_as_ref(self.num_var, dom, add_consistency, e, lbl)
			})
			.ok_or(Unsatisfiable)
	}

	/// Creates new auxiliary var
	pub fn new_var(
		&mut self,
		dom: &[Coeff],
		lbl: Option<String>,
	) -> Result<IntVarRef, Unsatisfiable> {
		self.new_aux_var(Dom::from_slice(dom), true, None, lbl)
	}

	/// Add constraint to model
	pub fn add_constraint(&mut self, constraint: Lin) -> Result {
		// TODO call constrain.simplified?
		self.cons.push(constraint);
		Ok(())
	}

	pub(crate) fn new_constant(&mut self, c: Coeff) -> IntVarRef {
		self.new_aux_var(Dom::constant(c), false, None, None)
			.unwrap()
	}

	// TODO used for experiments, made private for release
	#[allow(dead_code)]
	/// Decompose every constraint
	pub(crate) fn fold(self, decompose: impl Fn(Self) -> Result<Self>) -> Result<Model> {
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
	#[allow(dead_code)]
	pub(crate) fn constraints(&'_ self) -> impl Iterator<Item = &'_ Lin> {
		self.cons.iter()
	}

	pub(crate) fn decompose(
		self,
		spec: Option<HashMap<IntVarId, IntVarEnc>>,
	) -> Result<Model, Unsatisfiable> {
		ModelDecomposer { spec }.decompose(self)
	}

	// TODO used for experiments, made private for release
	#[allow(dead_code)]
	pub(crate) fn encode_vars<DB: ClauseDatabase>(
		&mut self,
		db: &mut DB,
	) -> Result<(), Unsatisfiable> {
		// Encode (or retrieve encoded) variables (in order of id so lits line up more nicely with variable order)
		self.vars()
			.iter()
			.sorted_by_key(|var| var.borrow().id)
			.try_for_each(|var| {
				var.borrow_mut().decide_encoding(self.config.cutoff);
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

	pub(crate) fn propagate(&mut self, consistency: &Consistency) -> Result<(), Unsatisfiable> {
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
	pub fn vars(&self) -> Vec<IntVarRef> {
		self.cons
			.iter()
			.flat_map(|con| con.exp.terms.iter().map(|term| &term.x)) // don't use con.vars() since this will do redundant canonicalizing
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	/// Assign `sol` to model to yield its integer `Assignment`
	pub fn assign<F: Valuation + ?Sized>(&self, sol: &F) -> Result<Assignment, CheckError> {
		Ok(Assignment(
			self.vars()
				.iter()
				.map(|x| {
					x.borrow()
						.assign(sol)
						.map(|a| (x.borrow().id, (x.borrow().lbl(), a)))
				})
				.try_collect()?,
		))
	}

	/// Checks correctness of `assignment`
	pub fn check_assignment(&self, assignment: &Assignment) -> Result<(), CheckError> {
		self.cons.iter().try_for_each(|con| con.check(assignment))
	}

	/// Brute-forces all solutions
	pub(crate) fn generate_solutions(
		&self,
		max_var: Option<IntVarId>,
	) -> Result<Vec<Assignment>, ()> {
		let vars = self.vars();
		let max_var = max_var.unwrap_or(IntVarId(self.num_var));

		/// Limit the search space for solution generation
		const MAX_SEARCH_SPACE: Option<usize> = Some(250);
		let mut max_search_space = MAX_SEARCH_SPACE;
		let mut last_s = None;

		Ok(vars
			.iter()
			.map(|var| {
				let ds = var.borrow().dom.iter().collect::<Vec<_>>();
				if let Some(curr_max_search_space) = max_search_space {
					if let Some(new_max_search_space) =
						curr_max_search_space.checked_sub(ds.len() * last_s.unwrap_or(1))
					{
						max_search_space = Some(new_max_search_space);
						last_s = Some(ds.len());
					} else {
						return Err(());
					}
				}
				Ok(ds)
			})
			.try_collect::<Vec<Coeff>, Vec<Vec<Coeff>>, ()>()?
			.into_iter()
			.multi_cartesian_product()
			.map(|a| {
				Assignment(
					vars.iter()
						.zip(a)
						.map(|(var, a)| (var.borrow().id, (var.borrow().lbl(), a)))
						.collect::<HashMap<_, _>>(),
				)
			})
			.filter(|a| self.check_assignment(a).is_ok())
			.map(|a| a.partialize(&max_var))
			.sorted() // need to sort to make unique since HashMap cannot derive Hash
			.dedup()
			.collect())
	}

	/// Check that `actual_assignments` to contain all solutions this model
	pub fn check_assignments(
		&self,
		actual_assignments: &[Assignment],
		expected_assignments: Option<&Vec<Assignment>>,
		brute_force_solve: bool,
	) -> Result<(), Vec<CheckError>> {
		let errs = actual_assignments
			.iter()
			.filter_map(
				|actual_assignment| match self.check_assignment(actual_assignment) {
					Err(CheckError::Fail(e)) => {
						Some(CheckError::Fail(format!("Inconsistency: {e}")))
					}
					Err(e) => panic!("Unexpected err: {e}"),
					_ => None,
				},
			)
			.collect::<Vec<_>>();

		// Throw early if expected_assignments need to be computed
		if !brute_force_solve || expected_assignments.is_none() {
			if errs.is_empty() {
				println!(
					"All constraints hold for actual assignments:\n{}",
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

		let expected_assignments = expected_assignments
			.as_ref()
			.map(|expected_assignments| expected_assignments.to_vec())
			.unwrap_or_else(|| self.generate_solutions(None).unwrap());

		let canonicalize = |a: &[Assignment]| a.iter().sorted().cloned().collect::<Vec<_>>();

		let check_unique = |a: &[Assignment], mess: &str| {
			assert!(
				a.iter().sorted().tuple_windows().all(|(a, b)| a != b),
				"Expected unique {mess} assignments but got:\n{}",
				a.iter().map(|a| format!("{}", a)).join("\n")
			)
		};

		let expected_assignments = canonicalize(&expected_assignments);
		check_unique(&expected_assignments, "expected");
		let actual_assignments = canonicalize(actual_assignments);
		// check_unique(&actual_assignments, "actual"); // TODO Regression for two tests

		let principals = expected_assignments
			.first()
			.map(|assignment| assignment.0.keys().collect::<HashSet<_>>())
			.unwrap_or_default();

		let principal_actual_assignments = canonicalize(
			&actual_assignments
				.iter()
				.map(|a| {
					Assignment(
						a.0.clone()
							.into_iter()
							.filter(|(id, _)| principals.contains(id))
							.collect(),
					)
				})
				.dedup()
				.collect::<Vec<_>>(),
		);

		// TODO unnecessary canonicalize?
		let extra_int_assignments = canonicalize(
			&actual_assignments
				.iter()
				.filter(|a| {
					!expected_assignments.contains(&Assignment(
						a.0.clone()
							.into_iter()
							.filter(|(id, _)| principals.contains(id))
							.collect(),
					))
				})
				.cloned()
				.collect::<Vec<_>>(),
		);

		let missing_int_assignments = canonicalize(
			&expected_assignments
				.iter()
				.filter(|a| !principal_actual_assignments.contains(a))
				.cloned()
				.collect::<Vec<_>>(),
		);

		if !extra_int_assignments.is_empty() || !missing_int_assignments.is_empty() {
			return Err(errs
				.into_iter()
				.chain([CheckError::Fail(format!(
					"
{:?}
Extra solutions:
{}
Missing solutions:
{}
Expected assignments:
{}
Actual assignments:
{}
",
					self.config,
					if actual_assignments.is_empty() {
						String::from("  Unsatisfiable")
					} else {
						extra_int_assignments
							.iter()
							.map(|a| format!("+ {}", a))
							.join("\n")
					},
					missing_int_assignments
						.iter()
						.map(|a| format!("- {}", a))
						.join("\n"),
					expected_assignments.iter().join("\n"),
					actual_assignments.iter().join("\n"),
				))])
				.collect());
		}

		assert_eq!(principal_actual_assignments,
                   expected_assignments,
                   "It seems the actual and expected assignments are not identical sets:\nactual:\n{}\n expected:\n{}",
                   principal_actual_assignments.iter().join("\n"),
                   expected_assignments.iter().join("\n")
                  );

		println!(
			"Actual assignments are complete and correct:\n{}",
			actual_assignments.iter().join("\n")
		);

		Ok(())
	}

	// TODO used for experiments, made private for release
	#[allow(dead_code)]
	pub(crate) fn lits(&self) -> BTreeSet<Var> {
		self.vars().iter().flat_map(|x| x.borrow().lits()).collect()
	}

	/// Configure model with `config`
	pub fn with_config(self, config: ModelConfig) -> Self {
		Model { config, ..self }
	}

	// TODO used for experiments, made private for release
	#[allow(dead_code)]
	pub(crate) fn deep_clone(&self) -> Self {
		// pff; cannot call deep_clone recursively on all the constraints, as it will deep_clone recurring variables multiple times
		let vars = self
			.vars()
			.iter()
			.map(|x| (x.borrow().id, Rc::new(RefCell::new((*x.borrow()).clone()))))
			.collect::<HashMap<_, _>>();
		#[allow(clippy::needless_update)]
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
mod tests {
	use super::*;
	use crate::{helpers::tests::assert_ok, Cnf, Lin, Lit, Model};

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

	#[test]
	fn model_test() {
		assert_ok!({
			// Instantiate model
			let mut model = Model::default().with_config(ModelConfig {
				scm: Scm::Add,
				..ModelConfig::default()
			});

			// Add variables using dom/slice with optional label
			let x1 = model.new_var(&[0, 2], Some("x1".to_string()))?;
			let x2 = model.new_var(&[0, 3], Some("x2".to_string()))?;
			let x3 = model.new_var(&[0, 5], Some("x3".to_string()))?;

			// Add (linear) constraint
			model.add_constraint(Lin::new(
				&[Term::new(1, x1), Term::new(1, x2), Term::new(1, x3)],
				Comparator::LessEq,
				6,
				Some(String::from("c1")),
			))?;

			// Encode to ClauseDatabase
			let mut cnf = Cnf::default();
			model.encode_internal(&mut cnf, true)?;

			Ok::<(), Unsatisfiable>(())
		});
	}

	use itertools::{iproduct, Itertools};
	#[cfg(feature = "trace")]
	use traced_test::test;

	use crate::{helpers::tests::TestDB, int::decompose::LinDecomposer, Format};

	/// All possible currently stable (!) configurations
	fn get_model_configs() -> Vec<ModelConfig> {
		iproduct!(
			[Scm::Rca],
			[
				Decomposer::Gt(true),
				Decomposer::Gt(false),
				// Decomposer::Swc, // TODO
				// Decomposer::Bdd,
				// Decomposer::Rca
			],
			[Consistency::None],
			[false], // consistency
			// [true],          // equalize terns
			[None],  // cutoffs: [None, Some(0), Some(2)]
			[false]  // equalize_uniform_bin_ineqs
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
					propagate: propagate.clone(),
					add_consistency,
					equalize_ternaries: cutoff == Some(0),
					cutoff,
					equalize_uniform_bin_ineqs,
					..ModelConfig::default()
				}
			},
		)
		.collect()
	}

	/// Solve
	const SOLVE: bool = false;
	// TODO expect_test! should remove this
	/// Generate solutions for expected models
	const BRUTE_FORCE_SOLVE: bool = false;
	/// Which uniform (for now) integer encoding specifications to test
	const VAR_ENCS: &[IntVarEnc] = &[IntVarEnc::Ord(None)];

	/// Check each constraint of the decomposition individually (unstable)
	const CHECK_CONSTRAINTS: bool = false;
	/// Show assignments to auxiliary variables as well (shows more detail, but also more (symmetrical) solutions)
	const SHOW_AUX: bool = true;

	fn test_lp_for_configs(lp: &str, configs: Option<Vec<ModelConfig>>) {
		test_model(
			Model::from_string(lp.into(), Format::Lp).unwrap(),
			Some(configs.unwrap_or_else(get_model_configs)),
		)
	}

	fn check_decomposition(
		model: &Model,
		decomposition: &Model,
		expected_assignments: Option<&Vec<Assignment>>,
	) {
		if !BRUTE_FORCE_SOLVE || !SOLVE {
			return;
		} else if let Ok(decomposition_expected_assignments) =
			&decomposition.generate_solutions(Some(IntVarId(model.num_var)))
		{
			if let Err(errs) = model.check_assignments(
				&decomposition_expected_assignments,
				expected_assignments,
				BRUTE_FORCE_SOLVE,
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

	fn expand_var_encs(
		var_encs: &[IntVarEnc],
		vars: Vec<IntVarRef>,
	) -> Vec<HashMap<IntVarId, IntVarEnc>> {
		if var_encs.is_empty() {
			return vec![HashMap::default()];
		}
		return VAR_ENCS
			.iter()
			.map(|enc| {
				vars.iter()
					.sorted_by_key(|var| var.borrow().id)
					.filter(|x| x.borrow().e.is_none())
					.map(|x| (x.borrow().id, enc.clone()))
					.collect::<HashMap<_, _>>()
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
					.collect::<HashMap<_, _>>()
			})
			.collect_vec();

		if var_encs_gen.is_empty() {
			vec![HashMap::default()]
		} else {
			var_encs_gen
		}

		*/
	}

	fn test_model(model: Model, configs: Option<Vec<ModelConfig>>) {
		println!("model = {}", model);

		let expected_assignments = BRUTE_FORCE_SOLVE
			.then(|| model.generate_solutions(None).ok())
			.flatten();

		if Some(vec![]) == expected_assignments {
			panic!("WARNING: brute force solver found model UNSAT");
		}

		/// Check a specific config or decomposition
		const CHECK_CONFIG_I: Option<usize> = None;
		const CHECK_DECOMPOSITION_I: Option<usize> = None;

		for (i, config) in {
			let configs = configs.unwrap_or_else(|| vec![model.config.clone()]);

			if let Some(i) = CHECK_CONFIG_I {
				vec![(
					i,
					configs
						.get(i)
						.expect("CHECK_CONFIG_I is not set to None")
						.clone(),
				)]
			} else {
				configs.into_iter().enumerate().collect_vec()
			}
		} {
			let model = model.deep_clone().with_config(config.clone());

			const CHECK_DECOMPOSITION: bool = true;
			for (j, var_encs) in {
				let lin_decomp = model
					.clone()
					.decompose_with(Some(&LinDecomposer::default()))
					.unwrap();

				println!("lin_decomp = {}", lin_decomp);
				// check the linear decomposition as well
				// if CHECK_DECOMPOSITION {
				// 	check_decomposition(&model, &lin_decomp, expected_assignments.as_ref());
				// }

				let var_encs_gen =
					expand_var_encs(VAR_ENCS, lin_decomp.vars().into_iter().collect());
				if let Some(j) = CHECK_DECOMPOSITION_I {
					vec![(
						j,
						var_encs_gen
							.get(j)
							.expect("CHECK_DECOMPOSITION_I is not set to None")
							.clone(),
					)]
				} else {
					if var_encs_gen.is_empty() {
						vec![(0, HashMap::default())]
					} else {
						var_encs_gen.into_iter().enumerate().collect_vec()
					}
				}
			} {
				let spec = if VAR_ENCS.is_empty() {
					None
				} else {
					Some(var_encs)
				};
				let decomposition = model.clone().decompose(spec).unwrap();

				println!("decomposition = {}", decomposition);

				if CHECK_DECOMPOSITION {
					check_decomposition(&model, &decomposition, expected_assignments.as_ref());
				}

				for (decomposition, expected_assignments) in if CHECK_CONSTRAINTS {
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

	fn test_decomp(
		mut decomposition: Model,
		model: &Model,
		expected_assignments: Option<&Vec<Assignment>>,
	) {
		let mut db = TestDB::new(0);

		let principal_vars = decomposition
			.vars()
			.into_iter()
			.filter(|x| x.borrow().id.0 <= model.num_var)
			.map(|x| {
				// if x.borrow().e.is_some() {
				x.borrow_mut().encode(&mut db).unwrap();
				// }
				(x.borrow().id.clone(), x.clone())
			})
			.collect::<HashMap<IntVarId, IntVarRef>>();
		println!("decomposition = {}", decomposition);

		// encode and solve
		let lit_assignments = decomposition
			.encode_internal(&mut db, false)
			.map(|_| {
				let output = if CHECK_CONSTRAINTS || SHOW_AUX {
					decomposition.lits()
				} else {
					principal_vars
						.values()
						.flat_map(|x| x.borrow().lits())
						.collect()
				};

				SOLVE.then(|| {
					db.solve(Some(output))
						.into_iter()
						.sorted()
						.map(MapSol::from)
						.collect()
				})
			})
			.unwrap_or_else(|_| {
				println!("Warning: encoding decomposition lead to UNSAT");
				Some(Vec::default())
			});

		println!("encoded = {}", decomposition);
		println!("statics = [{}/{}/{}]", db.num_vars, db.num_cls, db.num_lits);

		// TODO Implement hash for MapSol
		// assert_eq!(
		// 	lit_assignments.iter().unique().count(),
		// 	lit_assignments.len(),
		// 	"Expected lit assignments to be unique, but was {lit_assignments:?}"
		// );

		// The checker model depends on whether we are testing each individual constraint of the decomp or showing aux variables
		let checker = if CHECK_CONSTRAINTS || SHOW_AUX {
			decomposition.clone()
		} else {
			// create a checker model with the constraints of the principal model and the encodings of the encoded decomposition
			let principal = model.deep_clone();
			principal.vars().into_iter().for_each(|x| {
				let id = x.borrow().id;
				x.borrow_mut().e = principal_vars[&id].borrow().e.clone();
			});
			principal
		};

		if let Some(lit_assignments) = lit_assignments {
			let actual_assignments = lit_assignments
				.iter()
				.flat_map(|lit_assignment| checker.assign(lit_assignment))
				.collect::<Vec<_>>();

			// TODO impl Hash for Assignment
			// assert_eq!(actual_assignments.iter().unique(), actual_assignments);

			let check = checker.check_assignments(
				&actual_assignments,
				expected_assignments,
				BRUTE_FORCE_SOLVE,
			);
			if let Err(errs) = check {
				for err in errs {
					println!("{err}");
				}
				panic!("Encoding is incorrect. Test failed for {:?}", model.config);
			}
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

	#[test]
	fn test_int_lin_le_1() {
		test_lp_for_configs(
			r"
Subject To
c0: + 2 x1 + 3 x2 + 5 x3 <= 6
Binary
x1
x2
x3
End
",
			None,
		);
	}

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
		)
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

	#[test]
	fn test_int_lin_eq_3() {
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
	fn test_lp_ge_pb_triv() {
		test_lp_for_configs(
			r"
Subject To
c0: + 1 x1 + 2 x2 + 1 x3 >= -2
Bounds
0 <= x1 <= 1
0 <= x2 <= 1
0 <= x3 <= 1
End
",
			None,
		);
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
x3
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
    c0: x - y {} 0
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
    c0: x - y {} 0
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
    c0: x - y {} 0
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
				c0: x - y {} 0
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
				c0: x - y {} 0
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
			cutoff: Some(2),
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
			cutoff: None,
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
					Some(String::from("x1")),
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
					Some(String::from("x2")),
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
								Some(String::from("x3")),
							)
							.unwrap(),
					),
				],
			},
			cmp: Comparator::Equal,
			k: 0,
			lbl: None,
		};
		model.add_constraint(con).unwrap();
		test_decomp(model.deep_clone(), &model, None);
	}

	#[test]
	fn test_int_lin_le_big() {
		// test_lp_for_configs(
		// 	r"
		// Subject To
		// c0: + 2 x1 + 3 x2 + 5 x3 + 4 x4 + 7 x5 + 4 x6 + 3 x7 + 8 x8 <= 24
		// Binary
		// x1
		// x2
		// x3
		// x4
		// x5
		// x6
		// x7
		// x8
		// End
		// ",
		// 	None,
		// );

		use rand::distributions::{Distribution, Uniform};
		use rand::{rngs::StdRng, SeedableRng};

		let n = 50;
		let f = 0.7;
		let u = 10;
		let seed = 42;

		// .35
		// statics = [1571/71136/168782]
		// statics = [1373/59602/133084]

		// % .7
		// statics = [1571/38620/103897]
		// statics = [1360/22958/56834]

		let q_sampler = Uniform::from(1..u);
		let mut fixed_seed = StdRng::seed_from_u64(seed);
		let mut sample = |_| q_sampler.sample(&mut fixed_seed);

		let mut model = Model::default();
		let xs = (1..=n)
			.map(|i| {
				model
					.new_var(&[0, sample(0)], Some(format!("x{i}")))
					.unwrap()
			})
			.collect_vec();

		let ub = xs.iter().map(|x| x.borrow().ub()).sum::<Coeff>();

		model
			.add_constraint(Lin {
				exp: LinExp {
					terms: xs.into_iter().map(Term::from).collect(),
				},
				cmp: Comparator::LessEq,
				k: (f * (ub as f32)) as Coeff,
				lbl: None,
			})
			.unwrap();
		test_model(model, Some(get_model_configs()))
	}
}
