#![allow(unused_imports, unused_variables, dead_code, unreachable_code)]
use crate::int::display::SHOW_IDS;
use crate::int::enc::GROUND_BINARY_AT_LB;
use crate::int::helpers::nearest_power_of_two;
use crate::int::{IntVar, IntVarId, IntVarRef, LinExp};
use crate::linear::log_enc_add_;
use crate::{
	helpers::{add_clauses_for, as_binary, negate_cnf, two_comp_bounds, unsigned_binary_range},
	int::{ord::OrdEnc, scm::ScmDecomposer, Dom, TernLeConstraint, TernLeEncoder},
	linear::{clause, log_enc_add_fn, Part},
	trace::emit_clause,
	BddEncoder, CheckError, Checker, ClauseDatabase, Cnf, Coefficient, Comparator, Encoder,
	LimitComp, Literal, PosCoeff, Result, SwcEncoder, TotalizerEncoder, Unsatisfiable,
};
use crate::{IntLinExp, Lin, Term};
use iset::interval_map;
use rustc_hash::FxHashMap;
use std::hash::BuildHasherDefault;

use crate::trace::new_var;
use itertools::{Itertools, Position};
use std::{
	cell::RefCell,
	cmp::Ordering,
	collections::{BTreeSet, HashMap, HashSet},
	ops::{Index, Mul},
	rc::Rc,
};
use std::{fmt::Display, path::PathBuf};

#[cfg(feature = "trace")]
pub(crate) const PRINT_COUPLING: bool = false;
#[cfg(not(feature = "trace"))]
pub(crate) const PRINT_COUPLING: bool = false;
/// In the coupling, skip redundant clauses of which every term is already implied
pub(crate) const REMOVE_IMPLIED_CLAUSES: bool = true;
/// Replace unary constraints by coupling
pub(crate) const USE_COUPLING_IO_LEX: bool = false;

/// View coupling
pub(crate) const VIEW_COUPLING: bool = true;

use iset::IntervalMap;

use super::{
	bin::BinEnc, helpers::filter_fixed, required_lits, IntVarBin, IntVarEnc, IntVarOrd, LitOrConst,
};

pub trait Decompose<Lit: Literal, C: Coefficient> {
	fn decompose(
		&self,
		lin: Lin<Lit, C>,
		num_var: usize,
		model_config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable>;
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Scm {
	#[default]
	Add,
	Rca,
	Pow,
	Dnf,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Decomposer {
	Gt,
	Swc,
	#[default]
	Bdd,
	Rca,
}

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModelConfig<C: Coefficient> {
	pub scm: Scm,
	pub cutoff: Option<C>,
	pub decomposer: Decomposer,
	/// Rewrites all but last equation x:B + y:B ≤ z:B to x:B + y:B = z:B
	pub equalize_ternaries: bool,
	pub add_consistency: bool,
	pub propagate: Consistency,
	/// Rewrites x:B + y:B ≤ z:B to x:B + y:B = z':B ∧ y:B ≤ z:B
	pub equalize_uniform_bin_ineqs: bool,
}

// TODO should we keep IntVar i/o IntVarEnc?
#[derive(Debug, Clone)]
pub struct Model<Lit: Literal, C: Coefficient> {
	pub cons: Vec<Lin<Lit, C>>,
	pub(crate) num_var: usize,
	pub obj: Obj<Lit, C>,
	pub config: ModelConfig<C>,
}

#[derive(Debug, Default, Clone, Eq, PartialEq)]
pub struct Assignment<C: Coefficient>(pub HashMap<IntVarId, (String, C)>);

impl<C: Coefficient> Ord for Assignment<C> {
	fn cmp(&self, other: &Self) -> Ordering {
		self.0.iter().sorted().cmp(other.0.iter().sorted())
	}
}

impl<C: Coefficient> PartialOrd for Assignment<C> {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		Some(self.cmp(other))
	}
}

impl<C: Coefficient> Index<&IntVarId> for Assignment<C> {
	type Output = (String, C);

	fn index(&self, id: &IntVarId) -> &Self::Output {
		&self.0[id]
	}
}

impl<C: Coefficient> Display for Assignment<C> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			self.0
				.iter()
				.sorted()
				.map(|(id, (lbl, a))| format!("{}={}", lbl, a))
				.join(", ")
		)
	}
}

impl<C: Coefficient> Assignment<C> {
	pub(crate) fn partialize(self, max_var: &IntVarId) -> Self {
		Self(self.0.into_iter().filter(|(k, _)| k <= max_var).collect())
	}
}
// impl<C: Coefficient> Index for Assignment<C> {

// }

// TODO Domain will be used once (/if) this is added as encoder feature.
#[allow(dead_code)]
#[derive(Debug, Default, Eq, Ord, PartialOrd, Hash, Clone, PartialEq)]
pub enum Consistency {
	#[default]
	None,
	Bounds,
	Domain,
}

#[derive(Default, Debug, Clone)]
pub enum Obj<Lit: Literal, C: Coefficient> {
	#[default]
	Satisfy,
	Minimize(LinExp<Lit, C>),
	Maximize(LinExp<Lit, C>),
}

impl<Lit: Literal, C: Coefficient> Obj<Lit, C> {
	pub fn obj(&self) -> Option<&LinExp<Lit, C>> {
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

impl<Lit: Literal, C: Coefficient> FromIterator<Model<Lit, C>> for Model<Lit, C> {
	fn from_iter<I: IntoIterator<Item = Model<Lit, C>>>(iter: I) -> Self {
		let mut c = Model::default();

		for i in iter {
			c.extend(i)
		}

		c
	}
}

impl<Lit: Literal, C: Coefficient> Checker for Model<Lit, C> {
	type Lit = Lit;
	fn check(&self, solution: &[Self::Lit]) -> Result<(), CheckError<Self::Lit>> {
		let a = self.assign(solution)?;
		self.cons.iter().try_for_each(|con| con.check(&a))
	}
}

impl<Lit: Literal, C: Coefficient> Default for Model<Lit, C> {
	fn default() -> Self {
		Self {
			cons: vec![],
			num_var: 0,
			obj: Obj::Satisfy,
			config: ModelConfig::default(),
		}
	}
}

impl<Lit: Literal, C: Coefficient> Model<Lit, C> {
	pub fn new(num_var: usize, config: &ModelConfig<C>) -> Self {
		Self {
			num_var,
			config: config.clone(),
			..Model::default()
		}
	}

	pub fn constraints(&'_ self) -> impl Iterator<Item = &'_ Lin<Lit, C>> {
		self.cons.iter()
	}

	pub(crate) fn add_int_var_enc(
		&mut self,
		x: IntVarEnc<Lit, C>,
	) -> Result<IntVarRef<Lit, C>, Unsatisfiable> {
		todo!("cannot get dom anymore from IntVarEnc");
		/*
		let dom = x
			.dom()
			.iter(..)
			.map(|d| d.end - C::one())
			.collect::<Vec<_>>();
		let var = self.new_var(&dom, false, Some(x), None)?;
		// self.vars.insert(var.borrow().id, x);
		Ok(var)
		*/
	}

	pub fn var(
		&mut self,
		dom: &[C],
		lbl: Option<String>,
	) -> Result<IntVarRef<Lit, C>, Unsatisfiable> {
		self.new_var(dom, true, None, lbl)
	}

	pub fn con(
		&mut self,
		terms: &[(C, IntVarRef<Lit, C>)],
		cmp: Comparator,
		k: C,
		lbl: Option<String>,
	) -> Result {
		self.add_constraint(Lin::new(
			&terms
				.iter()
				.cloned()
				.map(|(c, x)| Term::new(c, x))
				.collect::<Vec<_>>(),
			cmp,
			k,
			lbl,
		))
	}

	pub(crate) fn new_var_from_dom(
		&mut self,
		dom: Dom<C>,
		add_consistency: bool,
		e: Option<IntVarEnc<Lit, C>>,
		lbl: Option<String>,
	) -> Result<IntVarRef<Lit, C>, Unsatisfiable> {
		(!dom.is_empty())
			.then(|| {
				self.num_var += 1;
				IntVar::from_dom_as_ref(self.num_var, dom, add_consistency, e, lbl)
			})
			.ok_or(Unsatisfiable)
	}

	pub(crate) fn new_var(
		&mut self,
		dom: &[C],
		add_consistency: bool,
		e: Option<IntVarEnc<Lit, C>>,
		lbl: Option<String>,
	) -> Result<IntVarRef<Lit, C>, Unsatisfiable> {
		self.new_var_from_dom(Dom::from_slice(dom), add_consistency, e, lbl)
	}

	pub fn add_constraint(&mut self, constraint: Lin<Lit, C>) -> Result {
		self.cons.push(constraint.simplified()?);
		Ok(())
	}

	pub fn new_constant(&mut self, c: C) -> IntVarRef<Lit, C> {
		self.new_var(&[c], false, None, None).unwrap()
	}

	pub fn decompose(
		self,
		spec: Option<HashMap<IntVarId, IntVarEnc<Lit, C>>>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		let ModelConfig {
			equalize_ternaries,
			cutoff,
			equalize_uniform_bin_ineqs,
			scm,
			..
		} = self.config.clone();

		let enc = EncSpecDecomposer { cutoff, spec };
		let mut num_var = None;
		self.decompose_with(Some(&LinDecomposer {}))?
			.into_iter()
			.map(|mut con_decomposition| {
				if let Some(num_var) = num_var {
					con_decomposition.num_var = num_var;
				}

				let mut model = con_decomposition
					.decompose_with(Some(&enc))
					.map(|models| models.into_iter().collect::<Model<_, _>>())?;

				// split out uniform binary constraints
				let cons = model.cons.clone();
				if model.cons.is_empty() {
					return Ok(model);
				}

				let (last, firsts) = cons.split_last().unwrap();
				// TODO ub still too high, does not adhere to k (but actually not to next ub if <=, or next lb if >=)

				let model: Model<Lit, C> = Model {
					cons: firsts.to_vec(),
					..model.clone()
				}
				.decompose_with(
					equalize_ternaries
						.then(EqualizeTernsDecomposer::default)
						.as_ref(),
				)?
				.into_iter()
				.chain(std::iter::once({
					const REWRITE_LAST: bool = true;
					if REWRITE_LAST
						&& last.cmp.is_ineq() && last.exp.terms.len() > 1
						&& last
							.vars()
							.iter()
							.all(|x| matches!(x.borrow().e, Some(IntVarEnc::Bin(_))))
					// TODO all?
					{
						let dom = Dom::from_slice(
							&last
								.exp
								.terms
								.iter()
								.map(|t| t.dom().into_iter())
								.multi_cartesian_product()
								.map(|cs| cs.into_iter().reduce(C::add).unwrap())
								.sorted()
								.dedup()
								.collect_vec(),
						);

						// match last.cmp {
						// 	Comparator::LessEq => dom.le(last.k),
						// 	Comparator::Equal => unreachable!(),
						// 	Comparator::GreaterEq => dom.ge(last.k),
						// };

						let y = model
							.new_var_from_dom(
								dom,
								model.config.add_consistency,
								Some(IntVarEnc::Bin(None)),
								last.lbl.as_ref().map(|lbl| format!("last-lhs-{lbl}")),
							)
							.unwrap();

						Model {
							cons: vec![
								Lin {
									exp: LinExp {
										terms: last
											.exp
											.terms
											.iter()
											.cloned()
											.chain(vec![Term::new(-C::one(), y.clone())])
											.collect(),
									},
									cmp: Comparator::Equal,
									k: C::zero(),
									lbl: last.lbl.as_ref().map(|lbl| format!("last-{lbl}")),
								},
								Lin {
									exp: LinExp {
										terms: vec![Term::from(y)],
									},
									..last.clone()
								},
							],
							..model
						}
					} else {
						Model {
							cons: vec![last.clone()],
							..model
						}
					}
				}))
				.collect();

				num_var = Some(model.num_var);
				Ok(model)
			})
			.try_collect::<Model<_, _>, Model<_, _>, _>()?
			.decompose_with(
				equalize_uniform_bin_ineqs
					.then(UniformBinEqDecomposer::default)
					.as_ref(),
			)
			.map(|models| models.into_iter().collect::<Model<_, _>>())?
			.decompose_with((scm == Scm::Dnf).then(ScmDecomposer::default).as_ref())
			.map(|models| models.into_iter().collect())
	}

	pub fn decompose_with(
		self,
		decomposer: Option<&impl Decompose<Lit, C>>,
	) -> Result<Vec<Model<Lit, C>>, Unsatisfiable> {
		decomposer
			.map(|decomposer| {
				let mut num_var = self.num_var;
				self.cons
					.iter()
					.cloned()
					// .map(|con| con.decompose(&self.config, self.num_var).unwrap())
					.map(|con| {
						decomposer
							.decompose(con, num_var, &self.config)
							.map(|decomp| {
								num_var = decomp.num_var; // TODO find better solution for this
								decomp
							})
					})
					.try_collect()
			})
			.unwrap_or(Ok(vec![self])) // None -> identity decomposer
	}

	pub fn encode_vars<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
	) -> Result<(), Unsatisfiable> {
		// Encode (or retrieve encoded) variables (in order of id so lits line up more nicely with variable order)
		self.vars()
			.iter()
			.sorted_by_key(|var| var.borrow().id)
			.try_for_each(|var| {
				var.borrow_mut().decide_encoding(self.config.cutoff);
				var.borrow_mut().encode(db, None).map(|_| ())
			})
	}

	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		decompose: bool,
	) -> Result<Self, Unsatisfiable> {
		// Create decomposed model and its aux vars

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

	pub(crate) fn extend(&mut self, other: Model<Lit, C>) {
		self.config = other.config;
		self.num_var = other.num_var;
		self.cons.extend(other.cons);
	}

	pub fn vars(&self) -> Vec<IntVarRef<Lit, C>> {
		self.cons
			.iter()
			.flat_map(|con| con.exp.terms.iter().map(|term| &term.x)) // don't use con.vars() since this will do redundant canonicalizing
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	pub fn assign(&self, a: &[Lit]) -> Result<Assignment<C>, CheckError<Lit>> {
		self.vars()
			.iter()
			.map(|x| {
				x.borrow()
					.assign(a)
					.map(|a| (x.borrow().id, (x.borrow().lbl(), a)))
			})
			.collect::<Result<HashMap<_, _>, _>>()
			.map(|a| Assignment(a))
	}

	pub fn check_assignment(&self, assignment: &Assignment<C>) -> Result<(), CheckError<Lit>> {
		self.cons.iter().try_for_each(|con| con.check(assignment))
	}

	pub(crate) fn brute_force_solve(&self, max_var: Option<IntVarId>) -> Vec<Assignment<C>> {
		let vars = self.vars();
		let max_var = max_var.unwrap_or(IntVarId(self.num_var));
		vars.iter()
			.map(|var| var.borrow().dom.iter().collect::<Vec<_>>())
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
			// .filter(|a| {
			// 	matches!(
			// 		self.check_assignment(a),
			// 		// Err(CheckError::VarInconsistency(_)) | Ok(())
			// 		Ok(())
			// 	)
			// })
			.map(|a| a.partialize(&max_var))
			.sorted() // need to sort to make unique since HashMap cannot derive Hash
			.dedup()
			.collect()
	}

	/// Expecting actual_assignments to contain all solutions of the model
	pub fn check_assignments(
		&self,
		actual_assignments: &[Assignment<C>],
		expected_assignments: Option<&Vec<Assignment<C>>>,
		lit_assignments: Option<&[Vec<Lit>]>,
		brute_force_solve: bool,
	) -> Result<(), Vec<CheckError<Lit>>> {
		let errs = actual_assignments
			.iter()
			.filter_map(
				|actual_assignment| match self.check_assignment(actual_assignment) {
					Err(CheckError::Fail(e)) => {
						Some(CheckError::Fail(format!("Inconsistency: {e}")))
					}
					// Err(CheckError::VarInconsistency(_)) => None,
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
					actual_assignments.iter().join("\n")
				);
				return Ok(());
			} else {
				return Err(errs);
			}
		}

		let expected_assignments = expected_assignments
			.as_ref()
			.map(|expected_assignments| expected_assignments.to_vec())
			.unwrap_or_else(|| self.brute_force_solve(None));

		let canonicalize = |a: &[Assignment<C>]| a.iter().sorted().cloned().collect::<Vec<_>>();

		let check_unique = |a: &[Assignment<C>], mess: &str| {
			assert!(
				a.iter().sorted().tuple_windows().all(|(a, b)| a != b),
				"Expected unique {mess} assignments but got:\n{}",
				a.iter().map(|a| format!("{}", a)).join("\n")
			)
		};

		let expected_assignments = canonicalize(&expected_assignments);
		check_unique(&expected_assignments, "expected");
		let actual_assignments = canonicalize(actual_assignments);
		// check_unique(&actual_assignments, "actual"); // TODO why not true anymore?

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

	pub fn lits(&self) -> HashSet<Lit> {
		self.vars().iter().flat_map(|x| x.borrow().lits()).collect()
	}

	pub fn with_config(self, config: ModelConfig<C>) -> Self {
		Model { config, ..self }
	}

	pub fn deep_clone(&self) -> Self {
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
}

#[derive(Default)]
pub struct EqualizeTernsDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for EqualizeTernsDecomposer {
	fn decompose(
		&self,
		con: Lin<Lit, C>,
		num_var: usize,
		config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		const REMOVE_GAPS: bool = true;

		Ok(Model {
			cons: vec![if REMOVE_GAPS
				&& con.exp.terms.len() >= 2
				&& con.k.is_zero()
				&& con
					.exp
					.terms
					.iter()
					.all(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
			{
				if let Some((last, firsts)) = con.exp.terms.split_last() {
					// TODO avoid removing gaps on the order encoded vars?
					let (lb, ub) = firsts.iter().fold((C::zero(), C::zero()), |(lb, ub), t| {
						(lb + t.lb(), std::cmp::min(ub + t.ub(), -last.lb()))
					});
					last.x.borrow_mut().dom = Dom::from_bounds(lb, ub);

					Lin {
						exp: LinExp {
							terms: firsts.iter().chain([last]).cloned().collect(),
						},
						cmp: Comparator::Equal,
						..con
					}
				} else {
					unreachable!()
				}
			} else {
				con
			}],
			num_var,
			config: config.clone(),
			..Model::default()
		})
	}
}

#[derive(Default)]
pub struct UniformBinEqDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for UniformBinEqDecomposer {
	fn decompose(
		&self,
		con: Lin<Lit, C>,
		num_var: usize,
		model_config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		let mut model = Model::<Lit, C>::new(num_var, model_config);
		if con.cmp.is_ineq()
			&& con.exp.terms.len() >= 3
			&& con.k.is_zero() // TODO potentially could work for non-zero k
			&& con
				.exp
				.terms
				.iter()
				.all(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
		{
			if let Some((last, firsts)) = con.exp.terms.split_last() {
				// sum all but last term into lhs, where lb(lhs)=lb(sum(firsts)) (to match addition)
				// but ub(lhs) is same if cmp # = <= (because its binding)
				// if # = >=, the ub(lhs) is not binding so set to inf ~= lb(sum(firsts))
				// but the lb(lhs) is, which might be set to low, so we constrain lhs>=lb later
				let lhs = model
					.new_var_from_dom(
						{
							let (lb, ub) =
								firsts.iter().fold((C::zero(), C::zero()), |(lb, ub), t| {
									(lb + t.lb(), ub + t.ub())
								});
							match con.cmp {
								Comparator::LessEq => Dom::from_bounds(lb, last.x.borrow().ub()),
								Comparator::Equal => todo!(),
								Comparator::GreaterEq => Dom::from_bounds(lb, ub),
							}
						},
						true,                       // TODO should be able to set to model_confing.add_consistency
						Some(IntVarEnc::Bin(None)), // annotate to use BinEnc
						Some(format!("eq-{}", last.x.borrow().lbl())), // None,
					)
					.unwrap();

				// sum(firsts) = sum(lhs)
				model.add_constraint(Lin {
					exp: LinExp {
						terms: firsts
							.iter()
							.cloned()
							.chain([Term::new(-C::one(), lhs.clone())])
							.collect(),
					},
					cmp: Comparator::Equal,
					k: C::zero(),
					lbl: con.lbl.clone().map(|lbl| (format!("eq-1-{}", lbl))),
				})?;

				// If # = >=, the original lb is binding!
				if matches!(con.cmp, Comparator::GreaterEq) {
					model.add_constraint(Lin {
						exp: LinExp {
							terms: [Term::new(C::one(), lhs.clone())].to_vec(),
						},
						cmp: Comparator::GreaterEq,
						k: last.x.borrow().lb(),
						lbl: con.lbl.clone().map(|lbl| (format!("eq-1-{}", lbl))),
					})?;
				}

				// if possible, we change the domain of last.x so its binary encoding is grounded at the same lower bound as z_prime so we can constrain bitwise using lex constraint
				// TODO otherwise, coupling will take care of it, but this is non-ideal
				if matches!(last.x.borrow().e, Some(IntVarEnc::Bin(None))) {
					let ub = last.x.borrow().ub();
					let x_dom = last
						.x
						.borrow()
						.dom
						.clone()
						.union(Dom::constant(lhs.borrow().lb()));
					last.x.borrow_mut().dom = x_dom;
				}

				// lhs # rhs
				model.add_constraint(Lin {
					exp: LinExp {
						terms: [Term::new(C::one(), lhs), last.clone()].to_vec(),
					},
					cmp: con.cmp,
					k: C::zero(),
					lbl: con.lbl.clone().map(|lbl| (format!("eq-2-{}", lbl))),
				})?;
			} else {
				unreachable!()
			}
		} else {
			model.add_constraint(con)?;
		}
		Ok(model)
	}
}

#[derive(Debug, Default)]
pub struct EncSpecDecomposer<Lit: Literal, C: Coefficient> {
	cutoff: Option<C>,
	spec: Option<HashMap<IntVarId, IntVarEnc<Lit, C>>>,
}

const COUPLE_SINGLE_VARS: bool = true;
impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for EncSpecDecomposer<Lit, C> {
	fn decompose(
		&self,
		con: Lin<Lit, C>,
		num_var: usize,
		config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		let mut model = Model {
			config: config.clone(),
			num_var,
			..Model::default()
		};

		let encs = con
			.vars()
			.into_iter()
			.map(|x| {
				if let Some(spec) = self.spec.as_ref() {
					// only encode var which are specified
					if let Some(var_enc) = {
						let id = x.borrow().id;
						spec.get(&id)
					} {
						// overwriting encodings
						x.borrow_mut().e = Some(var_enc.clone());
					}
				} else {
					x.borrow_mut().decide_encoding(self.cutoff);
				}
				(
					x.clone(),
					matches!(x.borrow().e.as_ref().unwrap(), IntVarEnc::Ord(_)),
				)
			})
			.collect_vec();

		let mut is_last_term = false;
		let new_con =
            // if mixed encoding of more than 2 terms, couple each xi:O<=yi:B 
			if COUPLE_SINGLE_VARS && encs.len() > 2 && encs.iter().any(|(_, e)| *e) && encs.iter().any(|(_, e)| !e) {
				Lin {
					exp: LinExp {
						terms: con
							.exp
							.terms
							.into_iter()
                            .with_position()
							.map(|(p,t)| {

								let x_enc = t.x.borrow().e.clone();
								let t_new = if let Some(IntVarEnc::Ord(None)) = x_enc {
                                    is_last_term = matches!(p, Position::Last);
                                    Ok(t.encode_bin(Some(&mut model), con.cmp, con.lbl.clone()).unwrap())
								} else {
									Ok(t.clone())
								}?;
								Ok(t_new)
							})
							.try_collect()?,
					},

					..con
				}
			} else {
				con
			};

		Ok(Model {
			cons: if is_last_term {
				[new_con].into_iter().chain(model.cons).collect()
			} else {
				model.cons.into_iter().chain([new_con]).collect()
			},
			..model
		})
	}
}

#[derive(Default)]
pub struct LinDecomposer {}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for LinDecomposer {
	fn decompose(
		&self,
		con: Lin<Lit, C>,
		num_var: usize,
		model_config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		match &con.exp.terms[..] {
			[] => con
				.check(&Assignment(HashMap::default()))
				.map(|_| Model::<Lit, C>::new(num_var, model_config))
				.map_err(|_| Unsatisfiable),
			_ if con.exp.terms.len() <= 2
				|| con.is_tern() || model_config.decomposer == Decomposer::Rca =>
			{
				let mut model = Model::<Lit, C>::new(num_var, model_config);
				model.add_constraint(con)?;
				Ok(model)
			}
			_ => match model_config.decomposer {
				Decomposer::Bdd => BddEncoder::default().decompose(con, num_var, model_config),
				Decomposer::Gt => TotalizerEncoder::default().decompose(con, num_var, model_config),
				Decomposer::Swc => SwcEncoder::default().decompose(con, num_var, model_config),
				Decomposer::Rca => unreachable!(),
			},
		}
	}
}

// impl<Lit: Literal, C: Coefficient> AsRef<IntVarRef<Lit, C>> for IntVar<Lit, C> {
// 	fn as_ref(&self) -> &IntVarRef<Lit, C> {
// 		Rc::new(RefCell::new(self.clone()))
// 	}
// }

#[cfg(test)]
mod tests {
	type Lit = i32;
	type C = i64;

	use super::*;
	use crate::{Cnf, Lin, LinearEncoder, Model};

	#[test]
	fn model_test() {
		let mut model = Model::<Lit, C>::default();
		let x1 = model
			.new_var(&[0, 2], true, None, Some("x1".to_string()))
			.unwrap();
		let x2 = model
			.new_var(&[0, 3], true, None, Some("x2".to_string()))
			.unwrap();
		let x3 = model
			.new_var(&[0, 5], true, None, Some("x3".to_string()))
			.unwrap();
		let k = 6;
		model
			.add_constraint(Lin::new(
				&[Term::new(1, x1), Term::new(1, x2), Term::new(1, x3)],
				Comparator::LessEq,
				k,
				Some(String::from("c1")),
			))
			.unwrap();
		let mut cnf = Cnf::new(0);

		// model.propagate(&Consistency::Bounds);
		model.encode(&mut cnf, true).unwrap();
	}

	use crate::{helpers::tests::TestDB, Format};
	use itertools::{iproduct, Itertools};

	#[cfg(feature = "trace")]
	use traced_test::test;

	fn get_model_configs() -> Vec<ModelConfig<C>> {
		iproduct!(
			// [Scm::Add, Scm::Rca, Scm::Pow, Scm::Dnf],
			// [Decomposer::Gt, Decomposer::Swc, Decomposer::Bdd],
			// [Consistency::None, Consistency::Bounds],
			// [false, true],
			// [None] // smaller number of tests
			// [None, Some(0), Some(2)]
			// [Scm::Add],
			// [Decomposer::Swc],
			// [Consistency::None],
			// [false],
			// [Some(0)] // [None, Some(0), Some(2)]
			[Scm::Dnf],
			[
				// Decomposer::Gt,
				// Decomposer::Swc,
				Decomposer::Bdd,
				// Decomposer::Rca
			],
			// [Consistency::None],
			// [Consistency::None, Consistency::Bounds],
			[Consistency::None],
			[false], // consistency
			// [true],
			// [Some(0), Some(2)] // [None, Some(0), Some(2)]
			[true],  // equalize terns
			[None],  // [None, Some(0), Some(2)]
			[false]  // equalize_uniform_bin_ineqs
		)
		.map(
			|(
				scm,
				decomposer,
				propagate,
				add_consistency,
				equalize_ternaries,
				cutoff,
				equalize_uniform_bin_ineqs,
			)| {
				ModelConfig {
					scm: scm.clone(),
					decomposer: decomposer.clone(),
					propagate: propagate.clone(),
					add_consistency,
					equalize_ternaries,
					cutoff,
					equalize_uniform_bin_ineqs,
					..ModelConfig::default()
				}
			},
		)
		.collect()
	}

	const BRUTE_FORCE_SOLVE: bool = true;
	const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[IntVarEnc::Ord(None), IntVarEnc::Bin(None)];
	// const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[IntVarEnc::Bin(None)];
	// const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[IntVarEnc::Ord(None)];
	// const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[];

	fn test_lp_for_configs(lp: &str, configs: Option<Vec<ModelConfig<C>>>) {
		test_model(
			Model::<Lit, C>::from_string(lp.into(), Format::Lp).unwrap(),
			Some(configs.unwrap_or_else(get_model_configs)),
		)
	}

	fn check_decomposition(
		model: &Model<Lit, C>,
		decomposition: &Model<Lit, C>,
		expected_assignments: Option<&Vec<Assignment<C>>>,
	) {
		if !BRUTE_FORCE_SOLVE {
			return;
		} else if let Err(errs) = model.check_assignments(
			&decomposition.brute_force_solve(Some(IntVarId(model.num_var))),
			expected_assignments,
			None,
			BRUTE_FORCE_SOLVE,
		) {
			for err in errs {
				println!("Decomposition error:\n{err}");
			}
			panic!(
				"Decomposition is incorrect. Test failed for {:?}\n{model}\n{decomposition}",
				model.config,
			);
		}
	}

	fn expand_var_encs(
		var_encs: &[IntVarEnc<Lit, C>],
		vars: Vec<IntVarRef<Lit, C>>,
	) -> Vec<HashMap<IntVarId, IntVarEnc<Lit, C>>> {
		if var_encs.is_empty() {
			return vec![HashMap::default()];
		}
		let var_enc_ids = vars
			.iter()
			.sorted_by_key(|var| var.borrow().id)
			// If not encoded and no encoding preference (e.g. scm), assign and encode
			// TODO maybe remove constants (although some bugs might arise from the different encodings of constants
			.filter(|x| x.borrow().e.is_none())
			.map(|x| x.borrow().id)
			.collect_vec();

		assert!(
			var_enc_ids.len() <= 50,
			"Attempting to test many ({}) var enc specs ({:?})",
			var_enc_ids.len(),
			var_enc_ids
		);

		let var_encs_gen = var_enc_ids
			.iter()
			.map(|_| VAR_ENCS)
			.multi_cartesian_product()
			.map(|var_encs| {
				var_enc_ids
					.iter()
					.cloned()
					.zip(var_encs.into_iter().cloned())
					.collect::<HashMap<_, _>>()
			})
			.collect_vec();

		if var_encs_gen.is_empty() {
			vec![HashMap::default()]
		} else {
			var_encs_gen
		}
	}

	fn test_model(model: Model<Lit, C>, configs: Option<Vec<ModelConfig<C>>>) {
		let expected_assignments = BRUTE_FORCE_SOLVE.then(|| model.brute_force_solve(None));

		// TODO merge with CHECK_DECOMPOSITION_I
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
			let ModelConfig {
				scm,
				cutoff,
				decomposer,
				equalize_ternaries,
				add_consistency,
				propagate,
				equalize_uniform_bin_ineqs,
				..
			} = model.config.clone();

			for (j, var_encs) in {
				let var_encs_gen = expand_var_encs(
					VAR_ENCS,
					model
						.clone()
						.decompose_with(Some(&LinDecomposer::default()))
						.map(|models| models.into_iter().collect::<Model<_, _>>())
						.unwrap()
						.vars()
						.into_iter()
						.collect(),
				);
				if let Some(j) = CHECK_DECOMPOSITION_I {
					vec![(
						j,
						var_encs_gen
							.get(j)
							.expect("CHECK_DECOMPOSITION_I is not set to None")
							.clone(),
					)]
				} else {
					var_encs_gen.into_iter().enumerate().collect_vec()
				}
			} {
				let decomposition = model
					.clone()
					.decompose(if VAR_ENCS.is_empty() {
						None
					} else {
						Some(var_encs)
					})
					.unwrap();

				println!("decomposition = {}", decomposition);

				const CHECK_DECOMPOSITION: bool = true;
				if CHECK_DECOMPOSITION {
					check_decomposition(&model, &decomposition, expected_assignments.as_ref());
				}

				// TODO move into var_encs loop
				const CHECK_CONSTRAINTS: bool = false;
				const SHOW_AUX: bool = true;

				for (mut decomposition, expected_assignments) in if CHECK_CONSTRAINTS {
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
					// let mut con_db = decomp_db.clone();
					// Set num_var to lits in principal vars (not counting auxiliary vars of decomposition)
					// TODO should that be moved after encode step since encoding itself might introduce aux (bool) vars?
					let mut db = TestDB::new(0);

					let principal_vars = decomposition
						.vars()
						.into_iter()
						.filter(|x| x.borrow().id.0 <= model.num_var)
						.map(|x| {
							x.borrow_mut().encode(&mut db, None).unwrap();
							(x.borrow().id.clone(), x.clone())
						})
						.collect::<HashMap<IntVarId, IntVarRef<Lit, C>>>();

					println!("decomposition = {}", decomposition);

					// encode and solve
					let lit_assignments =
						decomposition
							.encode(&mut db, false)
							.map(|_| {
								println!(
								"checking config #{i} = {:?}\ndecomposition #{j} = {} [{}/{}/{}]",
								config, decomposition,
                                db.cnf.variables(), db.cnf.clauses(), db.cnf.literals()
							);

								let output = if CHECK_CONSTRAINTS || SHOW_AUX {
									decomposition.lits()
								} else {
									principal_vars
										.values()
										.flat_map(|x| x.borrow().lits())
										.collect()
								};

								db.solve(Some(output))
									.into_iter()
									.sorted()
									.collect::<Vec<_>>()
							})
							.unwrap_or_else(|_| {
								println!("Warning: encoding decomposition lead to UNSAT");
								// TODO panic based on expected_assignments.is_empty
								Vec::default()
							});

					assert_eq!(
						lit_assignments.iter().unique().count(),
						lit_assignments.len(),
						"Expected lit assignments to be unique, but was {lit_assignments:?}"
					);

					// TODO find way to encode principal variables first (to remove extra solutions that only differe )

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

					let actual_assignments = lit_assignments
						.iter()
						.flat_map(|lit_assignment| checker.assign(lit_assignment))
						.collect::<Vec<_>>();

					// assert_eq!(actual_assignments.iter().unique(), actual_assignments);

					let check = checker.check_assignments(
						&actual_assignments,
						expected_assignments,
						Some(&lit_assignments),
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

	#[test]
	fn test_int_lin_le_single_neg_coef() {
		test_lp_for_configs(
			r"
Subject To
c0: -1 x1 <= -1
Binary
x1
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

	/// Shows the problem for current binary ineq method
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
	fn test_int_lin_le_4_unit_tern() {
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
	fn test_int_lin_eq_1() {
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

	// #[test]
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
c1: + 2 x1 + 5 x3 >= 5
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

	// #[test]
	fn _test_lp_scm_2() {
		test_lp_for_configs(
			r"
Subject To
c0: x1 - 11 x2 = 0
Bounds
0 <= x1 <= 33
0 <= x2 <= 4
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
	fn test_scm_2_117() {
		test_lp_for_configs(
			r"
	Subject To
	c0: 117 x_1 = 0
	Bounds
	0 <= x_1 <= 3
	End
	",
			None,
		);
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

	#[test]
	fn test_two_neg() {
		// - (x1:O ∈ |0..1| 1L) ≥ - (x2:O ∈ |0..1| 1L)
		test_lp_for_configs(
			r"
Subject To
  c0: - x1 - x2 >= 0
  \ c0: - x1 + x2 >= 0
  \ c0: x1 - x2 <= 0
Binary
  x1
  x2
End
",
			None,
		);
	}

	#[test]
	fn test_couple_view() {
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
			scm: Scm::Rca,
			cutoff: None,
			decomposer: Decomposer::Rca,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: false,
			equalize_uniform_bin_ineqs: false,
		};
		// Expected output only has 1 (!) clause (3, -4)

		for cmp in ["<=", ">="] {
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
				y in 2,3,4,5
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
	}

	#[test]
	fn test_tmp_whiteboard() {
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
	fn test_sugar() {
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
	fn test_sugar_3() {
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
	  c0: - 1 x1 - 1 x2 >= 0
	Bounds
	  0 <= x1 <= 1
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
	fn test_sugar_pbc() {
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

		test_lp_for_configs(
			r"
	Subject To
	  c0: -1 x1 >= 0
	Bounds
	  0 <= x1 <= 1
	End
	",
			Some(vec![base.clone()]),
		);

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

		test_lp_for_configs(
			r"
	Subject To
	  c0: - 1 x1 <= -1
	Bounds
	  0 <= x1 <= 1
	End
	",
			Some(vec![base.clone()]),
		);
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

		test_lp_for_configs(
			r"
	Subject To
	  c0: -1 x1 >= -1
	Bounds
	  0 <= x1 <= 3
	End
	",
			Some(vec![base.clone()]),
		);

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

		test_lp_for_configs(
			r"
	Subject To
	  c0: - 1 x1 <= -3
	Bounds
	  0 <= x1 <= 3
	End
	",
			Some(vec![base.clone()]),
		);
	}

	// #[test]
	// fn test_ineqs() {
	// 	let mut db = TestDB::new(0);
	// 	let mut model = Model::<Lit, C>::default();
	// 	let t = Term::new(1, model.new_var(&[-2, 3, 5], true, None, None).unwrap());
	// 	t.x.borrow_mut().e = Some(IntVarEnc::Bin(None));
	// 	t.x.borrow_mut()
	// 		.encode(&mut db, &mut HashMap::new())
	// 		.unwrap();
	// 	// let x = BinEnc::new(&mut db, 4, Some(String::from("x")));
	// }
}
