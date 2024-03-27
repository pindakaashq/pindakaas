#![allow(unused_imports, unused_variables, dead_code, unreachable_code)]
use crate::int::display::SHOW_IDS;
use crate::int::enc::GROUND_BINARY_AT_LB;
use crate::linear::log_enc_add_;
use crate::{
	helpers::{add_clauses_for, as_binary, negate_cnf, two_comp_bounds, unsigned_binary_range},
	int::{ord::OrdEnc, scm::ScmDecomposer, Dom, TernLeConstraint, TernLeEncoder},
	linear::{clause, log_enc_add_fn, Part},
	trace::emit_clause,
	BddEncoder, CheckError, Checker, ClauseDatabase, Cnf, Coefficient, Comparator, Encoder,
	LimitComp, Literal, PosCoeff, Result, SwcEncoder, TotalizerEncoder, Unsatisfiable,
};
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

const DECOMPOSE: bool = true;

use iset::IntervalMap;

use super::{
	bin::BinEnc, helpers::filter_fixed, required_lits, IntVarBin, IntVarEnc, IntVarOrd, LitOrConst,
};

#[derive(Hash, Copy, Clone, Debug, PartialEq, Eq, Default, PartialOrd, Ord)]
pub struct IntVarId(pub usize);

pub type IntVarRef<Lit, C> = Rc<RefCell<IntVar<Lit, C>>>;

impl Display for IntVarId {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

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

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Assignment<C: Coefficient>(pub HashMap<IntVarId, C>);

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
	type Output = C;

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
				.map(|(id, a)| format!("x_{}={}", id, a))
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
				Rc::new(RefCell::new(IntVar::from_dom(
					self.num_var,
					dom,
					add_consistency,
					e,
					lbl,
				)))
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
		self.cons.push(constraint);
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
		self.decompose_with(Some(&LinDecomposer {}))?
			.into_iter()
			.map(|con_decomposition| {
				let model = con_decomposition
					.decompose_with(Some(&enc))
					.map(|models| models.into_iter().collect::<Model<_, _>>())?;

				let (last, firsts) = model.cons.split_last().unwrap();
				let (con_eqs, cons) = firsts.iter().cloned().partition(|con| {
					con.exp
						.terms
						.iter()
						.any(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_))))
				});
				// .with_position()
				// .partition(|(pos, con)| match pos {
				// 	Position::First | Position::Middle => con
				// 		.exp
				// 		.terms
				// 		.iter()
				// 		.any(|t| matches!(t.x.borrow().e, Some(IntVarEnc::Bin(_)))),

				// 	Position::Last => false,
				// });

				Model {
					cons: con_eqs,
					..model.clone() // not wasteful I think because shouldn't clone cons
				}
				.decompose_with(
					equalize_ternaries
						.then(EqualizeTernsDecomposer::default)
						.as_ref(),
				)
				.map(|models| {
					let mut model = models
						.into_iter()
						.chain([Model {
							cons: [cons, vec![last.clone()]].concat(),
							..model
						}])
						.collect::<Model<_, _>>();
					model.cons.sort_by_key(|con| con.exp.terms[1].x.borrow().id); // dirty trick to restore order
					model
				})
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
		let mut all_views = HashMap::new();
		self.vars()
			.iter()
			.sorted_by_key(|var| var.borrow().id)
			.try_for_each(|var| {
				var.borrow_mut().decide_encoding(self.config.cutoff);
				var.borrow_mut().encode(db, &mut all_views).map(|_| ())
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
			con.encode(db, &self.config).unwrap();
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
			.map(|x| x.borrow().assign(a).map(|a| (x.borrow().id, a)))
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
						.map(|var| var.borrow().id)
						.zip(a)
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
		expected_assignments: Option<&[Assignment<C>]>,
		lit_assignments: Option<Vec<Vec<Lit>>>,
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
		if !errs.is_empty() && expected_assignments.is_none() {
			return Err(errs);
		}

		let expected_assignments = expected_assignments
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
			.unwrap()
			.0
			.keys()
			.collect::<HashSet<_>>();

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

#[derive(Debug, Clone, Default)]
pub struct LinExp<Lit: Literal, C: Coefficient> {
	pub terms: Vec<Term<Lit, C>>,
}

#[derive(Debug, Clone)]
pub struct Lin<Lit: Literal, C: Coefficient> {
	pub exp: LinExp<Lit, C>,
	pub cmp: Comparator,
	pub k: C,
	pub lbl: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Term<Lit: Literal, C: Coefficient> {
	pub c: C,
	pub x: IntVarRef<Lit, C>,
}

impl<Lit: Literal, C: Coefficient> Mul<C> for Term<Lit, C> {
	type Output = Self;
	fn mul(self, rhs: C) -> Self {
		Self {
			x: self.x,
			c: self.c * rhs,
		}
	}
}

impl<Lit: Literal, C: Coefficient> From<IntVarRef<Lit, C>> for Term<Lit, C> {
	fn from(value: IntVarRef<Lit, C>) -> Self {
		Term::new(C::one(), value)
	}
}

impl<Lit: Literal, C: Coefficient> Term<Lit, C> {
	pub fn new(c: C, x: IntVarRef<Lit, C>) -> Self {
		Self { c, x }
	}

	fn handle_polarity(&self, cmp: &Comparator) -> bool {
		// (cmp == &Comparator::GreaterEq) == self.c.is_positive()
		match cmp {
			Comparator::GreaterEq => self.c.is_positive(),
			Comparator::LessEq => !self.c.is_positive(),
			Comparator::Equal => unimplemented!(),
		}
	}

	// pub fn constant(c: C) -> Self {
	// Self::new(C::one(), Rc::new(RefCell::new(IntVar::new)))
	// }

	pub fn ineqs(&self, cmp: &Comparator) -> Vec<(C, Vec<Vec<Lit>>)> {
		// TODO merge or handle repeated literals
		let up = self.handle_polarity(cmp);
		let x_dom = &self.x.borrow().dom;
		match self
			.x
			.borrow()
			.e
			.as_ref()
			.unwrap_or_else(|| panic!("{} was not encoded", self.x.borrow()))
		{
			IntVarEnc::Ord(Some(o)) => self.dom().into_iter().zip(o.ineqs(up)).collect(),
			IntVarEnc::Bin(Some(b)) => {
				// TODO not (particularly) optimized for the domain of x, but this is tricky as the domain values go outside the binary encoding ranges
				// go over x's bounds
				let (range_lb, range_ub) = if GROUND_BINARY_AT_LB {
					// (C::zero(), x_dom.ub() - x_dom.lb())
					unsigned_binary_range(b.bits())
				} else {
					let is_two_comp = x_dom.lb().is_negative();
					if is_two_comp {
						two_comp_bounds(b.bits())
					} else {
						unsigned_binary_range::<C>(b.bits())
					}
				};

				// normalize domain
				// TODO
				// let dom = x_dom.clone().add(-self.lb());
				let dom = Dom::from_bounds(range_lb, range_ub);

				// get conjunction for every k in lb..dom (or k in dom..ub)
				let xs = b.ineqs(up, dom);

				// hard-code first (or last) fixed term bound literal
				let xs = if up {
					[(range_lb, vec![])]
						.into_iter()
						.chain(xs[1..].iter().cloned())
						.collect_vec()
				} else {
					xs[..xs.len() - 1]
						.iter()
						.cloned()
						.chain([(range_ub, vec![])])
						.collect_vec()
				};

				// b.ineqs returns range values -> (de!)normalize to x's dom values and then to term's values (by multiplying by coefficient)
				xs.into_iter()
					.map(|(k, conjunction)| ((k + x_dom.lb()) * self.c, conjunction))
					.collect()
			}
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
			IntVarEnc::Const(_) => todo!(),
		}
	}

	/// Return CNF for c*x>=k (or c*x<=k)
	pub fn ineq(&self, k: C, cmp: &Comparator) -> Vec<Vec<Lit>> {
		// we get the position of a*x >= c == x >= ceil(c/a) if cmp = >= and a >= 0; either might flip it to x <= floor(c/a)
		let up = self.handle_polarity(cmp);

		// }

		let k = if up {
			k.div_ceil(&self.c)
		} else {
			k.div_floor(&self.c)
		};

		// TODO move into IntVar since self.c is taken care off?
		match self.x.borrow().e.as_ref().unwrap() {
			IntVarEnc::Ord(Some(o)) => o.ineq(self.x.borrow().dom.ineq(k, up), up),
			IntVarEnc::Bin(Some(b)) => {
				// x>=k == ¬(x<k) == ¬(x<=k-1) (or x<=k == ¬(x>k) == ¬(x>=k+1))
				let k = if up { k - C::one() } else { k + C::one() };
				let k = b.normalize(k, &self.x.borrow().dom);

				let (range_lb, range_ub) = unsigned_binary_range(b.bits());
				let k = if up { (range_lb, k) } else { (k, range_ub) };
				let k = (std::cmp::max(range_lb, k.0), std::cmp::min(range_ub, k.1)); // TODO temp
				let k = Dom::from_bounds(k.0, k.1);

				b.ineqs(!up, k)
					.into_iter()
					.map(|(_, cnf)| cnf)
					.flat_map(|cnf| negate_cnf(cnf))
					.collect()
			}
			IntVarEnc::Const(_) => todo!(),

			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
		}
		// self.x[c].clone()
		// if (cmp == &Comparator::LessEq) == self.c.is_positive() {
		//     self.x[0].clone()
		// }
	}

	/*
		// TODO move enc into Term ?
		// TODO clippy
		#[allow(clippy::type_complexity)]
		pub(crate) fn encode<DB: ClauseDatabase<Lit = Lit>>(
			&self,
			db: &mut DB,
			config: &ModelConfig<C>,
		) -> Result<(Vec<IntVarEnc<DB::Lit, C>>, C), Unsatisfiable> {
			let enc = self.x.borrow().e.as_ref().unwrap().clone();
			if self.c == C::zero() {
				Ok((vec![IntVarEnc::Const(C::zero())], C::zero()))
			} else if self.c == C::one() {
				Ok((vec![enc.clone()], C::zero()))
			} else {
				match enc {
					IntVarEnc::Ord(o) => Ok((vec![IntVarEnc::Ord(o.mul(db, self.c))], C::zero())),
					IntVarEnc::Bin(x_enc) => {
						// handle negative coefficient
						let (mut c, xs, k, dom) = if !self.c.is_negative() {
							(
								self.c,
								x_enc.xs(false),
								C::zero(),
								Dom::from_slice(
									&self
										.x
										.borrow()
										.dom
										.iter()
										.map(|d| self.c * d)
										.sorted()
										.collect::<Vec<_>>(),
								),
							)
						} else {
							(
								-self.c,
								x_enc.xs(false).into_iter().map(|x| -x).collect(), // 2-comp
								-self.c, // return constant addition `-c` because `-c*x = c* -x = c* (1-~x) = c - c*~x`
								Dom::from_slice(
									&self
										.x
										.borrow()
										.dom
										.iter()
										.map(|d| self.c * d + self.c)
										// -1 * {0,1} = {-1,0} = {-2,-1} + 1
										// [b,F] in {0,1} = [!b,T] in {-2,-1}
										.sorted()
										.collect::<Vec<_>>(),
								),
							)
						};

						// TODO shift by zeroes..
						let mut sh = 0;

						while c.is_even() {
							sh += 1;
							c = c.div(C::one() + C::one());
						}

						let lits = match config.scm {
							Scm::Add | Scm::Dnf => x_enc.lits(),
							Scm::Rca | Scm::Pow => 0,
						};

						let scm = match config.scm {
							_ if c.is_one() => Some(vec![]),
							Scm::Add | Scm::Rca => SCM
								.iter()
								.find_map(|(bits, mul, scm)| {
									(*bits == lits && C::from(*mul).unwrap() == c).then_some(scm)
								})
								.map(|v| v.to_vec()),
							Scm::Pow => None,
							Scm::Dnf => {
								let cnf = Cnf::<DB::Lit>::from_file(&PathBuf::from(format!(
									"{}/res/ecm/{lits}_{c}.dimacs",
									env!("CARGO_MANIFEST_DIR")
								)))
								.unwrap_or_else(|_| {
									panic!("Could not find Dnf method cnf for {lits}_{c}")
								});
								let map = cnf
									.vars()
									.zip(
										xs.iter()
											.flat_map(|x| match x {
												LitOrConst::Lit(l) => Some(l.clone()),
												_ => None,
											})
											.chain(
												(0..(cnf.variables() - lits))
													.map(|_i| {
														new_var!(
															db,
															format!(
																"{}_y_{}",
																self.x.borrow().lbl(),
																_i
															)
														)
													})
													.collect::<Vec<_>>(),
											),
									)
									.collect::<HashMap<_, _>>();
								cnf.iter().try_for_each(|clause| {
									emit_clause!(
										db,
										&clause
											.iter()
											.map(|x| {
												let lit = &map[&x.var()];
												if x.is_negated() {
													lit.negate()
												} else {
													lit.clone()
												}
											})
											.collect::<Vec<_>>()
									)
								})?;
								return Ok((
									vec![IntVarEnc::Bin(IntVarBin::from_lits(
										&num::iter::range(C::zero(), C::from(sh).unwrap())
											.map(|_| LitOrConst::Const(false))
											.chain(
												map.values()
													.sorted()
													.skip(lits)
													.cloned()
													.map(LitOrConst::from),
											)
											.collect::<Vec<_>>(),
										dom,
										format!("{}*{}", self.c.clone(), self.x.borrow().lbl()),
									))],
									k,
								));
							}
						};

						// if we have no recipe for this particular (b,c) key, in which case we fallback to Pow
						let scm = if let Some(scm) = scm {
							scm
						} else {
							assert!(
								matches!(config.scm, Scm::Pow),
								"Current SCM DB is complete but could not find {c} for {lits}"
							);
							return Ok((
								as_binary(c.into(), None)
									.into_iter()
									.enumerate()
									.filter_map(|(shift, b)| b.then_some(sh + shift))
									.map(|sh| {
										let xs = num::iter::range(C::zero(), C::from(sh).unwrap())
											.map(|_| LitOrConst::Const(false))
											.chain(xs.clone())
											.collect::<Vec<_>>();
										IntVarEnc::Bin(IntVarBin::from_lits(
											&xs,
											x_enc.dom.clone().mul(C::one().shl(sh)),
											format!("{}<<{}", self.x.borrow().lbl(), sh.clone()),
										))
									})
									.collect(),
								k,
							));
						};

						// TODO store `c` value i/o of node index
						let mut ys = [(C::zero(), xs)].into_iter().collect::<HashMap<_, _>>();

						let get_and_shift =
							|ys: &HashMap<C, Vec<LitOrConst<DB::Lit>>>, i: C, sh: usize| {
								(0..sh)
									.map(|_| LitOrConst::Const(false))
									.chain(
										ys.get(&i)
											.unwrap_or_else(|| {
												panic!("ys[{i}] does not exist in {ys:?} when encoding SCM {c}*x of {lits} lits")
											})
											.clone(),
									)
									.collect::<Vec<_>>()
							};

						for rca in scm {
							let (i, i1, sh1, i2, sh2) = (
								C::from(rca.i).unwrap(),
								C::from(rca.i1).unwrap(),
								rca.sh1 as usize,
								C::from(rca.i2).unwrap(),
								rca.sh2 as usize,
							);
							let (z_i, x, add, y) = (
								i,
								get_and_shift(&ys, i1, sh1),
								rca.add,
								get_and_shift(&ys, i2, sh2),
							);

							// If subtracting, use 2-comp of y and set initial carry to true
							let (y, c) = if add {
								(y, false)
							} else {
								(y.into_iter().map(|l| -l).collect(), true)
							};

							let z = log_enc_add_fn(db, &x, &y, &Comparator::Equal, c.into(), None)?;
							ys.insert(z_i, z);
						}

						let xs = get_and_shift(&ys, *ys.keys().max().unwrap(), sh);
						Ok((
							vec![IntVarEnc::Bin(IntVarBin::from_lits(
								&xs,
								dom,
								format!("{}*{}", self.c, self.x.borrow().lbl()),
							))],
							k,
						))
					}
					IntVarEnc::Const(c) => Ok((vec![IntVarEnc::Const(c * self.c)], C::zero())),
				}
			}
		}
	*/

	pub fn lb(&self) -> C {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().ub()
			} else {
				self.x.borrow().lb()
			})
	}

	pub(crate) fn ub(&self) -> C {
		self.c
			* (if self.c.is_negative() {
				self.x.borrow().lb()
			} else {
				self.x.borrow().ub()
			})
	}

	// TODO [?] correct way to return iter?
	pub(crate) fn dom(&self) -> Vec<C> {
		if self.c.is_zero() {
			vec![C::zero()]
		} else {
			let mut d = self.x.borrow().dom.iter().map(|d| self.c * d).collect_vec();
			if self.c.is_negative() {
				d.reverse() // TODO implement reverse iterator
			}
			d
		}
	}

	pub(crate) fn size(&self) -> C {
		self.x.borrow().size()
	}
}

impl<Lit: Literal, C: Coefficient> Lin<Lit, C> {
	pub fn new(terms: &[Term<Lit, C>], cmp: Comparator, k: C, lbl: Option<String>) -> Self {
		Lin {
			exp: LinExp {
				terms: terms.to_vec(),
			},
			cmp,
			k,
			lbl,
		}
	}

	pub fn tern(
		x: Term<Lit, C>,
		y: Term<Lit, C>,
		cmp: Comparator,
		z: Term<Lit, C>,
		lbl: Option<String>,
	) -> Self {
		Lin {
			exp: LinExp {
				terms: vec![x, y, Term::new(-z.c, z.x)],
			},
			cmp,
			k: C::zero(),
			lbl,
		}
	}

	pub fn decompose(
		self,
		model_config: &ModelConfig<C>,
		num_var: usize,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		LinDecomposer::default().decompose(self, num_var, model_config)
		// let decomp = LinDecomposer::default().decompose(self, num_var, model_config)?;
	}

	pub fn lb(&self) -> C {
		self.exp.terms.iter().map(Term::lb).fold(C::zero(), C::add)
	}

	pub fn ub(&self) -> C {
		self.exp.terms.iter().map(Term::ub).fold(C::zero(), C::add)
	}

	pub(crate) fn propagate(
		&mut self,
		consistency: &Consistency,
	) -> Result<Vec<IntVarId>, Unsatisfiable> {
		let mut changed = vec![];
		match consistency {
			Consistency::None => unreachable!(),
			Consistency::Bounds => loop {
				let mut fixpoint = true;
				self.cmp.split().into_iter().try_for_each(|cmp| {
					match cmp {
						Comparator::LessEq => {
							let rs_lb = self.lb() - self.k;
							for term in &self.exp.terms {
								let mut x = term.x.borrow_mut();
								let size = x.size();
								let x_lb = if term.c.is_positive() {
									x.dom.lb()
								} else {
									x.dom.ub()
								};

								let id = x.id;

								// c*d <= c*x_lb - rs_lb
								// d <= x_lb - (rs_lb / c) (or d >= .. if d<0)
								let b = x_lb - (rs_lb / term.c);

								if term.c.is_negative() {
									x.ge(&b);
								} else {
									x.le(&b);
								}

								if x.size() < size {
									//println!("Pruned {}", size - x.size());
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == C::zero() {
									return Err(Unsatisfiable);
								}
							}
							Ok(())
						}
						Comparator::GreaterEq => {
							let xs_ub = self.ub() - self.k;
							for term in &self.exp.terms {
								let mut x = term.x.borrow_mut();
								let size = x.size();

								let id = x.id;
								let x_ub = if term.c.is_positive() {
									x.dom.ub()
								} else {
									x.dom.lb()
								};

								// c*d >= x_ub*c + xs_ub := d >= x_ub - xs_ub/c
								let b = x_ub - (xs_ub / term.c);

								if !term.c.is_negative() {
									x.ge(&b);
								} else {
									x.le(&b);
								}

								if x.size() < size {
									changed.push(id);
									fixpoint = false;
								}
								if x.size() == C::zero() {
									return Err(Unsatisfiable);
								}
							}
							Ok(())
						}
						_ => unreachable!(),
					}
				})?;

				if fixpoint {
					return Ok(changed);
				}
			},
			Consistency::Domain => {
				todo!()
				/*
				assert!(self.cmp == Comparator::Equal);
				loop {
					let mut fixpoint = true;
					for (i, term) in self.exp.terms.iter().enumerate() {
						let id = term.x.borrow().id;
						term.x.borrow_mut().dom.retain(|d_i| {
							if self
								.exp
								.terms
								.iter()
								.enumerate()
								.filter_map(|(j, term_j)| {
									(i != j).then(|| {
										term_j
											.x
											.borrow()
											.dom
											.iter()
											.map(|d_j_k| term_j.c * *d_j_k)
											.collect::<Vec<_>>()
									})
								})
								.multi_cartesian_product()
								.any(|rs| {
									term.c * *d_i + rs.into_iter().fold(C::zero(), |a, b| a + b)
										== C::zero()
								}) {
								true
							} else {
								fixpoint = false;
								changed.push(id);
								false
							}
						});
						assert!(term.x.borrow().size() > 0);
					}

					if fixpoint {
						return changed;
					}
				}
				*/
			}
		}
	}

	pub(crate) fn is_tern(&self) -> bool {
		let cs = self.exp.terms.iter().map(|term| term.c).collect::<Vec<_>>();
		cs.len() == 3 && cs[2] == -C::one() && self.k.is_zero()
	}

	fn check(&self, a: &Assignment<C>) -> Result<(), CheckError<Lit>> {
		let lhs = self
			.exp
			.terms
			.iter()
			.map(|term| term.c * a[&term.x.borrow().id])
			.fold(C::zero(), C::add);

		if match self.cmp {
			Comparator::LessEq => lhs <= self.k,
			Comparator::Equal => lhs == self.k,
			Comparator::GreaterEq => lhs >= self.k,
		} {
			Ok(())
		} else {
			Err(CheckError::Fail(format!(
				"Inconsistency in {}: {} == {} !{} {}",
				self.lbl.clone().unwrap_or_default(),
				self.exp
					.terms
					.iter()
					.map(|term| {
						format!(
							"{} * {}={} (={})",
							term.c,
							term.x.borrow().lbl(),
							a[&term.x.borrow().id],
							term.c * a[&term.x.borrow().id],
						)
					})
					.join(" + "),
				lhs,
				self.cmp,
				self.k
			)))
		}
	}

	fn _is_simplified(&self) -> bool {
		self.exp
			.terms
			.iter()
			.all(|term| !term.c.is_zero() && !term.x.borrow().is_constant())
	}

	fn into_tern(self) -> Self {
		Lin {
			exp: LinExp {
				terms: self
					.exp
					.terms
					.into_iter()
					.with_position()
					.map(|pos| match pos {
						(Position::Last, term) => term * -C::one(),
						(_, term) => term, // also matches Only element; so unary constraints are not minused
					})
					.collect(),
			},
			..self
		}
	}

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&self,
		db: &mut DB,
		config: &ModelConfig<C>,
	) -> Result {
		const PRINT_COUPLING: bool = false;
		if PRINT_COUPLING {
			println!("{self}");
		}

		// TODO only one cmp == Equality (and exchange equalities)
		let term_encs = self
			.exp
			.terms
			.iter()
			.map(|t| (t, t.x.borrow().e.clone()))
			// TODO hopefully does not clone inner enc?
			.collect_vec();

		match (&term_encs[..], self.cmp) {
			([(Term { c, x }, Some(IntVarEnc::Bin(_)))], _) if c.is_one() => {
				let x_enc = x.borrow_mut().encode_bin(db)?; // avoid BorrowMutError
				x_enc.encode_unary_constraint(db, &self.cmp, self.k, &x.borrow().dom, false)
			}
			// SCM
			(
				[(Term { c, x }, _), (Term { c: y_c, x: y }, Some(IntVarEnc::Bin(None)))],
				Comparator::Equal,
			) if *y_c == -C::one()
				&& self.k.is_zero()
				&& matches!(y.borrow().e, Some(IntVarEnc::Bin(_))) =>
			{
				let x_enc = x.borrow_mut().encode_bin(db)?;
				assert!(matches!(y.borrow().e, Some(IntVarEnc::Bin(None))));
				let lits = x_enc.lits().len(); // TODO use max(), but requires coercing Lit to usize later for skip(..)
				let sh = c.trailing_zeros();
				let c = c.shr(sh as usize);
				if c.is_one() {
					y.borrow_mut().e = Some(IntVarEnc::Bin(Some(BinEnc::from_lits(
						&(0..sh)
							.map(|_| LitOrConst::Const(false))
							.chain(x_enc.xs().iter().cloned())
							.collect_vec(),
					))));
					return Ok(());
				}

				let y_lits = scm_dnf(db, x_enc.xs(), lits, c)?;

				// set encoding of y
				let y_enc = IntVarEnc::Bin(Some(BinEnc::from_lits(
					&(0..sh)
						.map(|_| LitOrConst::Const(false))
						.chain(y_lits.into_iter().map(LitOrConst::from))
						.collect_vec(),
				)));
				y.borrow_mut().e = Some(y_enc);
				if y.borrow().add_consistency {
					y.borrow().consistent(db)?;
				}

				Ok(())
			}
			(
				[(x, Some(IntVarEnc::Bin(_))), (y, Some(IntVarEnc::Bin(_))), (z, Some(IntVarEnc::Bin(_)))],
				Comparator::Equal,
			) if [x.c, y.c, z.c] == [C::one(), C::one(), -C::one()] => {
				assert!(
					x.lb() + y.lb() == ((*z).clone() * -C::one()).lb(),
					"LBs for addition not matching: {self}"
				);
				// TODO do not have to encode z if we use functional addition!
				let (x, y, z) = &self
					.exp
					.terms
					.iter()
					// .with_position()
					.map(|t| t.x.borrow_mut().encode_bin(db).unwrap().xs())
					.collect_tuple()
					.unwrap();

				log_enc_add_(db, x, y, &self.cmp, z)
			}
			_ => {
				// encode all variables
				self.exp.terms.iter().try_for_each(|t| {
					t.x.borrow_mut()
						.encode(db, &mut HashMap::default())
						.map(|_| ())
				})?;

				self.cmp.split().into_iter().try_for_each(|cmp| {
					let conditions = &self.exp.terms[..self.exp.terms.len() - 1];
					let consequent = self.exp.terms.last().unwrap();

					[vec![(C::zero(), vec![])]] // handle empty conditions
						.into_iter()
						.chain(conditions.iter().map(|term| term.ineqs(&cmp.reverse())))
						.multi_cartesian_product()
						.try_for_each(|conditions| {
							// calculate x>=k-sum(conditions)
							let k =
								self.k - conditions.iter().map(|(c, _)| *c).fold(C::zero(), C::add);
							let cons = consequent.ineq(k, &cmp);

							if PRINT_COUPLING {
								println!(
									"\t({}) -> {}*{}{}{} {:?}",
									conditions
										.iter()
										.skip(1)
										.zip(&self.exp.terms)
										.map(|(c, t)| format!(
											"{}{}{} {:?}",
											t.x.borrow().lbl(),
											cmp.reverse(),
											c.0,
											c.1
										))
										.join(" /\\ "),
									consequent.c,
									self.exp.terms.last().unwrap().x.borrow().lbl(),
									cmp,
									k,
									cons
								);
							}

							add_clauses_for(
								db,
								conditions
									.iter()
									.map(|(_, cnf)| negate_cnf(cnf.clone())) // negate conditions
									.chain([cons])
									.collect(),
							)
						})
				})
			}
		}
	}

	pub fn vars(&self) -> Vec<IntVarRef<Lit, C>> {
		self.exp
			.terms
			.iter()
			.map(|term| &term.x)
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	/*
		#[cfg_attr(
			feature = "trace",
			tracing::instrument(name = "lin_encoder", skip_all, fields(constraint = format!("{}", self)))
		)]
		pub fn _encode<DB: ClauseDatabase<Lit = Lit>>(
			&self,
			db: &mut DB,
			config: &ModelConfig<C>,
		) -> Result {
			// TODO assert simplified/simplify
			// assert!(self._is_simplified());

			let mut encoder = TernLeEncoder::default();
			// TODO use binary heap

			if config.decomposer == Decomposer::Rca || config.scm == Scm::Pow {
				assert!(config.cutoff == Some(C::zero()));
				let mut k = self.k;
				let mut encs = self
					.clone()
					.exp
					.terms
					.into_iter()
					.flat_map(|term| {
						term.encode(db, config).map(|(xs, c)| {
							k -= c;
							xs.into_iter()
								.filter(|x| {
									if let IntVarEnc::Const(c) = x {
										k -= *c;
										false
									} else {
										true
									}
								})
								.collect_vec()
						})
					})
					.flatten()
					.collect::<Vec<_>>();
				assert!(
					encs.iter().all(|e| matches!(e, IntVarEnc::Bin(_))),
					"{encs:?}"
				);

				if self
					.exp
					.terms
					.iter()
					.all(|term| matches!(term.x.borrow().e.as_ref().unwrap(), IntVarEnc::Bin(_)))
				{
					// TODO hard to do in a reduce ..
					// TODO Replace 0 for first element

					encs.sort_by_key(IntVarEnc::ub);
					while encs.len() > 1 {
						let x = encs.pop().unwrap();
						let z = if let Some(y) = encs.pop() {
							x.add(db, &mut encoder, &y, None, None)?
						} else {
							x
						};

						encs.insert(
							encs.iter()
								.position(|enc| z.ub() < enc.ub())
								.unwrap_or(encs.len()),
							z,
						);
						debug_assert!(encs.windows(2).all(|x| x[0].ub() <= x[1].ub()));
					}

					assert!(encs.len() == 1);
					encoder.encode(
						db,
						&TernLeConstraint::new(
							&encs.pop().unwrap(),
							&IntVarEnc::Const(C::zero()),
							&self.cmp,
							&IntVarEnc::Const(k),
						),
					)?;
				}
				return Ok(());
			}

			let mut k = self.k;
			let encs = self
				.clone()
				// Encodes terms into ternary constrain (i.e. last term is multiplied by -1)
				.into_tern()
				.exp
				.terms
				.into_iter()
				.with_position()
				.flat_map(|(pos, term)| {
					term.encode(db, config).map(|(xs, c)| {
						match pos {
							Position::Last => {
								k += c;
							}
							_ => {
								k -= c;
							}
						}
						xs
					})
				})
				.flatten()
				.collect::<Vec<_>>();

			// TODO generalize n-ary encoding; currently using fallback of TernLeEncoder
			return match &encs[..] {
				[] => return Ok(()),
				[x] if DECOMPOSE => encoder.encode(
					db,
					&TernLeConstraint::new(
						x,
						&IntVarEnc::Const(C::zero()),
						&self.cmp,
						&IntVarEnc::Const(k),
					),
				),
				[x, z] if DECOMPOSE => encoder.encode(
					db,
					&TernLeConstraint::new(x, &IntVarEnc::Const(-k), &self.cmp, z),
				),
				[x, y, z] if DECOMPOSE => {
					let z = z.add(db, &mut encoder, &IntVarEnc::Const(k), None, None)?;
					encoder.encode(db, &TernLeConstraint::new(x, y, &self.cmp, &z))
				}
				_ => {
					assert!(
						encs.iter()
							.all(|enc| matches!(enc, IntVarEnc::Ord(_) | IntVarEnc::Const(_))),
						"TODO: {encs:?}"
					);

					// just get encoding; does not need to handle terms coefficient here
					// let encs = self
					// 	.clone()
					// 	.exp
					// 	.terms
					// 	.into_iter()
					// 	.map(|term| {
					// 		term.x.borrow_mut().encode(db, &mut HashMap::new(), true)?;
					// 		Ok(term.x.borrow().e.as_ref().unwrap().clone())
					// 	})
					// 	.collect::<Result<Vec<_>>>()?;
					// TODO support binary
					self.cmp.split().into_iter().try_for_each(|cmp| {
						let is_leq = matches!(cmp, Comparator::LessEq);

						// encs[0..encs.len() - 1]
						self.exp
							.terms
							.iter()
							// .zip(&self.exp.terms)
							.map(|term| {
								term.ineqs(&Comparator::GreaterEq)
								// if is_leq == term.c.is_positive() {
								// 	term.geqs()
								// } else {
								// 	term.leqs()
								// }
							})
							.multi_cartesian_product()
							.try_for_each(|geqs| {
								let rhs = geqs
									.iter()
									.zip(&self.exp.terms)
									.map(|((d, _), term)| {
										if is_leq == term.c.is_positive() {
											term.c * (d.end - C::one())
										} else {
											term.c * d.start
										}
									})
									.fold(self.k, C::sub);

								let conditions = geqs
									.iter()
									.map(|(_, cnf)| negate_cnf(cnf.clone()))
									.collect::<Vec<_>>();

								let (last_enc, last_c) =
									(&encs[encs.len() - 1], &self.exp.terms[encs.len() - 1].c);

								let last = if is_leq == last_c.is_positive() {
									last_enc.leq_(rhs.div_ceil(last_c))
								} else {
									last_enc.geq_(rhs.div_floor(last_c))
								};

								let cnf = conditions.iter().cloned().chain([last]).collect();
								add_clauses_for(db, cnf)
							})
					})
				}
			};
		}
	*/
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
			cons: vec![Lin {
				cmp: Comparator::Equal,
				exp: if REMOVE_GAPS {
					if let Some((last, firsts)) = con.exp.terms.split_last() {
						// 						let x_dom = last
						// 							.x
						// 							.borrow()
						// 							.dom
						// 							.clone()
						// 							.union(Dom::from_slice(&[lb, ub]));
						// 						last.x.borrow_mut().dom = x_dom;

						// TODO avoid removing gaps on the order encoded vars?
						// if matches!(last.x.borrow().e, Some(IntVarEnc::Bin(_))) {
						// }
						let (lb, ub) = firsts.iter().fold((C::zero(), C::zero()), |(lb, ub), t| {
							(lb + t.lb(), ub + t.ub())
						});
						assert!(last.c.abs().is_one());
						last.x.borrow_mut().dom = Dom::from_bounds(lb, ub);

						LinExp {
							terms: firsts.iter().chain([last]).cloned().collect(),
						}
					} else {
						unreachable!()
					}
				} else {
					con.exp
				},
				..con
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
			&& con.exp.terms.len() == 3
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

#[derive(Default)]
pub struct EncSpecDecomposer<Lit: Literal, C: Coefficient> {
	cutoff: Option<C>,
	spec: Option<HashMap<IntVarId, IntVarEnc<Lit, C>>>,
}

impl<Lit: Literal, C: Coefficient> Decompose<Lit, C> for EncSpecDecomposer<Lit, C> {
	fn decompose(
		&self,
		con: Lin<Lit, C>,
		num_var: usize,
		config: &ModelConfig<C>,
	) -> Result<Model<Lit, C>, Unsatisfiable> {
		con.vars().into_iter().for_each(|var| {
			if let Some(spec) = self.spec.as_ref() {
				// only encode var which are specified
				if let Some(var_enc) = {
					let id = var.borrow().id;
					spec.get(&id)
				} {
					// overwriting encodings
					var.borrow_mut().e = Some(var_enc.clone());
				}
			} else {
				var.borrow_mut().decide_encoding(self.cutoff);
			}
		});
		Ok(Model {
			cons: vec![con],
			config: config.clone(),
			num_var,
			..Model::default()
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

// TODO perhaps id can be used by replacing vars HashMap to just vec
// TODO why can't we derive Default without impl. for Lit (since it's in Option?)
#[derive(Debug, Clone)]
pub struct IntVar<Lit: Literal, C: Coefficient> {
	pub id: IntVarId,
	pub dom: Dom<C>,
	pub(crate) add_consistency: bool,
	pub(crate) views: HashMap<C, (IntVarId, C)>,
	pub(crate) e: Option<IntVarEnc<Lit, C>>,
	// pub(crate) x: OrdEnc<Lit>,
	lbl: Option<String>,
}

// TODO implement Eq so we don't compare .e

impl<Lit: Literal, C: Coefficient> IntVar<Lit, C> {
	pub(crate) fn new(
		id: usize,
		dom: &[C],
		add_consistency: bool,
		e: Option<IntVarEnc<Lit, C>>,
		lbl: Option<String>,
	) -> Self {
		Self::from_dom(id, Dom::from_slice(dom), add_consistency, e, lbl)
	}

	pub(crate) fn from_dom(
		id: usize,
		dom: Dom<C>,
		add_consistency: bool,
		e: Option<IntVarEnc<Lit, C>>,
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

	fn into_ref(self) -> IntVarRef<Lit, C> {
		Rc::new(RefCell::new(self))
	}

	#[cfg_attr(
		feature = "trace",
		tracing::instrument(name = "consistency", skip_all, fields(constraint = format!("{}", self)))
	)]
	pub(crate) fn consistent<DB: ClauseDatabase<Lit = Lit>>(&self, db: &mut DB) -> Result {
		self.e
			.as_ref()
			.map(|e| e.consistent(db, &self.dom))
			.unwrap_or(Ok(()))
	}

	pub(crate) fn as_lin_exp(&self) -> crate::linear::LinExp<Lit, C> {
		match self.e.as_ref().unwrap() {
			IntVarEnc::Ord(Some(o)) => {
				crate::linear::LinExp::new()
					.add_chain(
						&self
							.dom
							.iter()
							.zip(o.ineqs(true))
							.tuple_windows()
							// Every lit adds the difference
							.map(|((prev, _), (v, cnf))| (cnf[0][0].clone(), v - prev))
							.collect::<Vec<_>>(),
					)
					.add_constant(self.lb())
			}
			IntVarEnc::Bin(Some(b)) => {
				let (terms, add) = b.as_lin_exp::<C>();
				// The offset and the fixed value `add` are added to the constant
				let add = if GROUND_BINARY_AT_LB {
					add + self.lb()
				} else if !self.dom.lb().is_negative() {
					add
				} else {
					add.checked_add(&two_comp_bounds::<C>(b.bits()).0).unwrap()
				};

				let (lb, ub) = if GROUND_BINARY_AT_LB {
					(C::zero() + add, self.ub() - self.lb() + add)
				} else {
					(self.lb() - add, self.ub() - add)
				};

				let lin_exp = crate::linear::LinExp::<Lit, C>::new().add_bounded_log_encoding(
					terms.as_slice(),
					// The Domain constraint bounds only account for the unfixed part of the offset binary notation
					lb,
					ub,
				);

				lin_exp.add_constant(add)
			}
			IntVarEnc::Ord(None) | IntVarEnc::Bin(None) => panic!("Expected encoding"),
			IntVarEnc::Const(c) => crate::linear::LinExp::new().add_constant(*c),
		}
	}

	pub fn assign(&self, a: &[Lit]) -> Result<C, CheckError<Lit>> {
		crate::linear::LinExp::from(self).assign(a)
		// match  {
		// 	IntVarEnc::Ord(o) => LinExp::from(o).assign
		// 	IntVarEnc::Bin(_) => todo!(),
		// 	IntVarEnc::Const(c) => Ok(*c),
		// }

		// .assign(a)
	}
	pub fn is_constant(&self) -> bool {
		self.size() == C::one()
	}

	pub(crate) fn lits(&self) -> HashSet<Lit> {
		self.e.as_ref().map(|e| e.lits()).unwrap_or_default()
	}

	fn encode_bin<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
	) -> Result<BinEnc<Lit>, Unsatisfiable> {
		self.encode(db, &mut HashMap::default()).map(|e| match e {
			IntVarEnc::Bin(Some(b)) => b,
			_ => unreachable!(),
		})
	}

	fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		views: &mut HashMap<(IntVarId, C), Lit>,
	) -> Result<IntVarEnc<Lit, C>, Unsatisfiable> {
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
				required_lits::<C>(self.dom.lb(), self.dom.ub()),
				self.lbl.clone(),
			))),
			Some(IntVarEnc::Const(_)) => todo!(),
		};

		self.e = Some(e.clone());

		if self.add_consistency {
			self.consistent(db)?;
		}

		Ok(e)
	}

	// TODO should not be C i/o &C?
	fn fix(&mut self, q: &C) -> Result {
		if self.dom.contains(*q) {
			self.dom = Dom::from_slice(&[*q]);
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}

	fn ge(&mut self, bound: &C) {
		self.dom.ge(*bound);
	}

	fn le(&mut self, bound: &C) {
		self.dom.le(*bound);
	}

	pub(crate) fn size(&self) -> C {
		self.dom.size()
	}

	pub fn lb(&self) -> C {
		self.dom.lb()
	}

	pub fn ub(&self) -> C {
		self.dom.ub()
	}

	fn decide_encoding(&mut self, cutoff: Option<C>) -> IntVarEnc<Lit, C> {
		if let Some(e) = self.e.as_ref() {
			return e.clone();
		}
		self.e = Some(match cutoff {
			None => IntVarEnc::Ord(None),
			Some(cutoff) if cutoff == C::zero() => IntVarEnc::Bin(None),
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
	#[allow(private_interfaces)]
	pub fn from_part<DB: ClauseDatabase<Lit = Lit>>(
		db: &mut DB,
		model: &mut Model<DB::Lit, C>,
		xs: &Part<Lit, PosCoeff<C>>,
		ub: PosCoeff<C>,
		lbl: String,
	) -> Result<IntVarRef<Lit, C>, Unsatisfiable> {
		match xs {
			Part::Amo(terms) => {
				let terms: Vec<(PosCoeff<C>, Lit)> = terms
					.iter()
					.map(|(lit, coef)| (coef.clone(), lit.clone()))
					.collect();
				// for a set of terms with the same coefficients, replace by a single term with fresh variable o (implied by each literal)
				let mut h: FxHashMap<C, Vec<Lit>> =
					FxHashMap::with_capacity_and_hasher(terms.len(), BuildHasherDefault::default());
				for (coef, lit) in terms {
					debug_assert!(coef <= ub);
					h.entry(*coef).or_default().push(lit);
				}

				let (dom, lits): (Vec<_>, Vec<_>) = h
					.into_iter()
					.sorted_by(|(a, _), (b, _)| a.cmp(b))
					// .tuple_windows()
					// .map(|((prev, _), (coef, lits))| {
					.map(|(coef, lits)| {
						// let interval = (prev + C::one())..(coef + C::one());
						if lits.is_empty() {
							(coef, None)
						} else if lits.len() == 1 {
							(coef, Some(lits[0].clone()))
						} else {
							let o = new_var!(db, format!("y_{:?}>={:?}", lits, coef));
							for lit in lits {
								emit_clause!(db, &[lit.negate(), o.clone()]).unwrap();
							}
							(coef, Some(o))
						}
					})
					.unzip();
				model.new_var(
					&[C::zero()].into_iter().chain(dom).collect_vec(),
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
			Part::Ic(terms) => {
				todo!();
				let mut acc = C::zero(); // running sum
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
							// ((prev + C::one())..(coef + C::one()), Some(lit))
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
			}
			Part::Dom(terms, l, u) => {
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
								interval_map! { C::one()..(**coef+C::one()) => Some(lit.clone()) },
								format!("{lbl}^{i}"),
							))
						})
						.collect()
				}
				*/
			} // TODO Not so easy to transfer a binary encoded int var
			  // Part::Dom(terms, l, u) => {
			  // let coef = (terms[0].1);
			  // let false_ if (coef > 1).then(|| let false_ = Some(new_var!(db)); emit_clause!(&[-false_]); false_ });
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

// impl<Lit: Literal, C: Coefficient> AsRef<IntVarRef<Lit, C>> for IntVar<Lit, C> {
// 	fn as_ref(&self) -> &IntVarRef<Lit, C> {
// 		Rc::new(RefCell::new(self.clone()))
// 	}
// }

#[cfg_attr(
	feature = "trace",
	tracing::instrument(name = "scm_dnf", skip_all, fields(constraint = format!("DNF:{lits}_{c}")))
)]
fn scm_dnf<DB: ClauseDatabase, C: Coefficient>(
	db: &mut DB,
	xs: Vec<LitOrConst<DB::Lit>>,
	lits: usize,
	c: C,
) -> Result<Vec<DB::Lit>, Unsatisfiable> {
	let cnf = Cnf::<DB::Lit>::from_file(&PathBuf::from(format!(
		"{}/res/ecm/{lits}_{c}.dimacs",
		env!("CARGO_MANIFEST_DIR")
	)))
	.unwrap_or_else(|_| panic!("Could not find Dnf method cnf for {lits}_{c}"));
	// TODO could replace with some arithmetic
	let map = cnf
		.vars()
		.zip_longest(xs.iter())
		.flat_map(|yx| match yx {
			itertools::EitherOrBoth::Both(x, y) => match y {
				LitOrConst::Lit(y) => Some((x, y.clone())),
				LitOrConst::Const(_) => None,
			},
			itertools::EitherOrBoth::Left(x) => Some((x.clone(), new_var!(db, format!("scm_{x}")))),
			itertools::EitherOrBoth::Right(_) => unreachable!(),
		})
		.collect::<HashMap<_, _>>();

	// add clauses according to Dnf
	cnf.iter().try_for_each(|clause| {
		emit_clause!(
			db,
			&clause
				.iter()
				.map(|x| {
					let lit = &map[&x.var()];
					if x.is_negated() {
						lit.negate()
					} else {
						lit.clone()
					}
				})
				.collect::<Vec<_>>()
		)
	})?;

	Ok(map.into_values().sorted().skip(lits).collect())
}

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
			[Scm::Rca, Scm::Dnf],
			[
				Decomposer::Gt,
				// Decomposer::Swc,
				Decomposer::Bdd,
				Decomposer::Rca
			],
			// [Consistency::None],
			// [Consistency::None, Consistency::Bounds],
			[Consistency::None],
			[false, true], // consistency
			// [true],
			// [Some(0), Some(2)] // [None, Some(0), Some(2)]
			[false, true], // equalize terns
			[None],        // [None, Some(0), Some(2)]
			[false]        // equalize_uniform_bin_ineqs
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

	const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[IntVarEnc::Ord(None), IntVarEnc::Bin(None)];
	// const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[IntVarEnc::Bin(None)];
	// const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[IntVarEnc::Ord(None)];
	// const VAR_ENCS: &[IntVarEnc<Lit, C>] = &[];

	fn test_lp_for_configs(lp: &str, configs: Option<Vec<ModelConfig<C>>>) {
		let model = Model::<Lit, C>::from_string(lp.into(), Format::Lp).unwrap();
		let expected_assignments = model.brute_force_solve(None);
		for config in configs.unwrap_or_else(get_model_configs) {
			assert!(
				model.num_var <= 10,
				"Attempting to test many (2^{}) var enc specs",
				model.num_var
			);

			test_lp(
				lp,
				TestDB::new(0),
				model.deep_clone().with_config(config.clone()),
				Some(&expected_assignments),
			)
		}
	}

	fn check_decomposition(
		model: &Model<Lit, C>,
		decomposition: &Model<Lit, C>,
		expected_assignments: Option<&[Assignment<C>]>,
	) {
		if let Err(errs) = model.check_assignments(
			&decomposition.brute_force_solve(Some(IntVarId(model.num_var))),
			expected_assignments,
			None,
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

	fn test_lp(
		lp: &str,
		db: TestDB,
		model: Model<Lit, C>,
		expected_assignments: Option<&[Assignment<C>]>,
	) {
		println!("model = {model}");
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

		const CHECK_DECOMPOSITION_I: Option<usize> = None;

		for (i, var_encs) in {
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
			if let Some(i) = CHECK_DECOMPOSITION_I {
				vec![(i, var_encs_gen[i].clone())]
			} else {
				var_encs_gen.into_iter().enumerate().collect_vec()
			}
		} {
			let spec = if VAR_ENCS.is_empty() {
				None
			} else {
				Some(var_encs)
			};

			let decomposition = model.clone().decompose(spec).unwrap();

			println!("decomposition = {}", decomposition);

			const CHECK_DECOMPOSITION: bool = true;
			if CHECK_DECOMPOSITION {
				check_decomposition(&model, &decomposition, expected_assignments);
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
				vec![(decomposition.clone(), expected_assignments)]
			} {
				// let mut con_db = decomp_db.clone();
				// Set num_var to lits in principal vars (not counting auxiliary vars of decomposition)
				// TODO should that be moved after encode step since encoding itself might introduce aux (bool) vars?
				let mut con_db = db.clone();

				let principal_vars = decomposition
					.vars()
					.into_iter()
					.filter(|x| x.borrow().id.0 <= model.num_var)
					.map(|x| {
						x.borrow_mut()
							.encode(&mut con_db, &mut HashMap::default())
							.unwrap();
						(x.borrow().id.clone(), x.clone())
					})
					.collect::<HashMap<IntVarId, IntVarRef<Lit, C>>>();

				println!("decomposition = {}", decomposition);

				// encode and solve
				let lit_assignments = decomposition
					.encode(&mut con_db, false)
					.map(|_| {
						println!("checking decomposition #{i} = {}", decomposition);

						let output = if CHECK_CONSTRAINTS || SHOW_AUX {
							decomposition.lits()
						} else {
							principal_vars
								.values()
								.flat_map(|x| x.borrow().lits())
								.collect()
						};

						con_db
							.solve(Some(output))
							.into_iter()
							.sorted()
							.collect::<Vec<_>>()
					})
					.unwrap_or_else(|_| {
						println!("Warning: encoding decomposition lead to UNSAT");
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
					Some(lit_assignments),
				);
				if let Err(errs) = check {
					for err in errs {
						println!("{err}");
					}
					panic!(
						"Encoding is incorrect. Test failed for {:?} and {lp}",
						model.config
					);
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

	#[test]
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

	#[test]
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
c0: + 2 x1 + 3 x2 + 2 x3 >= 4
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
	fn test_mixed_enc_bdd() {
		let base = ModelConfig {
			scm: Scm::Rca,
			cutoff: Some(2),
			decomposer: Decomposer::Bdd,
			add_consistency: false,
			propagate: Consistency::None,
			equalize_ternaries: true,
			equalize_uniform_bin_ineqs: false,
		};
		test_lp_for_configs(
			r"
Subject To
    c0: 2 x_1 + 2 x_2 + 2 x_3 + 2 x_4 <= 5
    \ c0: 2 x_1 + 2 x_2 + 2 x_3 <= 3
Binary
    x_1
    x_2
    x_3
    x_4
End
	",
			// None,
			Some(vec![
				base.clone(),
				// ModelConfig {
				// 	equalize_ternaries: true,
				// 	..base
				// },
			]),
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
	// 	// dbg!(t.ineqs(&Comparator::LessEq));
	// 	// let x = BinEnc::new(&mut db, 4, Some(String::from("x")));
	// }
}
