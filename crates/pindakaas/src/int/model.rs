use crate::{
	helpers::{add_clauses_for, as_binary, negate_cnf},
	int::{Dom, TernLeConstraint, TernLeEncoder},
	linear::log_enc_add_fn,
	trace::emit_clause,
	BddEncoder, CheckError, Checker, ClauseDatabase, Cnf, Coefficient, Comparator, Encoder,
	Literal, Result, SwcEncoder, TotalizerEncoder, Unsatisfiable,
};

use crate::trace::new_var;
use itertools::{Itertools, Position};
use std::{
	cell::RefCell,
	cmp::Ordering,
	collections::{BTreeSet, HashMap},
	ops::{Index, Mul},
	rc::Rc,
};
use std::{fmt::Display, path::PathBuf};

const DECOMPOSE: bool = true;

use iset::IntervalMap;

use super::{scm::SCM, IntVarBin, IntVarEnc, IntVarOrd, LitOrConst};

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
		&mut self,
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
	pub add_consistency: bool,
	pub propagate: Consistency,
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
		let dom = x
			.dom()
			.iter(..)
			.map(|d| d.end - C::one())
			.collect::<Vec<_>>();
		let var = self.new_var(&dom, false, Some(x), None)?;
		// self.vars.insert(var.borrow().id, x);
		Ok(var)
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

	pub(crate) fn new_var(
		&mut self,
		dom: &[C],
		add_consistency: bool,
		e: Option<IntVarEnc<Lit, C>>,
		lbl: Option<String>,
	) -> Result<IntVarRef<Lit, C>, Unsatisfiable> {
		(!dom.is_empty())
			.then(|| {
				self.num_var += 1;
				Rc::new(RefCell::new(IntVar {
					id: IntVarId(self.num_var),
					dom: Dom::from_slice(dom),
					add_consistency,
					views: HashMap::default(),
					e,
					lbl,
				}))
			})
			.ok_or(Unsatisfiable)
	}

	pub fn add_constraint(&mut self, constraint: Lin<Lit, C>) -> Result {
		self.cons.push(constraint);
		Ok(())
	}

	pub fn new_constant(&mut self, c: C) -> IntVarRef<Lit, C> {
		self.new_var(&[c], false, None, None).unwrap()
	}

	pub fn decompose(self) -> Result<Model<Lit, C>, Unsatisfiable> {
		// TODO aggregate constants + encode trivial constraints
		// let mut model = Model::new(self.num_var);
		// model.vars = self.vars.clone(); // TODO we should design the interaction between the model (self) and the decomposed model better (by consuming self?)

		let mut num_var = self.num_var;
		let cons = self
			.cons
			.iter()
			.cloned()
			.map(|con| {
				con.decompose(&self.config, num_var)
					.map(|(cons, new_num_var)| {
						num_var = new_num_var;
						cons
					})
			})
			.flatten_ok()
			.flatten()
			.collect::<Vec<_>>();
		Ok(Model {
			cons,
			num_var,
			..self
		})
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
				let prefer_order = var.borrow().prefer_order(self.config.cutoff);
				var.borrow_mut().encode(db, &mut all_views, prefer_order)
			})
	}

	pub fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
	) -> Result<Self, Unsatisfiable> {
		// Create decomposed model and its aux vars

		let mut decomposition = self.clone().decompose()?;

		self.propagate(&self.config.propagate.clone())?;

		decomposition.encode_vars(db)?;

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
		self.num_var = other.num_var;
		self.cons.extend(other.cons);
	}

	pub fn vars(&self) -> Vec<IntVarRef<Lit, C>> {
		self.cons
			.iter()
			.flat_map(|con| con.exp.terms.iter().map(|term| &term.x))
			.unique_by(|x| x.borrow().id)
			.cloned()
			.collect()
	}

	pub fn assign(&self, a: &[Lit]) -> Result<Assignment<C>, CheckError<Lit>> {
		self.vars()
			.iter()
			.map(|x| x.borrow().assign(a).map(|a| (x.borrow().id, a)))
			.collect::<Result<HashMap<_, _>, _>>() // TODO weird it can't infer type
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
	) -> Result<(), Vec<CheckError<Lit>>> {
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
		if !errs.is_empty() && expected_assignments.is_none() {
			return Err(errs);
		}

		let expected_assignments = expected_assignments
			.map(|expected_assignments| expected_assignments.to_vec())
			.unwrap_or_else(|| self.brute_force_solve(None));

		let canonicalize = |a: &[Assignment<C>]| a.iter().sorted().cloned().collect::<Vec<_>>();

		let expected_assignments = canonicalize(&expected_assignments);
		let actual_assignments = canonicalize(actual_assignments);

		// TODO unnecessary canonicalize?
		let extra_int_assignments = canonicalize(
			&actual_assignments
				.iter()
				.filter(|a| !expected_assignments.contains(a))
				.cloned()
				.collect::<Vec<_>>(),
		);

		let missing_int_assignments = canonicalize(
			&expected_assignments
				.iter()
				.filter(|a| !actual_assignments.contains(a))
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
Inconsistencies:
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
						.join("\n")
				))])
				.collect());
		}

		assert_eq!(actual_assignments,
                   expected_assignments,
                   "It seems the actual and expected assignments are not identical sets:\nactual:\n{}\n expected:\n{}",
                   actual_assignments.iter().join("\n"),
                   expected_assignments.iter().join("\n")
                  );

		Ok(())
	}

	pub fn lits(&self) -> usize {
		self.vars().iter().map(|x| x.borrow().lits()).sum::<usize>()
	}

	pub fn with_config(self, config: ModelConfig<C>) -> Self {
		Model { config, ..self }
	}
}

#[derive(Debug, Clone)]
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
		self.x.borrow().dom.iter().map(|d| self.c * d).collect()
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
	) -> Result<(Vec<Lin<Lit, C>>, usize), Unsatisfiable> {
		match &self.exp.terms[..] {
			[] => Ok((vec![], num_var)),
			[term] if false => {
				match self.cmp {
					Comparator::LessEq => {
						term.x.borrow_mut().le(&C::zero());
					}
					Comparator::Equal => {
						term.x.borrow_mut().fix(&C::zero())?;
					}
					Comparator::GreaterEq => {
						term.x.borrow_mut().ge(&C::zero());
					}
				};
				todo!("Untested code: fixing of vars from unary constraints");
				// Ok(vec![])
			}
			_ if self.exp.terms.len() <= 3 => Ok((vec![self], num_var)),
			_ => {
				let new_model = match model_config.decomposer {
					Decomposer::Bdd => BddEncoder::default().decompose(self, num_var, model_config),
					Decomposer::Gt => {
						TotalizerEncoder::default().decompose(self, num_var, model_config)
					}
					Decomposer::Swc => SwcEncoder::default().decompose(self, num_var, model_config),
					Decomposer::Rca => return Ok((vec![self], num_var)), // dodgy skip decomposition for SCM
				}?;
				Ok((new_model.cons, new_model.num_var))
			}
		}
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
				match self.cmp {
					Comparator::Equal => vec![true, false],
					Comparator::LessEq => vec![true],
					Comparator::GreaterEq => vec![false],
				}
				.into_iter()
				.try_for_each(|is_leq| {
					if is_leq {
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
					} else {
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
					}
					Ok(())
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

	pub(crate) fn _is_tern(&self) -> bool {
		let cs = self.exp.terms.iter().map(|term| term.c).collect::<Vec<_>>();
		cs.len() == 3
			&& cs[0].is_positive()
			&& cs[1].is_positive()
			&& cs[2].is_negative()
			&& self.k.is_zero()
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
		// TODO assert simplified/simplify
		// assert!(self._is_simplified());

		let mut encoder = TernLeEncoder::default();
		// TODO use binary heap

		if config.decomposer == Decomposer::Rca {
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
						xs
					})
				})
				.flatten()
				.collect::<Vec<_>>();
			assert!(encs.iter().all(|e| matches!(e, IntVarEnc::Bin(_))));

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
					encs.iter().all(|enc| matches!(enc, IntVarEnc::Bin(_))),
					"TODO: {encs:?}"
				);

				// just get encoding; does not need to handle terms coefficient here
				let encs = self
					.clone()
					.exp
					.terms
					.into_iter()
					.map(|term| {
						term.x.borrow_mut().encode(db, &mut HashMap::new(), true)?;
						Ok(term.x.borrow().e.as_ref().unwrap().clone())
					})
					.collect::<Result<Vec<_>>>()?;
				// TODO support binary
				match self.cmp {
					Comparator::Equal => vec![true, false],
					Comparator::LessEq => vec![true],
					Comparator::GreaterEq => vec![false],
				}
				.into_iter()
				.try_for_each(|is_leq| {
					encs[0..encs.len() - 1]
						.iter()
						.zip(&self.exp.terms)
						.map(|(enc, term)| {
							if is_leq == term.c.is_positive() {
								enc.geqs()
							} else {
								enc.leqs()
							}
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

							add_clauses_for(db, conditions.iter().cloned().chain([last]).collect())
						})
				})
			}
		};
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
	lbl: Option<String>,
}

// TODO implement Eq so we don't compare .e

impl<Lit: Literal, C: Coefficient> IntVar<Lit, C> {
	pub fn assign(&self, a: &[Lit]) -> Result<C, CheckError<Lit>> {
		self.e.as_ref().unwrap().assign(a)
	}
	pub fn is_constant(&self) -> bool {
		self.size() == C::one()
	}

	#[allow(dead_code)]
	pub(crate) fn lits(&self) -> usize {
		self.e.as_ref().map(IntVarEnc::lits).unwrap_or(0)
	}

	fn encode<DB: ClauseDatabase<Lit = Lit>>(
		&mut self,
		db: &mut DB,
		views: &mut HashMap<(IntVarId, C), Lit>,
		prefer_order: bool,
	) -> Result<(), Unsatisfiable> {
		if self.e.is_some() {
			return Ok(());
		};

		self.e = Some(if self.is_constant() {
			IntVarEnc::Const(self.dom.lb())
		} else {
			let e = if prefer_order {
				let dom = self
					.dom
					.iter()
					.sorted()
					.tuple_windows()
					.map(|(a, b)| (a + C::one())..(b + C::one()))
					.map(|v| (v.clone(), views.get(&(self.id, v.end - C::one())).cloned()))
					.collect::<IntervalMap<_, _>>();
				IntVarEnc::Ord(IntVarOrd::from_views(db, dom, self.lbl()))
			} else {
				let y = IntVarBin::from_dom(db, self.dom.clone(), self.lbl());
				IntVarEnc::Bin(y)
			};

			if self.add_consistency {
				e.consistent(db).unwrap();
			}

			for view in self
				.views
				.iter()
				.map(|(c, (id, val))| ((*id, *val), e.geq(*c..(*c + C::one()))))
			{
				// TODO refactor
				if !view.1.is_empty() {
					views.insert(view.0, view.1[0][0].clone());
				}
			}
			e
		});
		Ok(())
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

	fn prefer_order(&self, cutoff: Option<C>) -> bool {
		match cutoff {
			None => true,
			Some(cutoff) if cutoff == C::zero() => false,
			Some(cutoff) => self.dom.size() < cutoff,
		}
	}

	pub fn lbl(&self) -> String {
		self.lbl.clone().unwrap_or_else(|| format!("x{}", self.id))
	}
}

#[cfg(test)]
mod tests {
	type Lit = i32;
	type C = i64;

	use super::*;
	use crate::{Cnf, Lin, Model};

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
		model.encode(&mut cnf).unwrap();
	}

	use crate::{helpers::tests::TestDB, Format};
	use itertools::{iproduct, Itertools};

	#[cfg(feature = "trace")]
	use traced_test::test;

	fn get_model_configs() -> Vec<ModelConfig<C>> {
		iproduct!(
			[Scm::Add, Scm::Rca, Scm::Pow, Scm::Dnf],
			[Decomposer::Gt, Decomposer::Swc, Decomposer::Bdd],
			[Consistency::None, Consistency::Bounds],
			[false, true]
			[Scm::Rca],
			[Decomposer::Rca],
			[Consistency::None],
			[false],
			[Some(0)] // [None, Some(0), Some(2)]
		)
		.map(
			|(scm, decomposer, propagate, add_consistency, cutoff)| ModelConfig {
				scm: scm.clone(),
				decomposer: decomposer.clone(),
				propagate: propagate.clone(),
				add_consistency,
				cutoff,
				..ModelConfig::default()
			},
		)
		.collect()
	}

	fn test_lp_for_configs(lp: &str) {
		let model = Model::<Lit, C>::from_string(lp.into(), Format::Lp).unwrap();
		let expected_assignments = model.brute_force_solve(None);
		for config in get_model_configs() {
			test_lp(
				lp,
				Model::<Lit, C>::from_string(lp.into(), Format::Lp)
					.unwrap()
					.with_config(config),
				Some(&expected_assignments),
			)
		}
	}

	fn test_lp(lp: &str, mut model: Model<Lit, C>, expected_assignments: Option<&[Assignment<C>]>) {
		println!("model = {model}");

		let mut db = TestDB::new(0);
		model.encode_vars(&mut db).unwrap(); // Encode vars beforehand so db.num_var lines up

		let lit_assignments = if let Ok(decomposition) = model.encode(&mut db) {
			println!("decomposition = {}", decomposition);

			// Check decomposition
			const CHECK_DECOMPOSITION: bool = true;
			if CHECK_DECOMPOSITION {
				if let Err(errs) = model.check_assignments(
					&decomposition.brute_force_solve(Some(IntVarId(model.num_var))),
					expected_assignments,
				) {
					for err in errs {
						println!("Decomposition error:\n{err}");
					}
					panic!(
						"Decomposition is incorrect. Test failed for {:?} and {lp}\n{model}\n{decomposition}",
						model.config,
					);
				}
			}

			// Set num_var to lits in principal vars (not counting auxiliary vars of decomposition)
			db.num_var = model.lits() as Lit;
			db.solve().into_iter().sorted().collect::<Vec<_>>()
		} else {
			vec![]
		};

		let actual_assignments = lit_assignments
			.iter()
			.flat_map(|lit_assignment| model.assign(lit_assignment))
			.collect::<Vec<_>>();

		let check = model.check_assignments(&actual_assignments, expected_assignments);
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
		)
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
			);
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
			);
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
		);
	}

	#[test]
	fn test_lp_multiple_constraints() {
		test_lp_for_configs(
			r"
Subject To
c0: + 2 x1 + 3 x2 + 5 x3 <= 6
c1: + 2 x1 + 3 x2 + 5 x4 <= 5
Binary
x1
x2
x3
x4
End
",
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
		let lp = r"
	Subject To
	c0: 7 x_1 = 0
	Bounds
	0 <= x_1 <= 3
	End
	";
		test_lp_for_configs(lp);
	}

	#[test]
	fn test_scm_3_11() {
		let lp = r"
	Subject To
	c0: 11 x_1 = 0
	Bounds
	0 <= x_1 <= 15
	End
	";
		test_lp_for_configs(lp);
	}

	#[test]
	fn test_scm_3_43() {
		let lp = r"
	Subject To
	c0: 43 x_1 = 0
	Bounds
	0 <= x_1 <= 15
	End
	";
		test_lp_for_configs(lp);
	}

	#[test]
	fn test_scm_2_117() {
		let lp = r"
	Subject To
	c0: 117 x_1 = 0
	Bounds
	0 <= x_1 <= 3
	End
	";
		test_lp_for_configs(lp);
	}

	#[test]
	fn test_scm_4_9() {
		let lp = r"
Subject To
  c0: 9 x_1 = 0
Bounds
  0 <= x_1 <= 7
End
";
		test_lp_for_configs(lp);
		// test_lp(lp, ModelConfig { scm_add: true });
	}

	#[test]
	fn test_scm_4_43() {
		let lp = r"
Subject To
  c0: 43 x_1 = 0
Bounds
  0 <= x_1 <= 7
End
";
		test_lp_for_configs(lp);
	}

	#[test]
	fn test_incon() {
		// 59 * x_1=0 (=0) + 46 * x_2=7 (=322) + 132 * x_3=4 (=528) + 50 * x_4=4 (=200) + 7 * x_5=0 (=0) == 1050 !≤ 931
		let lp = r"
Subject To
  c0: 6 x_1 <= 11
Bounds
  0 <= x_1 <= 3
End
";
		test_lp_for_configs(lp);
	}

	#[test]
	fn test_lp_tmp() {
		// 59 * x_1=0 (=0) + 46 * x_2=7 (=322) + 132 * x_3=4 (=528) + 50 * x_4=4 (=200) + 7 * x_5=0 (=0) == 1050 !≤ 931
		let lp = r"
Subject To
  c0: 2 x_1 <= 200
Bounds
  0 <= x_1 <= 7
End
";
		test_lp_for_configs(lp);
	}

	#[test]
	fn test_lp_scm_recipe() {
		// || thread 'main' panicked at 'ys[1] does not exist in {0: [Lit(1), Lit(2), Lit(3), Lit(4), Lit(5), Const(false)]} when encoding SCM 731*x of 5 lits', /home/hbie0002/Projects/pbc/bin/pindakaas/crates/pindakaas/src/int/model.rs:615:41
		let lp = r"
Subject To
  c0: 731 x_1 = 0
Bounds
  0 <= x_1 <= 31
End
";
		test_lp_for_configs(lp);
	}
}
