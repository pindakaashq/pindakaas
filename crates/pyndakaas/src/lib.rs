//! This crate implements the the internal `pindakaas.pindakaas` Python module,
//! which provides bindings for the `pindakaas` Rust crate.

#![expect(
	clippy::upper_case_acronyms,
	reason = "Python naming for exposed types"
)]

use std::sync::PoisonError;

use pyo3::{create_exception, exceptions::PyException, prelude::*};

create_exception!(pindakaas, InvalidEncoder, PyException, "Raised when the chosen encoder does not support the constraint (e.g. when the `PairwiseEncoder` encoder for AMO constraints is used to encode a PB constraint).");
create_exception!(
	pindakaas,
	Unsatisfiable,
	PyException,
	"Raised when the given constraint is found to be Unsatisfiable during encoding."
);

// Use Result i/o PyResult to use `?` to easily return Rust errors as Python
// exceptions
type Result<R = (), E = ErrWrapper> = std::result::Result<R, E>;

// Avoid orphan rule preventing impl PyErr on pindakaas::Unsatisfiable
struct ErrWrapper(PyErr);

// Allow `pindakaas::Unsatisfiable` to become a wrapped Unsatisfiable exception
impl<T> From<PoisonError<T>> for ErrWrapper {
	fn from(e: PoisonError<T>) -> Self {
		Self(PyException::new_err(e.to_string()))
	}
}

// Allow other `PyErr`s to become a wrapped exception
impl From<PyErr> for ErrWrapper {
	fn from(err: PyErr) -> Self {
		ErrWrapper(err)
	}
}

// Allow `pindakaas::Unsatisfiable` to become a wrapped Unsatisfiable exception
impl From<::pindakaas::Unsatisfiable> for ErrWrapper {
	fn from(_: ::pindakaas::Unsatisfiable) -> Self {
		Self(Unsatisfiable::new_err(
			"The given constraint was found to be Unsatisfiable during encoding",
		))
	}
}

// Allow ErrWrapper to become PyErr
impl From<ErrWrapper> for PyErr {
	fn from(err: ErrWrapper) -> Self {
		err.0
	}
}

#[pymodule]
mod pindakaas {
	use std::{
		fmt::{self, Display},
		num::NonZeroI32,
	};

	use pindakaas::{
		bool_linear::{
			AdderEncoder, BoolLinAggregator, BoolLinExp as BaseBoolLinExp, BoolLinVariant,
			BoolLinear as BaseBoolLinCon, Comparator, SwcEncoder, TotalizerEncoder,
		},
		cardinality::SortingNetworkEncoder,
		cardinality_one::{BitwiseEncoder, LadderEncoder, PairwiseEncoder},
		propositional_logic::{Formula as BaseFormula, TseitinEncoder},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder as _, Lit as BaseLit,
		VarRange as BaseVarRange, Wcnf,
	};
	use pyo3::{exceptions::PyValueError, prelude::*, types::PyIterator};

	#[pymodule_export]
	use crate::InvalidEncoder;
	use crate::Result;
	#[pymodule_export]
	use crate::Unsatisfiable;

	#[derive(FromPyObject)]
	/// Argument capture for types that can become :class:`BoolLinExp`.
	enum BoolLinArg {
		Bool(bool),
		BoolLin(BoolLinExp),
		Int(i64),
		Lit(Lit),
	}

	#[pyclass]
	#[derive(Clone, Debug)]
	/// A Boolean linear constraint, also known as a pseudo-Boolean constraint.
	struct BoolLinCon(BaseBoolLinCon);

	#[pyclass]
	#[derive(Clone, Debug)]
	/// A Boolean linear expression, also known as a pseudo-Boolean expression.
	///
	/// Using operators `<`, `<=`, `==`, `>=`, and `>` with a `int` right hand
	/// side, the expression can be turned into a :class:`BoolLinCon`.
	struct BoolLinExp(BaseBoolLinExp);

	#[pyclass]
	#[derive(Clone, Debug, Default)]
	/// The internal representation of a CNF formula.
	struct CNFInner(Cnf);

	#[derive(FromPyObject)]
	/// Argument capture for types that represent constraint that can be encoded
	/// into a CNF formula.
	enum ConstraintArg {
		/// A Boolean linear constraint
		BoolLin(BoolLinCon),
		/// A propositional formula to be enforced.
		Formula(Formula),
	}

	#[expect(non_camel_case_types, reason = "match python naming convention")]
	#[pyclass(eq, eq_int)]
	#[derive(Clone, Copy, Debug, PartialEq)]
	/// Method used to encode a constraint.
	///
	/// Warning: Not all encoders can be used to encode each type of constraint.
	/// If an invalid encoder is selected, then an :class:`InvalidEncoder`
	/// exception will be raised.
	enum Encoder {
		// TODO These doc-strings do not show up, upstream issue: https://github.com/PyO3/pyo3/issues/5197
		/// Use :class:`pindakaas::bool_linear::AdderEncoder`, which is able to
		/// encode all Boolean linear constraints.
		ADDER,
		/// Use :class:`pindakaas::cardinality_one::BitwiseEncoder`, which is
		/// able to encode all Boolean cardinality one constraints.
		BITWISE,
		/// Use :class:`pindakaas::bool_linear::BddEncoder`, which is able to
		/// encode all Boolean linear constraints.
		DECISION_DIAGRAM,
		/// Use :class:`pindakaas::cardinality_one::LadderEncoder`, which is
		/// able to encode all Boolean cardinality one constraints.
		LADDER,
		/// Use :class:`pindakaas::cardinality_one::PairwiseEncoder`, which is
		/// able to encode all Boolean cardinality one constraints.
		PAIRWISE,
		/// Use :class:`pindakaas::bool_linear::SwcEncoder`, which is able to
		/// encode all Boolean linear constraints.
		SORTED_WEIGHT_COUNTER,
		/// Use :class:`pindakaas::cardinality::SwcEncoder`, which is able to
		/// encode all Boolean cardinality constraints.
		SORTING_NETWORK,
		/// Use :class:`pindakaas::bool_linear::TotalizerEncoder`, which is able
		/// to encode all Boolean linear constraints.
		TOTALIZER,
		/// Use :class:`pindakaas::propositional_logic::TseitinEncoder`, which
		/// is able to encode propositional logic formulas.
		TSEITIN,
	}

	#[pyclass]
	#[derive(Clone, Debug)]
	/// A propositional logic formula.
	struct Formula(BaseFormula<BoolVal>);

	#[derive(FromPyObject)]
	/// Argument capture for types that can become :class:`Formula`.
	enum FormulaArg {
		Const(bool),
		Formula(Formula),
		Lit(Lit),
	}

	#[pyclass]
	#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
	/// A Boolean literal, representing a Boolean variable or its negation.
	struct Lit(BaseLit);

	#[pyclass]
	#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
	/// Representation of a continuous range of variables.
	struct VarRange(BaseVarRange);

	#[pyclass]
	#[derive(Clone, Debug, Default)]
	/// The internal representation of a CNF formula where clauses have optional
	/// associated weights.
	struct WCNFInner(Wcnf);

	/// Same `encode_constraint`, but evaluates the conditions if not empty.
	/// This prevents costly virtual method access if this were done inside
	/// `encode_constraint`
	fn encode_constraint_with_conditions<Db>(
		db: &mut Db,
		con: ConstraintArg,
		enc: Option<Encoder>,
		conditions: Vec<Lit>,
	) -> Result
	where
		Db: ClauseDatabase,
	{
		if conditions.is_empty() {
			encode_constraint(db, con, enc)
		} else {
			encode_constraint(
				&mut db.with_conditions(conditions.into_iter().map(|l| l.0).collect()),
				con,
				enc,
			)
		}
	}

	/// Internal function to help with the encoding of a constraint given an
	/// optional encoder.
	fn encode_constraint<Db>(db: &mut Db, con: ConstraintArg, enc: Option<Encoder>) -> Result
	where
		Db: ClauseDatabase,
	{
		let invalid_enc = |con_ty, enc| {
			Err(InvalidEncoder::new_err(format!(
				"Unable to encode object of type `{con_ty}' using {enc:?}"
			))
			.into())
		};

		match con {
			ConstraintArg::BoolLin(lin) => {
				let aggregated = BoolLinAggregator::default().aggregate(db, &lin.0)?;
				match aggregated {
					BoolLinVariant::Cardinality(c) => match enc.unwrap_or(Encoder::SORTING_NETWORK)
					{
						Encoder::SORTING_NETWORK => SortingNetworkEncoder::default().encode(db, &c),
						Encoder::ADDER => AdderEncoder::default().encode(db, &c),
						Encoder::SORTED_WEIGHT_COUNTER => SwcEncoder::default().encode(db, &c),
						Encoder::TOTALIZER => TotalizerEncoder::default().encode(db, &c),
						_ => return invalid_enc("Cardinality", enc.unwrap()),
					},
					BoolLinVariant::CardinalityOne(c) => match enc.unwrap_or(Encoder::BITWISE) {
						Encoder::BITWISE => BitwiseEncoder::default().encode(db, &c),
						Encoder::ADDER => AdderEncoder::default().encode(db, &c),
						Encoder::LADDER => LadderEncoder::default().encode(db, &c),
						Encoder::PAIRWISE => PairwiseEncoder::default().encode(db, &c),
						Encoder::SORTED_WEIGHT_COUNTER => SwcEncoder::default().encode(db, &c),
						Encoder::SORTING_NETWORK => SortingNetworkEncoder::default().encode(db, &c),
						Encoder::TOTALIZER => TotalizerEncoder::default().encode(db, &c),
						_ => return invalid_enc("CardinalityOne", enc.unwrap()),
					},
					BoolLinVariant::Linear(lin) => match enc.unwrap_or(Encoder::TOTALIZER) {
						Encoder::TOTALIZER => TotalizerEncoder::default().encode(db, &lin),
						Encoder::ADDER => AdderEncoder::default().encode(db, &lin),
						Encoder::SORTED_WEIGHT_COUNTER => SwcEncoder::default().encode(db, &lin),
						_ => return invalid_enc("BoolLinear", enc.unwrap()),
					},
					BoolLinVariant::Trivial => return Ok(()),
				}?;
			}
			ConstraintArg::Formula(f) => match enc.unwrap_or(Encoder::TSEITIN) {
				Encoder::TSEITIN => TseitinEncoder.encode(db, &f.0)?,
				_ => {
					return invalid_enc("Formula", enc.unwrap());
				}
			},
		};
		Ok(())
	}

	#[pyfunction]
	fn _wrap_encode_constraint(
		obj: &Bound<'_, PyAny>,
		con: ConstraintArg,
		enc: Option<Encoder>,
		conditions: Vec<Lit>,
	) -> Result {
		struct PyDbWrapper<'a>(&'a Bound<'a, PyAny>);
		impl ClauseDatabase for PyDbWrapper<'_> {
			fn add_clause_from_slice(
				&mut self,
				clause: &[BaseLit],
			) -> Result<(), pindakaas::Unsatisfiable> {
				let clause = clause.iter().map(|&l| Lit(l)).collect_vec();
				let res = self.0.call_method1("add_clause", (clause,));
				match res {
					Err(e) if e.is_instance_of::<Unsatisfiable>(self.0.py()) => {
						Err(pindakaas::Unsatisfiable)
					}
					Err(e) => {
						panic!("unexpected error in add_clause implementation: {}", e)
					}
					Ok(_) => Ok(()),
				}
			}

			fn new_var_range(&mut self, len: usize) -> BaseVarRange {
				let tup = self
					.0
					.call_method1("new_var_range", (len,))
					.expect("unexpected error in new_var_range implementation");
				let (start, end): (Lit, Lit) = tup
					.extract()
					.expect("new_var_range did not return a tuple of two literals");
				BaseVarRange::new(start.0.var(), end.0.var())
			}
		}

		encode_constraint_with_conditions(&mut PyDbWrapper(obj), con, enc, conditions)
	}

	impl BoolLinArg {
		fn as_bool_lin_exp(&self) -> BoolLinExp {
			match self {
				&BoolLinArg::Bool(b) => BoolLinExp(b.into()),
				BoolLinArg::BoolLin(exp) => exp.clone(),
				&BoolLinArg::Int(i) => BoolLinExp(i.into()),
				&BoolLinArg::Lit(l) => BoolLinExp(l.0.into()),
			}
		}
	}

	#[pymethods]
	impl BoolLinCon {
		fn __str__(&self) -> String {
			self.0.to_string()
		}
	}

	#[pymethods]
	impl BoolLinExp {
		fn __add__(&self, other: BoolLinArg) -> Self {
			let mut res = self.clone();
			res.__iadd__(other);
			res
		}

		fn __radd__(&self, other: BoolLinArg) -> Self {
			self.__add__(other)
		}

		fn __eq__(&self, other: i64) -> BoolLinCon {
			BoolLinCon(BaseBoolLinCon::new(
				self.0.clone(),
				Comparator::Equal,
				other,
			))
		}

		fn __ge__(&self, other: i64) -> BoolLinCon {
			BoolLinCon(BaseBoolLinCon::new(
				self.0.clone(),
				Comparator::GreaterEq,
				other,
			))
		}

		fn __gt__(&self, other: i64) -> BoolLinCon {
			self.__ge__(other + 1)
		}

		fn __iadd__(&mut self, other: BoolLinArg) {
			self.0 += other.as_bool_lin_exp().0;
		}

		fn __imul__(&mut self, other: i64) {
			self.0 *= other;
		}

		fn __isub__(&mut self, other: BoolLinArg) {
			self.0 -= other.as_bool_lin_exp().0;
		}

		fn __le__(&self, other: i64) -> BoolLinCon {
			BoolLinCon(BaseBoolLinCon::new(
				self.0.clone(),
				Comparator::LessEq,
				other,
			))
		}

		fn __lt__(&self, other: i64) -> BoolLinCon {
			self.__le__(other - 1)
		}

		fn __mul__(&self, other: i64) -> Self {
			let mut res = self.clone();
			res.__imul__(other);
			res
		}

		fn __rmul__(&self, other: i64) -> Self {
			self.__mul__(other)
		}

		fn __neg__(&self) -> Self {
			Self(-self.0.clone())
		}

		fn __str__(&self) -> String {
			self.0.to_string()
		}

		fn __sub__(&self, other: BoolLinArg) -> Self {
			let mut res = self.clone();
			res.__isub__(other);
			res
		}
	}

	use itertools::Itertools;

	#[pymethods]
	impl CNFInner {
		fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> Result {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
				.try_collect()?;
			self.0.add_clause(clause.into_iter().map(|lit| lit.0))?;
			Ok(())
		}

		fn add_encoding(
			&mut self,
			con: ConstraintArg,
			enc: Option<Encoder>,
			conditions: Vec<Lit>,
		) -> Result {
			encode_constraint_with_conditions(&mut self.0, con, enc, conditions)
		}

		fn clauses(&self) -> Vec<Vec<Lit>> {
			// TODO: It would be great if this could be converted to be lazy, but it
			// seems a little tricky. This should probably be okay for now.
			self.0
				.iter()
				.map(|c| c.iter().map(|&lit| Lit(lit)).collect())
				.collect()
		}

		#[new]
		fn new() -> Self {
			Self(Default::default())
		}

		fn new_var_range(&mut self, num_vars: usize) -> VarRange {
			let range = self.0.new_var_range(num_vars);
			VarRange(range)
		}

		fn to_dimacs(&self) -> String {
			self.0.to_string()
		}

		fn variables(&self) -> VarRange {
			VarRange(self.0.variables())
		}
	}

	#[pymethods]
	impl Formula {
		fn __and__(&self, other: FormulaArg) -> Self {
			Self(self.0.clone() & other.as_formula())
		}

		fn __rand__(&self, other: FormulaArg) -> Self {
			self.__and__(other)
		}

		fn __eq__(&self, other: FormulaArg) -> Self {
			use BaseFormula::*;

			Formula(Equiv(vec![self.0.clone(), other.as_formula()]))
		}

		fn __ge__(&self, other: FormulaArg) -> Self {
			use BaseFormula::*;

			Self(Implies(other.as_formula().into(), self.0.clone().into()))
		}

		fn __gt__(&self, other: FormulaArg) -> Self {
			Self(self.0.clone() & !other.as_formula())
		}

		fn __le__(&self, other: FormulaArg) -> Self {
			use BaseFormula::*;

			Self(Implies(self.0.clone().into(), other.as_formula().into()))
		}

		fn __lt__(&self, other: FormulaArg) -> Self {
			Self(!self.0.clone() & other.as_formula())
		}

		fn __invert__(&self) -> Self {
			Self(!self.0.clone())
		}

		fn __ne__(&self, other: FormulaArg) -> Self {
			self.__xor__(other)
		}

		fn __or__(&self, other: FormulaArg) -> Self {
			Formula(self.0.clone() | other.as_formula())
		}

		fn __ror__(&self, other: FormulaArg) -> Self {
			self.__or__(other)
		}

		fn __str__(&self) -> String {
			self.0.to_string()
		}

		fn __xor__(&self, other: FormulaArg) -> Self {
			Formula(self.0.clone() ^ other.as_formula())
		}

		fn __rxor__(&self, other: FormulaArg) -> Self {
			self.__xor__(other)
		}
	}

	impl FormulaArg {
		/// Internal method used to convert the :class:`FormulaArg` into a
		/// :class:`BaseFormula<BoolVal>`.
		fn as_formula(&self) -> BaseFormula<BoolVal> {
			use BaseFormula::*;

			match self {
				FormulaArg::Const(b) => Atom(BoolVal::Const(*b)),
				FormulaArg::Formula(formula) => formula.0.clone(),
				FormulaArg::Lit(lit) => lit.as_formula(),
			}
		}
	}

	impl Lit {
		fn as_bool_lin_exp(&self) -> BoolLinExp {
			BoolLinExp(self.0.into())
		}

		fn as_formula(&self) -> BaseFormula<BoolVal> {
			BaseFormula::Atom(self.0.into())
		}
	}

	#[pymethods]
	impl Lit {
		fn __add__(&self, other: BoolLinArg) -> BoolLinExp {
			self.as_bool_lin_exp().__add__(other)
		}

		fn __radd__(&self, other: BoolLinArg) -> BoolLinExp {
			self.__add__(other)
		}

		fn __and__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__and__(other)
		}

		fn __rand__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__and__(other)
		}

		fn __eq__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__eq__(other)
		}

		fn __ge__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__ge__(other)
		}

		fn __gt__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__gt__(other)
		}

		fn __le__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__le__(other)
		}

		fn __lt__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__lt__(other)
		}

		fn __int__(&self) -> i32 {
			self.0.into()
		}

		fn __invert__(&self) -> Self {
			Self(!self.0)
		}

		fn __mul__(&self, other: i64) -> BoolLinExp {
			self.as_bool_lin_exp().__mul__(other)
		}

		fn __rmul__(&self, other: i64) -> BoolLinExp {
			self.__mul__(other)
		}

		fn __ne__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__ne__(other)
		}

		fn __or__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__or__(other)
		}

		fn __ror__(&self, other: FormulaArg) -> Formula {
			self.__or__(other)
		}

		fn __str__(&self) -> String {
			self.0.to_string()
		}

		fn __sub__(&self, other: BoolLinArg) -> BoolLinExp {
			self.as_bool_lin_exp().__sub__(other)
		}

		fn __xor__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__xor__(other)
		}

		fn __rxor__(&self, other: FormulaArg) -> Formula {
			self.__xor__(other)
		}

		#[staticmethod]
		fn from_raw(value: NonZeroI32) -> Self {
			Self(BaseLit::from_raw(value))
		}

		/// Return whether the variable is negated
		fn is_negated(&self) -> bool {
			self.0.is_negated()
		}

		/// Return the literal's variable
		fn var(&self) -> Self {
			Self(self.0.var().into())
		}
	}

	impl Display for Lit {
		fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
			self.0.fmt(f)
		}
	}

	#[pymethods]
	impl VarRange {
		fn __iter__(slf: PyRef<'_, Self>) -> PyRef<'_, Self> {
			slf
		}

		fn __next__(mut slf: PyRefMut<'_, Self>) -> Option<Lit> {
			slf.0.next().map(|lit| Lit(lit.into()))
		}

		/// Returns the final variable included in the range.
		fn end(&self) -> Lit {
			Lit(self.0.end().into())
		}

		#[new]
		/// Create a new variable range that includes all variables between
		/// `start` and `end` (inclusive).
		fn new(start: Lit, end: Lit) -> PyResult<Self> {
			if start.is_negated() || end.is_negated() {
				return Err(PyValueError::new_err(
					"`start' and `end' must be positive literals (directly representing variables)",
				));
			}
			Ok(Self(BaseVarRange::new(start.0.var(), end.0.var())))
		}

		/// Returns the first variable included in the range.
		fn start(&self) -> Lit {
			Lit(self.0.start().into())
		}
	}

	#[pymethods]
	impl WCNFInner {
		fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> Result {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
				.try_collect()?;
			self.0.add_clause(clause.into_iter().map(|lit| lit.0))?;
			Ok(())
		}

		fn add_encoding(
			&mut self,
			con: ConstraintArg,
			enc: Option<Encoder>,
			conditions: Vec<Lit>,
		) -> Result {
			encode_constraint_with_conditions(&mut self.0, con, enc, conditions)
		}

		fn add_weighted_clause(&mut self, clause: Bound<'_, PyIterator>, weight: i64) -> Result {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
				.try_collect()?;
			self.0
				.add_weighted_clause(clause.into_iter().map(|lit| lit.0), weight)?;
			Ok(())
		}

		fn clauses(&self) -> Vec<Vec<Lit>> {
			// TODO: It would be great if this could be converted to be lazy, but it
			// seems a little tricky. This should probably be okay for now.
			self.0
				.iter()
				.filter(|(_, w)| w.is_none())
				.map(|(c, _)| c.iter().map(|&lit| Lit(lit)).collect_vec())
				.collect()
		}

		#[new]
		fn new() -> Self {
			Self(Default::default())
		}

		fn new_var_range(&mut self, num_vars: usize) -> VarRange {
			let range = self.0.new_var_range(num_vars);
			VarRange(range)
		}

		fn to_dimacs(&self) -> String {
			self.0.to_string()
		}

		fn variables(&self) -> VarRange {
			VarRange(self.0.variables())
		}

		fn weighted_clauses(&self) -> Vec<(Option<i64>, Vec<Lit>)> {
			// TODO: It would be great if this could be converted to be lazy, but it
			// seems a little tricky. This should probably be okay for now.
			self.0
				.iter()
				.map(|(c, &w)| (w, (c.iter().map(|&lit| Lit(lit)).collect())))
				.collect()
		}
	}

	#[pymodule]
	mod solver {
		use std::{
			collections::HashMap,
			sync::Mutex,
			time::{Duration, SystemTime},
		};

		use itertools::Itertools;
		use pindakaas::{
			solver::{
				cadical::Cadical, kissat::Kissat, Assumptions, FailedAssumptions, SolveResult,
				Solver, TermSignal, TerminateCallback,
			},
			ClauseDatabase, ClauseDatabaseTools, Valuation,
		};
		use pyo3::{exceptions::PyNotImplementedError, prelude::*, types::PyIterator};

		use super::{encode_constraint_with_conditions, Result};
		use crate::pindakaas::{ConstraintArg, Encoder, Lit};

		#[pyclass(unsendable)]
		#[derive(Debug, Default)]
		/// The internal representation of a instance of the CaDiCaL solver.
		struct CaDiCaLInner(Cadical);

		#[pyclass]
		#[derive(Debug, Default)]
		struct KissatInner(Mutex<Kissat>);

		#[pyclass(eq, eq_int)]
		#[derive(Clone, Copy, Debug, PartialEq)]
		/// The resulting status of solving a problem.
		enum Status {
			/// A solution was found.
			SATISFIED,
			/// No solution exists for the given problem.
			UNSATISFIABLE,
			/// The solving process was interrupted before a result was found.
			UNKNOWN,
		}

		fn dur_term_fn(dur: Duration) -> impl Fn() -> TermSignal + 'static {
			let deadline = SystemTime::now() + dur;
			move || {
				if SystemTime::now() > deadline {
					TermSignal::Terminate
				} else {
					TermSignal::Continue
				}
			}
		}

		/// Hack: workaround for https://github.com/PyO3/pyo3/issues/759
		#[pymodule_init]
		fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
			Python::attach(|py| {
				py.import("sys")?
					.getattr("modules")?
					.set_item("pindakaas.pindakaas.solver", m)
			})
		}

		#[pymethods]
		impl CaDiCaLInner {
			fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> Result {
				let clause: Vec<Lit> = clause
					.into_iter()
					.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
					.try_collect()?;
				self.0.add_clause(clause.into_iter().map(|lit| lit.0))?;
				Ok(())
			}

			fn add_encoding(
				&mut self,
				con: ConstraintArg,
				enc: Option<Encoder>,
				conditions: Vec<Lit>,
			) -> Result {
				encode_constraint_with_conditions(&mut self.0, con, enc, conditions)
			}

			#[new]
			fn new() -> Self {
				Self(Default::default())
			}

			fn new_var_range(&mut self, num_vars: usize) -> Result<(Lit, Lit)> {
				let range = self.0.new_var_range(num_vars);
				Ok((Lit(range.start().into()), Lit(range.end().into())))
			}

			fn set_time_limit(&mut self, limit: Option<Duration>) -> Result {
				self.0.set_terminate_callback(limit.map(dur_term_fn));
				Ok(())
			}

			fn solve_assuming(
				&mut self,
				assumptions: Vec<Lit>,
			) -> Result<(Status, HashMap<i32, bool>)> {
				let vars = self.0.emitted_vars();
				let result = self.0.solve_assuming(assumptions.iter().map(|&lit| lit.0));
				Ok(match result {
					SolveResult::Satisfied(sol) => (
						Status::SATISFIED,
						vars.into_iter()
							.map(|var| (var.into(), sol.value(var.into())))
							.collect(),
					),
					SolveResult::Unsatisfiable(fail) => (
						Status::UNSATISFIABLE,
						assumptions
							.iter()
							.map(|&lit| (lit.0.into(), fail.fail(lit.0)))
							.collect(),
					),
					SolveResult::Unknown => (Status::UNKNOWN, HashMap::new()),
				})
			}
		}

		#[pymethods]
		impl KissatInner {
			fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> PyResult<()> {
				let clause: Vec<Lit> = clause
					.into_iter()
					.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
					.collect::<PyResult<_>>()?;
				let mut guard = self.0.lock().unwrap();
				guard
					.add_clause(clause.into_iter().map(|lit| lit.0))
					.unwrap();
				Ok(())
			}

			fn add_encoding(
				&mut self,
				con: ConstraintArg,
				enc: Option<Encoder>,
				conditions: Vec<Lit>,
			) -> Result {
				let mut guard = self.0.lock().unwrap();
				encode_constraint_with_conditions(&mut *guard, con, enc, conditions)
			}

			#[new]
			fn new() -> Self {
				Self(Default::default())
			}

			fn new_var_range(&mut self, num_vars: usize) -> Result<(Lit, Lit)> {
				let mut guard = self.0.lock().unwrap();
				let range = guard.new_var_range(num_vars);
				Ok((Lit(range.start().into()), Lit(range.end().into())))
			}

			fn set_time_limit(&mut self, limit: Option<Duration>) {
				let mut guard = self.0.lock().unwrap();
				guard.set_terminate_callback(limit.map(dur_term_fn));
			}

			fn solve_assuming(
				&self,
				assumptions: Vec<Lit>,
			) -> PyResult<(Status, HashMap<i32, bool>)> {
				if !assumptions.is_empty() {
					return Err(PyNotImplementedError::new_err(
						"Kissat does not support assumptions",
					));
				}
				let mut guard = self.0.lock().unwrap();
				let vars = guard.emitted_vars();
				Ok(match guard.solve() {
					SolveResult::Satisfied(sol) => (
						Status::SATISFIED,
						vars.into_iter()
							.map(|var| (var.into(), sol.value(var.into())))
							.collect(),
					),
					SolveResult::Unsatisfiable(_) => (Status::UNSATISFIABLE, Default::default()),
					SolveResult::Unknown => (Status::UNKNOWN, HashMap::new()),
				})
			}
		}
	}
}
