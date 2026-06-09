//! This crate implements the the internal `pindakaas.pindakaas` Python module,
//! which provides bindings for the `pindakaas` Rust crate.
#![expect(
	clippy::upper_case_acronyms,
	reason = "Python naming for exposed types"
)]

use std::sync::PoisonError;

use pyo3::{create_exception, exceptions::PyException, prelude::*};

// Avoid orphan rule preventing impl PyErr on pindakaas::Unsatisfiable
struct ErrWrapper(PyErr);

// Use Result i/o PyResult to use `?` to easily return Rust errors as Python
// exceptions
type Result<R = (), E = ErrWrapper> = std::result::Result<R, E>;

// Allow `pindakaas::Unsatisfiable` to become a wrapped Unsatisfiable exception
impl From<::pindakaas::Unsatisfiable> for ErrWrapper {
	fn from(_: ::pindakaas::Unsatisfiable) -> Self {
		Self(Unsatisfiable::new_err(
			"The given constraint was found to be Unsatisfiable during encoding",
		))
	}
}

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

// Allow ErrWrapper to become PyErr
impl From<ErrWrapper> for PyErr {
	fn from(err: ErrWrapper) -> Self {
		err.0
	}
}

create_exception! {
	pindakaas,
	InvalidEncoder,
	PyException,
	"Raised when the chosen encoder does not support the constraint (e.g. when the `PairwiseEncoder` encoder for AMO constraints is used to encode a PB constraint)."
}
create_exception! {
	pindakaas,
	Unsatisfiable,
	PyException,
	"Raised when the given constraint is found to be Unsatisfiable during encoding."
}

#[pymodule]
mod pindakaas {
	use std::{
		fmt::{self, Display},
		num::NonZeroI32,
		sync::Mutex,
	};

	use itertools::Itertools;
	use pindakaas::{
		bool_linear::{
			AdderEncoder, BoolLinAggregator, BoolLinExp as BaseBoolLinExp, BoolLinVariant,
			BoolLinear as BaseBoolLinCon, Comparator, LinearEncoder, NormalizedBoolLinear,
			SwcEncoder, TotalizerEncoder,
		},
		cardinality::{Cardinality, SortingNetworkEncoder},
		cardinality_one::{BitwiseEncoder, CardinalityOne, LadderEncoder, PairwiseEncoder},
		propositional_logic::{Formula as BaseFormula, TseitinEncoder},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder as EncoderTrait, Lit as BaseLit,
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

	#[pyclass(from_py_object)]
	#[derive(Clone, Debug)]
	/// A Boolean linear constraint, also known as a pseudo-Boolean constraint.
	struct BoolLinCon(BaseBoolLinCon);

	#[pyclass(from_py_object)]
	#[derive(Clone, Debug)]
	/// A Boolean linear expression, also known as a pseudo-Boolean expression.
	///
	/// Using operators `<`, `<=`, `==`, `>=`, and `>` with a `int` right hand
	/// side, the expression can be turned into a :class:`BoolLinCon`.
	struct BoolLinExp(BaseBoolLinExp);

	#[pyclass(skip_from_py_object)]
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
	#[pyclass(eq, eq_int, from_py_object)]
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

	#[pyclass(from_py_object)]
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

	struct LinEncoderWrapper {
		/// Method chosen by the user.
		method: Option<Encoder>,
		/// Error message for an invalid choice.
		error_message: Mutex<Option<PyErr>>,
	}

	#[pyclass(from_py_object)]
	#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
	/// A Boolean literal, representing a Boolean variable or its negation.
	struct Lit(BaseLit);

	#[pyclass(skip_from_py_object)]
	#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
	/// Representation of a continuous range of variables.
	struct VarRange(BaseVarRange);

	#[pyclass(skip_from_py_object)]
	#[derive(Clone, Debug, Default)]
	/// The internal representation of a CNF formula where clauses have optional
	/// associated weights.
	struct WCNFInner(Wcnf);

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
				let clause_vec = clause.iter().map(|&l| Lit(l)).collect_vec();
				let res = self.0.call_method1("add_clause", (clause_vec,));
				match res {
					Err(e) if e.is_instance_of::<Unsatisfiable>(self.0.py()) => {
						Err(pindakaas::Unsatisfiable)
					}
					Err(e) => {
						panic!("unexpected error in add_clause implementation: {}", e)
					}
					// We would have expected the user implementation to raise `Unsatisfiable`, but
					// is did not. Since encodings depend on this behaviour, we return the error
					// instead.
					Ok(_) if clause.is_empty() => Err(pindakaas::Unsatisfiable),
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

		encode_constraint(&mut PyDbWrapper(obj), con, enc, conditions)
	}

	/// Internal function to help with the encoding of a constraint given an
	/// optional encoder.
	///
	/// If conditions are provided, the constraint is encoded to only hold if
	/// all conditions are true.
	fn encode_constraint<Db>(
		db: &mut Db,
		con: ConstraintArg,
		enc: Option<Encoder>,
		conditions: Vec<Lit>,
	) -> Result
	where
		Db: ClauseDatabase + ?Sized,
	{
		let invalid_enc = |con_ty, enc| {
			Err(InvalidEncoder::new_err(format!(
				"Unable to encode object of type `{con_ty}' using {enc:?}"
			))
			.into())
		};
		let conditions: Vec<_> = conditions.into_iter().map(|l| l.0).collect();

		match con {
			ConstraintArg::BoolLin(lin) => {
				let encoder = LinEncoderWrapper::new(enc);
				let encoder = LinearEncoder::new(encoder, BoolLinAggregator::default());
				encoder.encode_implied(db, &conditions, &lin.0)?;
				let err = encoder
					.variant_encoder()
					.error_message
					.lock()
					.unwrap()
					.take();
				if let Some(err) = err {
					return Err(err.into());
				}
			}
			ConstraintArg::Formula(f) => match enc.unwrap_or(Encoder::TSEITIN) {
				Encoder::TSEITIN => TseitinEncoder.encode_implied(db, &conditions, &f.0)?,
				_ => {
					return invalid_enc("Formula", enc.unwrap());
				}
			},
		};
		Ok(())
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

		fn __neg__(&self) -> Self {
			Self(-self.0.clone())
		}

		fn __radd__(&self, other: BoolLinArg) -> Self {
			self.__add__(other)
		}

		fn __rmul__(&self, other: i64) -> Self {
			self.__mul__(other)
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

	#[pymethods]
	impl CNFInner {
		fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> Result {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>().map_err(PyErr::from)))
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
			encode_constraint(&mut self.0, con, enc, conditions)
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

		fn new_var_range(&mut self, num_vars: usize) -> PyResult<VarRange> {
			let range = self.0.new_var_range(num_vars);
			Ok(VarRange(range))
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

		fn __invert__(&self) -> Self {
			Self(!self.0.clone())
		}

		fn __le__(&self, other: FormulaArg) -> Self {
			use BaseFormula::*;

			Self(Implies(self.0.clone().into(), other.as_formula().into()))
		}

		fn __lt__(&self, other: FormulaArg) -> Self {
			Self(!self.0.clone() & other.as_formula())
		}

		fn __ne__(&self, other: FormulaArg) -> Self {
			self.__xor__(other)
		}

		fn __or__(&self, other: FormulaArg) -> Self {
			Formula(self.0.clone() | other.as_formula())
		}

		fn __rand__(&self, other: FormulaArg) -> Self {
			self.__and__(other)
		}

		fn __ror__(&self, other: FormulaArg) -> Self {
			self.__or__(other)
		}

		fn __rxor__(&self, other: FormulaArg) -> Self {
			self.__xor__(other)
		}

		fn __str__(&self) -> String {
			self.0.to_string()
		}

		fn __xor__(&self, other: FormulaArg) -> Self {
			Formula(self.0.clone() ^ other.as_formula())
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

	impl LinEncoderWrapper {
		fn new(method: Option<Encoder>) -> Self {
			Self {
				method,
				error_message: Mutex::new(None),
			}
		}

		fn set_err(&self, con_ty: &str, enc: Encoder) {
			let _ = self
				.error_message
				.lock()
				.unwrap()
				.replace(InvalidEncoder::new_err(format!(
					"Unable to encode object of type `{con_ty}' using {enc:?}"
				)));
		}
	}

	impl<Db: ClauseDatabase + ?Sized> EncoderTrait<Db, BoolLinVariant> for LinEncoderWrapper {
		fn encode(
			&self,
			db: &mut Db,
			con: &BoolLinVariant,
		) -> Result<(), pindakaas::Unsatisfiable> {
			match con {
				BoolLinVariant::Linear(lin) => self.encode(db, lin),
				BoolLinVariant::Cardinality(card) => self.encode(db, card),
				BoolLinVariant::CardinalityOne(card1) => self.encode(db, card1),
				BoolLinVariant::Trivial => Ok(()),
			}
		}
	}

	impl<Db: ClauseDatabase + ?Sized> EncoderTrait<Db, Cardinality> for LinEncoderWrapper {
		fn encode(&self, db: &mut Db, con: &Cardinality) -> Result<(), pindakaas::Unsatisfiable> {
			match self.method.unwrap_or(Encoder::ADDER) {
				Encoder::SORTING_NETWORK => SortingNetworkEncoder::default().encode(db, con),
				Encoder::ADDER => AdderEncoder::default().encode(db, con),
				Encoder::SORTED_WEIGHT_COUNTER => SwcEncoder::default().encode(db, con),
				Encoder::TOTALIZER => TotalizerEncoder::default().encode(db, con),
				enc => {
					self.set_err("Cardinality", enc);
					Ok(())
				}
			}
		}
	}

	impl<Db: ClauseDatabase + ?Sized> EncoderTrait<Db, CardinalityOne> for LinEncoderWrapper {
		fn encode(
			&self,
			db: &mut Db,
			con: &CardinalityOne,
		) -> Result<(), pindakaas::Unsatisfiable> {
			match self.method.unwrap_or(Encoder::BITWISE) {
				Encoder::BITWISE => BitwiseEncoder::default().encode(db, con),
				Encoder::ADDER => AdderEncoder::default().encode(db, con),
				Encoder::LADDER => LadderEncoder::default().encode(db, con),
				Encoder::PAIRWISE => PairwiseEncoder::default().encode(db, con),
				Encoder::SORTED_WEIGHT_COUNTER => SwcEncoder::default().encode(db, con),
				Encoder::SORTING_NETWORK => SortingNetworkEncoder::default().encode(db, con),
				Encoder::TOTALIZER => TotalizerEncoder::default().encode(db, con),
				enc => {
					self.set_err("CardinalityOne", enc);
					Ok(())
				}
			}
		}
	}

	impl<Db: ClauseDatabase + ?Sized> EncoderTrait<Db, NormalizedBoolLinear> for LinEncoderWrapper {
		fn encode(
			&self,
			db: &mut Db,
			con: &NormalizedBoolLinear,
		) -> Result<(), pindakaas::Unsatisfiable> {
			match self.method.unwrap_or(Encoder::ADDER) {
				Encoder::ADDER => AdderEncoder::default().encode(db, con),
				Encoder::SORTED_WEIGHT_COUNTER => SwcEncoder::default().encode(db, con),
				Encoder::TOTALIZER => TotalizerEncoder::default().encode(db, con),
				enc => {
					self.set_err("BoolLinear", enc);
					Ok(())
				}
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

		fn __and__(&self, other: FormulaArg) -> Formula {
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

		fn __int__(&self) -> i32 {
			self.0.into()
		}

		fn __invert__(&self) -> Self {
			Self(!self.0)
		}

		fn __le__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__le__(other)
		}

		fn __lt__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__lt__(other)
		}

		fn __mul__(&self, other: i64) -> BoolLinExp {
			self.as_bool_lin_exp().__mul__(other)
		}

		fn __ne__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__ne__(other)
		}

		fn __or__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__or__(other)
		}

		fn __radd__(&self, other: BoolLinArg) -> BoolLinExp {
			self.__add__(other)
		}

		fn __rand__(&self, other: FormulaArg) -> Formula {
			Formula(self.as_formula()).__and__(other)
		}

		fn __rmul__(&self, other: i64) -> BoolLinExp {
			self.__mul__(other)
		}

		fn __ror__(&self, other: FormulaArg) -> Formula {
			self.__or__(other)
		}

		fn __rxor__(&self, other: FormulaArg) -> Formula {
			self.__xor__(other)
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

		fn __len__(&self) -> usize {
			self.0.len()
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
				.map(|any| any.and_then(|lit| lit.extract::<Lit>().map_err(PyErr::from)))
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
			encode_constraint(&mut self.0, con, enc, conditions)
		}

		fn add_weighted_clause(&mut self, clause: Bound<'_, PyIterator>, weight: i64) -> Result {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>().map_err(PyErr::from)))
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

		fn new_var_range(&mut self, num_vars: usize) -> PyResult<VarRange> {
			let range = self.0.new_var_range(num_vars);
			Ok(VarRange(range))
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
		macro_rules! py_solver_result {
			($name:ident, $owner:ident, $solver:ty) => {
				#[pymethods]
				impl $name {
					fn __enter__(slf: Py<Self>) -> Py<Self> {
						slf
					}

					fn __exit__(
						&mut self,
						py: Python<'_>,
						_exc_type: Option<&Bound<'_, PyAny>>,
						_exc: Option<&Bound<'_, PyAny>>,
						_traceback: Option<&Bound<'_, PyAny>>,
					) -> PyResult<bool> {
						self.0.exit(py, |owner| &mut owner.0)
					}

					fn failed(&self, lit: Lit) -> PyResult<Option<bool>> {
						self.0.failed(lit)
					}

					#[getter]
					fn status(&self) -> PyResult<Status> {
						self.0.status()
					}

					fn value(&self, lit: Lit) -> PyResult<Option<bool>> {
						self.0.value(lit)
					}
				}
			};
		}

		use std::{
			mem::transmute,
			time::{Duration, SystemTime},
		};

		use itertools::Itertools;
		use pindakaas::{
			solver::{
				cadical::Cadical, kissat::Kissat, Assumptions, FailedAssumptions, SolveResult,
				Solver, TermSignal, TerminateCallback,
			},
			ClauseDatabase, ClauseDatabaseTools, Lit as BaseLit, Valuation,
		};
		use pyo3::{
			exceptions::{PyNotImplementedError, PyRuntimeError},
			prelude::*,
			pyclass::boolean_struct::False,
			types::{PyAny, PyIterator},
			PyClass,
		};

		use crate::{
			pindakaas::{encode_constraint, ConstraintArg, Encoder, Lit, VarRange},
			Result,
		};

		const CHECKED_OUT_ERROR: &str = "solver is currently checked out by an active result";
		const INACTIVE_RESULT_ERROR: &str = "solver result is no longer active";
		const RESTORED_ERROR: &str = "solver was already restored to its owner";

		#[pyclass(unsendable)]
		#[derive(Debug)]
		struct CaDiCaLInner(SolverImpl<Cadical>);

		#[pyclass(unsendable)]
		struct CaDiCaLResult(SolverResultImpl<CaDiCaLInner, Cadical>);

		#[pyclass(unsendable)]
		#[derive(Debug)]
		struct KissatInner(SolverImpl<Kissat>);

		#[pyclass(unsendable)]
		struct KissatResult(SolverResultImpl<KissatInner, Kissat>);

		#[derive(Debug)]
		struct SolverImpl<S> {
			solver: Option<S>,
		}

		struct SolverResultImpl<Owner, S> {
			owner: Py<Owner>,
			result: Option<SolverResultState>,
			solver: Option<S>,
			supports_assumptions: bool,
		}

		enum SolverResultState {
			/// A satisfying valuation for the current solve call.
			Satisfied(Box<dyn Valuation + 'static>),
			/// Failed assumptions for the current solve call.
			Unsatisfiable(Box<dyn Fn(BaseLit) -> Option<bool> + 'static>),
			/// The solver terminated without a definitive result.
			Unknown,
		}

		#[pyclass(eq, eq_int, skip_from_py_object)]
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

		/// Hack: workaround for https://github.com/PyO3/pyo3/issues/759
		#[pymodule_init]
		fn init(module: &Bound<'_, PyModule>) -> PyResult<()> {
			module
				.py()
				.import("sys")?
				.getattr("modules")?
				.set_item("pindakaas.pindakaas.solver", module)
		}

		#[pymethods]
		impl CaDiCaLInner {
			fn _set_option(&mut self, name: &str, value: i32) -> PyResult<()> {
				self.0.solver_mut()?.set_option(name, value);
				Ok(())
			}

			fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> Result {
				self.0.add_clause(clause)
			}

			fn add_encoding(
				&mut self,
				con: ConstraintArg,
				enc: Option<Encoder>,
				conditions: Vec<Lit>,
			) -> Result {
				self.0.add_encoding(con, enc, conditions)
			}

			#[new]
			fn new() -> Self {
				Self(SolverImpl::default())
			}

			fn new_var_range(&mut self, num_vars: usize) -> PyResult<VarRange> {
				self.0.new_var_range(num_vars)
			}

			fn set_time_limit(&mut self, limit: Option<Duration>) -> Result {
				self.0.set_time_limit(limit)
			}

			fn solve_assuming(
				slf: Py<Self>,
				py: Python<'_>,
				assumptions: Vec<Lit>,
			) -> Result<Py<CaDiCaLResult>> {
				let mut inner = slf.bind(py).borrow_mut();
				let solver = inner.0.take()?;
				Ok(Py::new(
					py,
					CaDiCaLResult(SolverResultImpl::from_assumptions_solver(
						slf.clone_ref(py),
						solver,
						&assumptions,
					)),
				)?)
			}
		}

		#[pymethods]
		impl KissatInner {
			fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> Result {
				self.0.add_clause(clause)
			}

			fn add_encoding(
				&mut self,
				con: ConstraintArg,
				enc: Option<Encoder>,
				conditions: Vec<Lit>,
			) -> Result {
				self.0.add_encoding(con, enc, conditions)
			}

			#[new]
			fn new() -> Self {
				Self(SolverImpl::default())
			}

			fn new_var_range(&mut self, num_vars: usize) -> PyResult<VarRange> {
				self.0.new_var_range(num_vars)
			}

			fn set_time_limit(&mut self, limit: Option<Duration>) -> Result {
				self.0.set_time_limit(limit)
			}

			fn solve_assuming(
				slf: Py<Self>,
				py: Python<'_>,
				assumptions: Vec<Lit>,
			) -> Result<Py<KissatResult>> {
				if !assumptions.is_empty() {
					return Err(PyNotImplementedError::new_err(
						"solver does not support assumptions",
					)
					.into());
				}
				let mut inner = slf.bind(py).borrow_mut();
				let solver = inner.0.take()?;
				Ok(Py::new(
					py,
					KissatResult(SolverResultImpl::from_solver(slf.clone_ref(py), solver)),
				)?)
			}
		}

		impl<S> SolverImpl<S> {
			fn solver_mut(&mut self) -> PyResult<&mut S> {
				self.solver
					.as_mut()
					.ok_or_else(|| PyRuntimeError::new_err(CHECKED_OUT_ERROR))
			}

			fn take(&mut self) -> PyResult<S> {
				self.solver
					.take()
					.ok_or_else(|| PyRuntimeError::new_err(CHECKED_OUT_ERROR))
			}
		}

		impl<S: ClauseDatabase> SolverImpl<S> {
			fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> Result {
				let clause: Vec<Lit> = clause
					.into_iter()
					.map(|any| any.and_then(|lit| lit.extract::<Lit>().map_err(PyErr::from)))
					.try_collect()?;
				self.solver_mut()?
					.add_clause(clause.into_iter().map(|lit| lit.0))?;
				Ok(())
			}

			fn add_encoding(
				&mut self,
				con: ConstraintArg,
				enc: Option<Encoder>,
				conditions: Vec<Lit>,
			) -> Result {
				encode_constraint(self.solver_mut()?, con, enc, conditions)
			}

			fn new_var_range(&mut self, num_vars: usize) -> PyResult<VarRange> {
				Ok(VarRange(self.solver_mut()?.new_var_range(num_vars)))
			}
		}

		impl<S: TerminateCallback> SolverImpl<S> {
			fn set_time_limit(&mut self, limit: Option<Duration>) -> Result {
				self.solver_mut()?.set_terminate_callback(limit.map(|dur| {
					let deadline = SystemTime::now() + dur;
					move || {
						if SystemTime::now() > deadline {
							TermSignal::Terminate
						} else {
							TermSignal::Continue
						}
					}
				}));
				Ok(())
			}
		}

		impl<S: Default> Default for SolverImpl<S> {
			fn default() -> Self {
				Self {
					solver: Some(S::default()),
				}
			}
		}

		impl<Owner: PyClass<Frozen = False>, S> SolverResultImpl<Owner, S> {
			fn exit(
				&mut self,
				py: Python<'_>,
				slot: fn(&mut Owner) -> &mut SolverImpl<S>,
			) -> PyResult<bool> {
				self.result = None;
				if let Some(solver) = self.solver.take() {
					let mut owner = self.owner.bind(py).borrow_mut();
					let inner = slot(std::ops::DerefMut::deref_mut(&mut owner));
					if inner.solver.is_some() {
						return Err(PyRuntimeError::new_err(RESTORED_ERROR));
					}
					inner.solver = Some(solver);
				}
				Ok(false)
			}
		}

		impl<Owner, S: Solver> SolverResultImpl<Owner, S> {
			fn from_solver(owner: Py<Owner>, mut solver: S) -> Self {
				let result = match solver.solve() {
					SolveResult::Satisfied(sol) => {
						let sol: Box<dyn Valuation + '_> = Box::new(sol);
						// SAFETY: The returned valuation is tied to the checked-out
						// solver and is dropped before solver access is restored.
						let sol: Box<dyn Valuation + 'static> = unsafe { transmute(sol) };
						SolverResultState::Satisfied(sol)
					}
					SolveResult::Unsatisfiable(_) => {
						SolverResultState::Unsatisfiable(Box::new(|_| None))
					}
					SolveResult::Unknown => SolverResultState::Unknown,
				};
				Self::new(owner, result, solver, false)
			}
		}

		impl<Owner, S: Assumptions> SolverResultImpl<Owner, S> {
			fn from_assumptions_solver(
				owner: Py<Owner>,
				mut solver: S,
				assumptions: &[Lit],
			) -> Self {
				let result = match solver.solve_assuming(assumptions.iter().map(|lit| lit.0)) {
					SolveResult::Satisfied(sol) => {
						let sol: Box<dyn Valuation + '_> = Box::new(sol);
						// SAFETY: The returned valuation is only valid while the solver
						// state remains alive and unchanged. The corresponding result
						// object owns the checked-out solver and drops this boxed value
						// before restoring solver access.
						let sol: Box<dyn Valuation + 'static> = unsafe { transmute(sol) };
						SolverResultState::Satisfied(sol)
					}
					SolveResult::Unsatisfiable(fail) => {
						let fail: Box<dyn FailedAssumptions + '_> = Box::new(fail);
						// SAFETY: Same reasoning as above for the failed-assumptions
						// object.
						let fail: Box<dyn FailedAssumptions + 'static> = unsafe { transmute(fail) };
						let fail = move |lit: BaseLit| Some(fail.fail(lit));
						SolverResultState::Unsatisfiable(Box::new(fail))
					}
					SolveResult::Unknown => SolverResultState::Unknown,
				};
				Self::new(owner, result, solver, true)
			}
		}

		impl<Owner, S> SolverResultImpl<Owner, S> {
			fn failed(&self, lit: Lit) -> PyResult<Option<bool>> {
				let Some(result) = self.result.as_ref() else {
					return Err(PyRuntimeError::new_err(INACTIVE_RESULT_ERROR));
				};
				if !self.supports_assumptions {
					return Ok(None);
				}
				Ok(match result {
					SolverResultState::Unsatisfiable(fail) => fail(lit.0),
					_ => None,
				})
			}

			fn new(
				owner: Py<Owner>,
				result: SolverResultState,
				solver: S,
				supports_assumptions: bool,
			) -> Self {
				Self {
					owner,
					result: Some(result),
					solver: Some(solver),
					supports_assumptions,
				}
			}

			fn status(&self) -> PyResult<Status> {
				let Some(result) = self.result.as_ref() else {
					return Err(PyRuntimeError::new_err(INACTIVE_RESULT_ERROR));
				};
				Ok(match result {
					SolverResultState::Satisfied(_) => Status::SATISFIED,
					SolverResultState::Unsatisfiable(_) => Status::UNSATISFIABLE,
					SolverResultState::Unknown => Status::UNKNOWN,
				})
			}

			fn value(&self, lit: Lit) -> PyResult<Option<bool>> {
				let Some(result) = self.result.as_ref() else {
					return Err(PyRuntimeError::new_err(INACTIVE_RESULT_ERROR));
				};
				Ok(match result {
					SolverResultState::Satisfied(sol) => Some(sol.value(lit.0)),
					_ => None,
				})
			}
		}

		py_solver_result!(CaDiCaLResult, CaDiCaLInner, Cadical);

		py_solver_result!(KissatResult, KissatInner, Kissat);
	}
}
