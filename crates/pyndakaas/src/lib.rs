#![expect(
	clippy::upper_case_acronyms,
	reason = "Python naming for exposed types"
)]
use pyo3::{create_exception, exceptions::PyException, prelude::*};

create_exception!(pindakaas, InvalidEncoder, PyException);
create_exception!(pindakaas, Unsatisfiable, PyException);

#[pymodule]
mod pindakaas {
	use std::fmt::Display;

	use pindakaas::{
		bool_linear::{
			AdderEncoder, BoolLinAggregator, BoolLinExp as BaseBoolLinExp, BoolLinVariant,
			BoolLinear as BaseBoolLinCon, Comparator, SwcEncoder, TotalizerEncoder,
		},
		cardinality::SortingNetworkEncoder,
		cardinality_one::{BitwiseEncoder, LadderEncoder, PairwiseEncoder},
		propositional_logic::{Formula as BaseFormula, TseitinEncoder},
		BoolVal, ClauseDatabase, ClauseDatabaseTools, Cnf, Encoder as _, Lit as BaseLit, Wcnf,
	};
	use pyo3::{prelude::*, types::PyIterator};

	#[pymodule_export]
	use super::InvalidEncoder;
	#[pymodule_export]
	use super::Unsatisfiable;

	#[derive(FromPyObject)]
	/// Argument capture for types that can become [`BoolLinExp`].
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
	/// side, the expression can be turned into a [`BoolLinCon`].
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
	/// Method used to encode a constraint
	///
	/// Warning: Not all encoders can be used to encode each [`ConstraintArg`]. If an
	/// invalid encoder is selected, then an exception will be raised.
	enum Encoder {
		/// Use [`pindakaas::bool_linear::AdderEncoder`], which is able to encode
		/// all Boolean linear constraints.
		ADDER,
		/// Use [`pindakaas::cardinality_one::BitwiseEncoder`], which is able to
		/// encode all Boolean cardinality one constraints.
		BITWISE,
		/// Use [`pindakaas::bool_linear::BddEncoder`], which is able to encode
		/// all Boolean linear constraints.
		DECISION_DIAGRAM,
		/// Use [`pindakaas::cardinality_one::LadderEncoder`], which is able to
		/// encode all Boolean cardinality one constraints.
		LADDER,
		/// Use [`pindakaas::cardinality_one::PairwiseEncoder`], which is able to
		/// encode all Boolean cardinality one constraints.
		PAIRWISE,
		/// Use [`pindakaas::bool_linear::SwcEncoder`], which is able to encode all
		/// Boolean linear constraints.
		SORTED_WEIGHT_COUNTER,
		/// Use [`pindakaas::cardinality::SwcEncoder`], which is able to encode all
		/// Boolean cardinality constraints.
		SORTING_NETWORK,
		/// Use [`pindakaas::bool_linear::TotalizerEncoder`], which is able to
		/// encode all Boolean linear constraints.
		TOTALIZER,
		/// Use [`pindakaas::propositional_logic::TseitinEncdoer`], which is able to
		/// encode propositional logic formulas.
		TSEITIN,
	}

	#[pyclass]
	#[derive(Clone, Debug)]
	/// A propositional logic formula.
	struct Formula(BaseFormula<BoolVal>);

	#[derive(FromPyObject)]
	/// Argument capture for types that can become [`Formula`].
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
	#[derive(Clone, Debug, Default)]
	/// The internal representation of a CNF formula where clauses have optional
	/// associated weights.
	struct WCNFInner(Wcnf);

	/// Internal function to help with the encoding of a constraint given an
	/// optional encoder.
	fn encode_constraint<Db: ClauseDatabase>(
		db: &mut Db,
		con: ConstraintArg,
		enc: Option<Encoder>,
	) -> PyResult<()> {
		let invalid_enc = |con_ty, enc| {
			Err(InvalidEncoder::new_err(format!(
				"unable to encode `{con_ty}' using {enc:?}"
			)))
		};
		let map_unsat = |_err| {
			Unsatisfiable::new_err("constraint was found to be unsatisfiable during encoding")
		};
		match con {
			ConstraintArg::BoolLin(lin) => {
				let aggregated = BoolLinAggregator::default()
					.aggregate(db, &lin.0)
					.map_err(map_unsat)?;
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
				}
				.map_err(map_unsat)?;
			}
			ConstraintArg::Formula(f) => match enc.unwrap_or(Encoder::TSEITIN) {
				Encoder::TSEITIN => TseitinEncoder.encode(db, &f.0).map_err(map_unsat)?,
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

	#[pymethods]
	impl CNFInner {
		fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> PyResult<()> {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
				.collect::<PyResult<_>>()?;
			self.0
				.add_clause(clause.into_iter().map(|lit| lit.0))
				.unwrap();
			Ok(())
		}

		fn add_encoding(&mut self, con: ConstraintArg, enc: Option<Encoder>) -> PyResult<()> {
			encode_constraint(&mut self.0, con, enc)
		}

		#[new]
		fn new() -> Self {
			Self(Default::default())
		}

		fn new_vars(&mut self, num_vars: usize) -> Vec<Lit> {
			self.0
				.new_var_range(num_vars)
				.into_iter()
				.map(|lit| Lit(lit.into()))
				.collect()
		}

		fn to_dimacs(&self) -> String {
			self.0.to_string()
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
		/// Internal method used to convert the [`FormulaArg`] into a
		/// [`BaseFormula<BoolVal>`].
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

		pub fn is_negated(&self) -> bool {
			self.0.is_negated()
		}

		pub fn var(&self) -> Self {
			Self(self.0.var().into())
		}
	}

	impl Display for Lit {
		fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
			self.0.fmt(f)
		}
	}

	#[pymethods]
	impl WCNFInner {
		fn add_clause(&mut self, clause: Bound<'_, PyIterator>) -> PyResult<()> {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
				.collect::<PyResult<_>>()?;
			self.0
				.add_clause(clause.into_iter().map(|lit| lit.0))
				.unwrap();
			Ok(())
		}

		fn add_encoding(&mut self, con: ConstraintArg, enc: Option<Encoder>) -> PyResult<()> {
			encode_constraint(&mut self.0, con, enc)
		}

		fn add_weighted_clause(
			&mut self,
			clause: Bound<'_, PyIterator>,
			weight: i64,
		) -> PyResult<()> {
			let clause: Vec<Lit> = clause
				.into_iter()
				.map(|any| any.and_then(|lit| lit.extract::<Lit>()))
				.collect::<PyResult<_>>()?;
			self.0
				.add_weighted_clause(clause.into_iter().map(|lit| lit.0), weight)
				.unwrap();
			Ok(())
		}

		#[new]
		fn new() -> Self {
			Self(Default::default())
		}

		fn new_vars(&mut self, num_vars: usize) -> Vec<Lit> {
			self.0
				.new_var_range(num_vars)
				.into_iter()
				.map(|lit| Lit(lit.into()))
				.collect()
		}

		fn to_dimacs(&self) -> String {
			self.0.to_string()
		}
	}

	#[pymodule]
	mod solver {
		use std::{
			collections::HashMap,
			sync::Mutex,
			time::{Duration, SystemTime},
		};

		use pindakaas::{
			solver::{
				cadical::Cadical, FailedAssumtions, SlvTermSignal, SolveAssuming, SolveResult,
				TermCallback,
			},
			ClauseDatabase, ClauseDatabaseTools, Valuation,
		};
		use pyo3::{prelude::*, types::PyIterator};

		use crate::pindakaas::{encode_constraint, ConstraintArg, Encoder, Lit};

		#[pyclass]
		#[derive(Debug, Default)]
		struct CaDiCaLInner(Mutex<Cadical>);

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

		fn dur_term_fn(dur: Duration) -> impl Fn() -> SlvTermSignal + 'static {
			let deadline = SystemTime::now() + dur;
			move || {
				if SystemTime::now() > deadline {
					SlvTermSignal::Terminate
				} else {
					SlvTermSignal::Continue
				}
			}
		}

		/// Hack: workaround for https://github.com/PyO3/pyo3/issues/759
		#[pymodule_init]
		fn init(m: &Bound<'_, PyModule>) -> PyResult<()> {
			Python::with_gil(|py| {
				py.import("sys")?
					.getattr("modules")?
					.set_item("pindakaas.pindakaas.solver", m)
			})
		}

		#[pymethods]
		impl CaDiCaLInner {
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

			fn add_encoding(&mut self, con: ConstraintArg, enc: Option<Encoder>) -> PyResult<()> {
				let mut guard = self.0.lock().unwrap();
				encode_constraint(&mut *guard, con, enc)
			}

			#[new]
			fn new() -> Self {
				Self(Default::default())
			}

			fn new_vars(&mut self, num_vars: usize) -> Vec<Lit> {
				let mut guard = self.0.lock().unwrap();
				guard
					.new_var_range(num_vars)
					.into_iter()
					.map(|lit| Lit(lit.into()))
					.collect()
			}

			fn set_time_limit(&mut self, limit: Option<Duration>) {
				let mut guard = self.0.lock().unwrap();
				guard.set_terminate_callback(limit.map(dur_term_fn))
			}

			fn solve_assuming(&self, assumptions: Vec<Lit>) -> (Status, HashMap<i32, bool>) {
				let mut guard = self.0.lock().unwrap();
				let vars = guard.emitted_vars();
				match guard.solve_assuming(assumptions.iter().map(|&lit| lit.0)) {
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
				}
			}
		}
	}
}
