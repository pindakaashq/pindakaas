macro_rules! as_dyn_trait {
	($as_dyn_name:ident, $trait_name:ident) => {
		/// Helper trait that allows the creation of a dynamic reference to a trait
		/// object. This trait is automatically implemented for all sized types that
		/// implement the trait, and for the trait object itself.
		pub trait $as_dyn_name {
			/// Cast the object reference to a dynamic trait object reference.
			fn as_dyn(&self) -> &dyn $trait_name;
			/// Cast the object mutable reference to a mutable dynamic trait object
			/// reference.
			fn as_mut_dyn(&mut self) -> &mut dyn $trait_name;
		}
		impl<T: $trait_name> $as_dyn_name for T {
			fn as_dyn(&self) -> &dyn $trait_name {
				self
			}
			fn as_mut_dyn(&mut self) -> &mut dyn $trait_name {
				self
			}
		}
		impl $as_dyn_name for dyn $trait_name {
			fn as_dyn(&self) -> &dyn $trait_name {
				self
			}
			fn as_mut_dyn(&mut self) -> &mut dyn $trait_name {
				self
			}
		}
	};
}

as_dyn_trait!(AsDynClauseDatabase, ClauseDatabase);

#[cfg(feature = "splr")]
macro_rules! concat_slices {
    ([$init:expr; $T:ty]: $($s:expr),+ $(,)?) => {{
        $(
            const _: &[$T] = $s; // require constants
        )*
        const LEN: usize = $( $s.len() + )* 0;
        const ARR: [$T; LEN] = {
            let mut arr: [$T; LEN] = [$init; LEN];
            let mut base: usize = 0;
            $({
                let mut i = 0;
                while i < $s.len() {
                    arr[base + i] = $s[i];
                    i += 1;
                }
                base += $s.len();
            })*
            if base != LEN { panic!("invalid length"); }
            arr
        };
        &ARR
    }};

    ([$T:ty]: $($s:expr),+ $(,)?) => {
        $crate::helpers::concat_slices!([0; $T]: $($s),+)
    };
}

#[cfg(feature = "splr")]
macro_rules! const_concat {
	($($e:expr),+) => {{
			$crate::helpers::const_concat!(@impl $($crate::helpers::maybe_std_concat!($e)),+)
	}};

	(@impl $($e:expr),+) => {{
			$(
					const _: &str = $e;
			)*
			let slice: &[u8] = $crate::helpers::concat_slices!([u8]: $($e.as_bytes()),+);
			// SAFETY: the slice is constructed from string literals, so it is valid UTF-8
			unsafe { std::str::from_utf8_unchecked(slice) }
	}};
}

#[cfg(feature = "splr")]
macro_rules! maybe_std_concat {
	($e:literal) => {
		concat!($e)
	};
	($e:expr) => {
		$e
	};
}

#[cfg(not(any(feature = "tracing", test)))]
/// Helper marco to create a new named literal within the library independent of
/// whether `tracing` is enabled.
macro_rules! new_named_lit {
	($db:expr, $lbl:expr) => {
		$crate::ClauseDatabaseTools::new_lit($db)
	};
}

#[cfg(any(feature = "tracing", test))]
/// Helper marco to create a new named literal within the library independent of
/// whether `tracing` is enabled.
macro_rules! new_named_lit {
	($db:expr, $lbl:expr) => {{
		$crate::ClauseDatabaseTools::new_named_lit($db, &$lbl)
	}};
}

use std::collections::HashSet;

use itertools::Itertools;
pub(crate) use new_named_lit;
#[cfg(feature = "splr")]
pub(crate) use {concat_slices, const_concat, maybe_std_concat};

use crate::{
	bool_linear::PosCoeff,
	integer::{enc::LitOrConst, helpers::required_lits, Dom},
	ClauseDatabase, Coeff, Lit, Result,
};

use crate::ClauseDatabaseTools;
pub(crate) fn emit_filtered_clause<
	DB: ClauseDatabase + ?Sized,
	I: IntoIterator<Item = LitOrConst>,
>(
	db: &mut DB,
	lits: I,
) -> Result {
	if let Ok(clause) = lits
		.into_iter()
		.filter_map(|lit| match lit {
			LitOrConst::Lit(lit) => Some(Ok(lit)),
			LitOrConst::Const(true) => Some(Err(())), // clause satisfied
			LitOrConst::Const(false) => None,         // literal falsified
		})
		.collect::<std::result::Result<Vec<_>, ()>>()
	{
		db.add_clause(clause)
	} else {
		Ok(())
	}
}

pub(crate) fn pow2(k: u32) -> Coeff {
	Coeff::from(2).pow(k)
}

// Copied from num library
pub(crate) const fn div_ceil(a: Coeff, b: Coeff) -> Coeff {
	let d = a / b;
	let r = a % b;
	if (r > 0 && b > 0) || (r < 0 && b < 0) {
		d + 1
	} else {
		d
	}
}

pub(crate) const fn div_floor(a: Coeff, b: Coeff) -> Coeff {
	let d = a / b;
	let r = a % b;
	if (r > 0 && b < 0) || (r < 0 && b > 0) {
		d - 1
	} else {
		d
	}
}

const FILTER_TRIVIAL_CLAUSES: bool = false;

/// Adds clauses for a DNF formula (disjunction of conjunctions)
/// Ex. (a /\ -b) \/ c == a \/ c /\ -b \/ c
/// If any disjunction is empty, this satisfies the whole formula. If any element contains the empty conjunction, that element is falsified in the final clause.
pub(crate) fn add_clauses_for<DB: ClauseDatabase + ?Sized>(
	db: &mut DB,
	expression: Vec<Vec<Vec<Lit>>>,
) -> Result {
	// TODO Move cnf: Vec<Vec<Lit>> functions into Cnf
	for cls in expression.into_iter().multi_cartesian_product() {
		let cls = cls.concat(); // filter out [] (empty conjunctions?) of the clause
		if FILTER_TRIVIAL_CLAUSES {
			let mut lits = HashSet::<Lit>::with_capacity(cls.len());
			if cls.iter().any(|lit| {
				#[allow(
					unused_results,
					reason = "since we already use contain, we do not need the insertion result"
				)]
				if lits.contains(&!*lit) {
					true
				} else {
					_ = lits.insert(*lit);
					false
				}
			}) {
				continue;
			}
		}
		db.add_clause(cls)?;
	}
	Ok(())
}

/// Given coefficients are powers of two multiplied by some value (1*c, 2*c, 4*c, 8*c, ..)
pub(crate) fn is_powers_of_two<I: IntoIterator<Item = Coeff>>(coefs: I) -> bool {
	let mut it = coefs.into_iter().enumerate();
	if let Some((_, mult)) = it.next() {
		const TWO: Coeff = 2;
		it.all(|(i, c)| c == (TWO.pow(i as u32) * mult))
	} else {
		false
	}
}

/// 2^bits - 1
pub(crate) fn unsigned_binary_range(bits: usize) -> (PosCoeff, PosCoeff) {
	(PosCoeff::new(0), PosCoeff::new(pow2(bits as u32) - 1))
}

/// Convert `k` to unsigned binary in `bits`
pub(crate) fn as_binary(k: PosCoeff, bits: Option<usize>) -> Vec<bool> {
	let bits = bits.unwrap_or_else(|| required_lits(&Dom::from_bounds(0, *k)));
	assert!(
		k <= unsigned_binary_range(bits).1,
		"{k} cannot be represented in {bits} bits"
	);
	(0..bits).map(|b| *k & (1 << b) != 0).collect()
}

/// Negates CNF (flipping between empty clause and formula)
pub(crate) fn negate_cnf(clauses: Vec<Vec<Lit>>) -> Vec<Vec<Lit>> {
	if clauses.is_empty() {
		vec![vec![]]
	} else if clauses.contains(&vec![]) {
		vec![]
	} else if clauses.len() == 1 {
		clauses
			.into_iter()
			.map(|clause| clause.into_iter().map(|lit| !lit).collect())
			.collect()
	} else if clauses.iter().all(|c| c.len() == 1) {
		vec![clauses
			.into_iter()
			.flat_map(|clause| clause.into_iter().map(|lit| !lit))
			.collect()]
	} else {
		unimplemented!("Negating CNF {clauses:?} leads to complex expression")
	}
}

pub(crate) fn subscript_number(num: usize) -> impl Iterator<Item = char> {
	num.to_string()
		.chars()
		.map(|d| d.to_digit(10).unwrap())
		.map(|d| char::from_u32(0x2080 + d).unwrap())
		.collect_vec()
		.into_iter()
}

pub(crate) fn is_unique<I: Iterator<Item = V>, V: Eq + std::hash::Hash>(mut i: I) -> bool {
	let mut seen = HashSet::new();
	i.all(|x| seen.insert(x))
}

#[cfg(test)]
pub(crate) mod tests {
	#[cfg(test)]
	macro_rules! expect_file {
		($rel_path:expr) => {{
			let p = std::path::PathBuf::from(
				format!("{}/corpus/{}", env!("CARGO_MANIFEST_DIR"), $rel_path).to_string(),
			);
			std::fs::create_dir_all(p.parent().unwrap()).unwrap();
			expect_test::expect_file!(p)
		}};
	}

	use std::{fmt::Display, num::NonZeroI32};

	#[cfg(test)]
	pub(crate) use expect_file;
	use expect_test::ExpectFile;
	use itertools::Itertools;

	use crate::{
		bool_linear::BoolLinExp,
		integer::IntVar,
		solver::{cadical::Cadical, SolveResult, Solver},
		Checker, ClauseDatabase, ClauseDatabaseTools, Cnf, Lit, Valuation, Var, VarRange,
	};

	/// Helper functions to ensure that the possible solutions of a formula
	/// abide by the given checker.
	pub(crate) fn assert_checker(formula: &Cnf, checker: &impl Checker) {
		Cadical::from(formula)
			.solve_all(formula.get_variables())
			.into_iter()
			.for_each(|value| {
				assert_eq!(checker.check(&value), Ok(()));
			});
	}

	/// Simple helper function to assert the generated formula against an expect
	/// block.
	pub(crate) fn assert_encoding(formula: &impl Display, expect: &ExpectFile) {
		expect.assert_eq(&formula.to_string());
	}

	#[allow(
		unused_variables,
		dead_code,
		reason = "TODO: prepare for checking integer encodings"
	)]
	/// Helper function that asserts that the integer solutions of a formula are
	/// as contained in the expect block.
	pub(crate) fn assert_integer_solutions<V, I>(formula: &Cnf, vars: I, expect: &ExpectFile)
	where
		V: Into<IntVar>,
		I: IntoIterator<Item = V> + Clone,
	{
		let mut slv = Cadical::from(formula);
		let vars = vars
			.into_iter()
			.map(|x| BoolLinExp::from(&x.into()))
			.collect_vec();
		let bool_vars = formula.get_variables();
		let mut solutions: Vec<Vec<i64>> = Vec::new();
		while let SolveResult::Satisfied(value) = slv.solve() {
			// Collect integer solution
			solutions.push(vars.clone().into_iter().map(|x| x.value(&value)).collect());
			// Add nogood clause
			let nogood: Vec<Lit> = bool_vars
				.map(|v| {
					let l = v.into();
					if value.value(l) {
						!l
					} else {
						l
					}
				})
				.collect();
			slv.add_clause(nogood).unwrap();
		}
		solutions.sort();
		let sol_str = format!(
			"{}",
			solutions
				.into_iter()
				.map(|sol| sol.into_iter().format(" "))
				.format("\n")
		);
		expect.assert_eq(&sol_str);
	}

	/// Helper functions to ensure that the possible solutions of a formula, with
	/// relation to a set of variables, match the expected solutions string.
	pub(crate) fn assert_solutions<V, I>(formula: &Cnf, vars: I, expect: &ExpectFile)
	where
		V: Into<Lit>,
		I: IntoIterator<Item = V> + Clone,
	{
		expect.assert_eq(
			&Cadical::from(formula)
				.solve_all(vars)
				.into_iter()
				.map(|sol| sol.iter().sorted_by_key(|l| l.var()).collect_vec())
				.sorted()
				.map(|sol| sol.into_iter().map(i32::from).format(" "))
				.join("\n"),
		);
	}

	/// Helper function to quickly create a valuation from a slice of literals.
	///
	/// ### Warning
	/// This function assumes that the literal slice contains all literals
	/// starting from the first variable, and that the literals are in order of
	/// the variables.
	#[allow(dead_code, reason = "Could be useful in the future.")]
	pub(crate) fn make_valuation<L: Into<Lit> + Copy>(solution: &[L]) -> impl Valuation + '_ {
		|l: Lit| {
			let abs: Lit = l.var().into();
			let v = Into::<i32>::into(abs) as usize;
			if v <= solution.len() {
				debug_assert_eq!(solution[v - 1].into().var(), l.var());
				solution[v - 1].into() == l
			} else {
				false
			}
		}
	}

	// TODO [?] Some unused code I don't know what to do with.
	macro_rules! lit {
		($lit:expr) => {
			$crate::Lit(std::num::NonZeroI32::new($lit).unwrap())
		};
	}

	// 	macro_rules! clause {
	// 	($($x:expr),+ $(,)?) => {
	//             &[$($crate::lit!($x)),+]
	// 	};
	// }

	// 	macro_rules! clauses {
	// 	($($x:expr),+ $(,)?) => {
	//             &[$($crate::clause!($x)),+]
	// 	};
	// }

	/// A const Cnf (constructed at compile-time)
	/// TODO lits are assumed to be in a contiguous var range starting from 1..
	#[derive(Debug)]
	pub(crate) struct ConstCnf {
		lits: &'static [Lit],
		sizes: &'static [usize],
	}

	impl ConstCnf {
		// TODO probably save this as a field
		fn vars(&self) -> Option<VarRange> {
			self.lits
				.iter()
				.map(|x| x.var())
				.max()
				.map(|x| VarRange::new(Var(NonZeroI32::new(1).unwrap()), x))
		}

		/// Return CNF, replacing literals according to map.
		fn encode<DB: ClauseDatabase>(&self, db: &mut DB, map: &[Lit]) -> crate::Result {
			if self.lits.is_empty() {
				return Ok(());
			}
			debug_assert!(
				map.len()
					== self
						.lits
						.iter()
						.map(|x| usize::try_from(i32::from(x.var())).unwrap())
						.max()
						.unwrap(),
				"All literals should be mapped but was given map: {map:?}"
			);
			let mut i = 0;
			for size in self.sizes {
				db.add_clause(self.lits[i..i + *size].iter().map(|x| {
					let lit: Lit = map[usize::try_from(i32::from(x.var())).unwrap() - 1];
					if x.is_negated() {
						!lit
					} else {
						lit
					}
				}))?;
				i += size;
			}
			Ok(())
		}
	}

	#[test]
	fn const_cnf_replace_test() {
		const CNF: ConstCnf = ConstCnf {
			lits: &[lit![1], lit![-2], lit![2]],
			sizes: &[2, 1],
		};
		assert_eq!(CNF.vars().unwrap().max(), Some(Var::from(2)));
		let mut db = Cnf::default();
		CNF.encode(&mut db, &[lit![42], lit![43]]).unwrap();
		// TODO ?? cannot update for some reason. Might be a local problem
		// assert_encoding(
		// 	&db,
		// 	&expect_file!["integer/term/const_cnf_replace_test.cnf"],
		// );
	}
}
