#[cfg(feature = "ipasir-up")]
use std::sync::{Arc, Mutex};
use std::{
	ffi::{c_void, CString},
	fmt,
};

use pindakaas_cadical::{ccadical_copy, ccadical_phase, ccadical_unphase};
use pindakaas_derive::IpasirSolver;

#[cfg(feature = "ipasir-up")]
use crate::solver::libloading::PropagatorPointer;
use crate::{solver::libloading::FFIPointer, Lit, VarFactory};

#[derive(IpasirSolver)]
#[ipasir(krate = pindakaas_cadical, assumptions, learn_callback, term_callback, ipasir_up)]
pub struct Cadical {
	/// The raw pointer to the Cadical solver.
	ptr: *mut c_void,
	/// The variable factory for this solver.
	#[cfg(not(feature = "ipasir-up"))]
	vars: VarFactory,
	/// The variable factory for this solver.
	#[cfg(feature = "ipasir-up")]
	vars: Arc<Mutex<VarFactory>>,
	/// The callback used when a clause is learned.
	learn_cb: FFIPointer,
	/// The callback used to check whether the solver should terminate.
	term_cb: FFIPointer,

	#[cfg(feature = "ipasir-up")]
	/// The external propagator called by the solver
	prop: Option<PropagatorPointer>,
}

impl Default for Cadical {
	fn default() -> Self {
		Self {
			// SAFETY: Assume ipasir_init() returns a non-null pointer.
			ptr: unsafe { pindakaas_cadical::ipasir_init() },
			#[cfg(not(feature = "ipasir-up"))]
			vars: VarFactory::default(),
			#[cfg(feature = "ipasir-up")]
			vars: Arc::default(),
			learn_cb: FFIPointer::default(),
			term_cb: FFIPointer::default(),
			#[cfg(feature = "ipasir-up")]
			prop: None,
		}
	}
}

impl Clone for Cadical {
	fn clone(&self) -> Self {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		let ptr = unsafe { ccadical_copy(self.ptr) };
		#[cfg(not(feature = "ipasir-up"))]
		let vars = self.vars; // Copy
		#[cfg(feature = "ipasir-up")]
		let vars = Arc::new(Mutex::new(*self.vars.as_ref().lock().unwrap()));
		Self {
			ptr,
			vars,
			learn_cb: FFIPointer::default(),
			term_cb: FFIPointer::default(),
			#[cfg(feature = "ipasir-up")]
			prop: None,
		}
	}
}

impl fmt::Debug for Cadical {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("Cadical")
			.field("ptr", &self.ptr)
			.field("vars", &self.vars)
			.finish()
	}
}

impl Cadical {
	pub fn phase(&mut self, lit: Lit) {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe { ccadical_phase(self.ptr, lit.0.get()) }
	}

	pub fn unphase(&mut self, lit: Lit) {
		// SAFETY: Pointer known to be non-null, no other known safety concerns.
		unsafe { ccadical_unphase(self.ptr, lit.0.get()) }
	}

	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn set_option(&mut self, name: &str, value: i32) {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { pindakaas_cadical::ccadical_set_option(self.ptr, name.as_ptr(), value) }
	}

	#[doc(hidden)] // TODO: Add a better interface for options in Cadical
	pub fn get_option(&self, name: &str) -> i32 {
		let name = CString::new(name).unwrap();
		// SAFETY: Pointer known to be non-null, we assume that Cadical Option API
		// handles non-existing options gracefully.
		unsafe { pindakaas_cadical::ccadical_get_option(self.ptr, name.as_ptr()) }
	}
}

#[cfg(test)]
mod tests {
	use traced_test::test;

	use crate::{
		linear::LimitComp,
		solver::{cadical::Cadical, SolveResult, Solver},
		CardinalityOne, ClauseDatabase, Encoder, PairwiseEncoder, Unsatisfiable, Valuation,
	};

	#[test]
	fn test_cadical() {
		let mut slv = Cadical::default();
		assert!(slv.signature().starts_with("cadical"));

		let a = slv.new_var().into();
		let b = slv.new_var().into();
		PairwiseEncoder::default()
			.encode(
				&mut slv,
				&CardinalityOne {
					lits: vec![a, b],
					cmp: LimitComp::Equal,
				},
			)
			.unwrap();
		let res = slv.solve(|model| {
			assert!(
				(model.value(!a).unwrap() && model.value(b).unwrap())
					|| (model.value(a).unwrap() && model.value(!b).unwrap()),
			);
		});
		assert_eq!(res, SolveResult::Sat);
		// Test clone implementation
		let mut cp = slv.clone();
		assert_eq!(
			cp.solve(|model| {
				assert!(
					(model.value(!a).unwrap() && model.value(b).unwrap())
						|| (model.value(a).unwrap() && model.value(!b).unwrap()),
				);
			}),
			SolveResult::Sat
		);
	}

	#[test]
	fn test_cadical_empty_clause() {
		let mut slv = Cadical::default();
		assert_eq!(slv.add_clause([]), Err(Unsatisfiable));
		assert_eq!(slv.solve(|_| unreachable!()), SolveResult::Unsat);
	}

	#[cfg(feature = "ipasir-up")]
	#[test]
	fn test_ipasir_up() {
		use std::any::Any;

		use itertools::Itertools;

		use crate::{
			helpers::tests::assert_solutions,
			solver::{
				cadical::CadicalSol, ClausePersistence, NextVarRange, PropagatingSolver,
				Propagator, PropagatorAccess, SolvingActions, VarRange,
			},
			Lit,
		};

		let mut slv = Cadical::default();

		let vars = slv.next_var_range(5).unwrap();

		struct Dist2 {
			vars: VarRange,
			tmp: Vec<Vec<Lit>>,
		}
		impl Propagator for Dist2 {
			fn is_check_only(&self) -> bool {
				true
			}
			fn check_model(
				&mut self,
				_slv: &mut dyn SolvingActions,
				model: &dyn crate::Valuation,
			) -> bool {
				let mut vars = self.vars.clone();
				while let Some(v) = vars.next() {
					if model.value(v.into()).unwrap_or(true) {
						let next_2 = vars.clone().take(2);
						for o in next_2 {
							if model.value(o.into()).unwrap_or(true) {
								self.tmp.push(vec![!v, !o]);
							}
						}
					}
				}
				self.tmp.is_empty()
			}
			fn add_external_clause(
				&mut self,
				_slv: &mut dyn SolvingActions,
			) -> Option<(Vec<Lit>, ClausePersistence)> {
				self.tmp.pop().map(|c| (c, ClausePersistence::Forgettable))
			}

			fn as_any(&self) -> &dyn Any {
				self
			}
			fn as_mut_any(&mut self) -> &mut dyn Any {
				self
			}
		}

		let p = Dist2 {
			vars: vars.clone(),
			tmp: Vec::new(),
		};
		slv.set_external_propagator(Some(p));
		slv.add_clause(vars.clone().map_into()).unwrap();
		for v in vars.clone() {
			PropagatingSolver::add_observed_var(&mut slv, v)
		}

		let mut solns: Vec<Vec<Lit>> = Vec::new();
		let push_sol = |model: &CadicalSol, solns: &mut Vec<Vec<Lit>>| {
			let sol: Vec<Lit> = vars
				.clone()
				.map(|v| {
					if model.value(v.into()).unwrap() {
						v.into()
					} else {
						!v
					}
				})
				.collect_vec();
			solns.push(sol);
		};
		while slv.solve(|model| push_sol(model, &mut solns)) == SolveResult::Sat {
			slv.add_clause(solns.last().unwrap().iter().map(|l| !l))
				.unwrap()
		}
		solns.sort();

		let (a, b, c, d, e) = vars.clone().iter_lits().collect_tuple().unwrap();
		assert_eq!(
			solns,
			vec![
				vec![a, !b, !c, d, !e],
				vec![a, !b, !c, !d, e],
				vec![a, !b, !c, !d, !e],
				vec![!a, b, !c, !d, e],
				vec![!a, b, !c, !d, !e],
				vec![!a, !b, c, !d, !e],
				vec![!a, !b, !c, d, !e],
				vec![!a, !b, !c, !d, e],
			]
		);
		assert!(slv.propagator::<Dist2>().unwrap().tmp.is_empty())
	}
}
