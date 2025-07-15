use std::{
	cell::{RefCell, RefMut},
	collections::VecDeque,
	ffi::c_void,
	fmt,
	marker::PhantomData,
	num::NonZeroI32,
	rc::Rc,
	slice,
};

use rustc_hash::FxHashMap;

use crate::{
	solver::{
		ipasir::{
			AccessIpasirStore, BasicIpasirStorage, IpasirSolverMethods, IpasirStore,
			IpasirStoreInner,
		},
		propagation::{
			ClausePersistence, ExtendedSolvingActions, PropagatingSolver, Propagator,
			PropagatorDefinition, SearchDecision, SolvingActions,
		},
		VarFactory,
	},
	Lit, Var,
};

#[derive(Default)]
/// Storage struct containing a [`Propagator`] and helper data to translate
/// between IPASIR-UP propagator callbacks and the Rust [`Propagator`].
pub(crate) struct IpasirPropagator {
	/// An external propagator used by the solver.
	///
	/// This attribute ensures that the [`Propagator`] is correctly released (and
	/// dropped) when the [`IpasirSolver`] is dropped. It is given by the solver
	/// using a pointer.
	external_propagator: Option<Rc<RefCell<dyn Propagator>>>,
	/// Reason clause queue
	reason_queue: VecDeque<Lit>,
	/// The current literal that is being explained
	explaining: Option<Lit>,
	/// Queue of literals for the external clause to be yielded.
	clause_queue: Option<VecDeque<Lit>>,
}

/// Helper trait that allows abstraction over different [`IpasirStore`] generics
/// as long as `UP` is set to 1.
trait IpasirPropagatorStorage {
	/// Returns whether a propagator is currently connected.
	fn has_propagator(&self) -> bool;
	/// Stores a new propagator in the storage, returning a pointer that is valid
	/// as long as the solver is alive and the propagator is connected, with a
	/// table of callbacks for the propagator methods.
	fn set_propagator<P: PropagatorDefinition + 'static>(
		&mut self,
		propagator: Rc<RefCell<P>>,
	) -> (*mut c_void, IpasirVTable);
	/// Resets the propagator storage, dropping the connected propagator (if any).
	fn reset_propagator(&mut self);
}

/// Helping wrapper struct to provide [`ExtendedSolvingActions`] to propagators
/// when connected to an IPASIR-UP solver.
struct IpasirSolvingActions<'a, Impl> {
	ptr: *mut c_void,
	vars: &'a mut VarFactory,
	_methods: PhantomData<Impl>,
}

/// Trait implemented by IPASIR solvers that support the extended IPASIR-UP
/// interface for external propagation.
///
/// When a type implements this trait and [`AccessIpasirSolver`] yielding a
/// [`IpasirStore`] with `UP = 1`, then [`PropagatingSolver`] is implemented
/// automatically.
pub(crate) trait IpasirUserPropagationMethods {
	#[expect(
		clippy::type_complexity,
		reason = "arguments are easier to support in C bindings than complex types"
	)]
	const IPASIR_CONNECT_EXTERNAL_PROPAGATOR: unsafe extern "C" fn(
		slv: *mut c_void,
		propagator_data: *mut c_void,
		notify_assignments: unsafe extern "C" fn(*mut c_void, *const i32, usize),
		notify_new_decision_level: unsafe extern "C" fn(*mut c_void),
		notify_backtrack: unsafe extern "C" fn(*mut c_void, usize, bool),
		cb_check_found_model: unsafe extern "C" fn(*mut c_void, *const i32, usize) -> bool,
		cb_has_external_clause: unsafe extern "C" fn(*mut c_void, *mut bool) -> bool,
		cb_add_external_clause_lit: unsafe extern "C" fn(*mut c_void) -> i32,
		is_lazy: bool,
		forgettable_reasons: bool,
		notify_fixed: bool,
		cb_decide: unsafe extern "C" fn(*mut c_void) -> i32,
		cb_propagate: unsafe extern "C" fn(*mut c_void) -> i32,
		cb_add_reason_clause_lit: unsafe extern "C" fn(*mut c_void, i32) -> i32,
		notify_fixed_assignment: unsafe extern "C" fn(*mut c_void, i32),
	);
	const IPASIR_DISCONNECT_EXTERNAL_PROPAGATOR: unsafe extern "C" fn(slv: *mut c_void);
	const IPASIR_ADD_OBSERVED_VAR: unsafe extern "C" fn(slv: *mut c_void, lit: i32);
	const IPASIR_REMOVE_OBSERVED_VAR: unsafe extern "C" fn(slv: *mut c_void, lit: i32);
	const IPASIR_RESET_OBSERVED_VARS: unsafe extern "C" fn(slv: *mut c_void);
	const IPASIR_IS_DECISION: unsafe extern "C" fn(slv: *mut c_void, lit: i32) -> bool;
	const IPASIR_FORCE_BACKTRACK: unsafe extern "C" fn(slv: *mut c_void, level: usize);
}

/// Temporary object used to store the callbacks for the IPASIR-UP C interface
/// for a specific [`Propagator`] implementation. Generally it is also specific
/// to a [`ExtendedSolvingActions`] implementation, and is generated when
/// creating a new [`IpasirPropStore`].
pub(crate) struct IpasirVTable {
	pub(crate) notify_assignments: unsafe extern "C" fn(*mut c_void, *const i32, usize),
	pub(crate) notify_new_decision_level: unsafe extern "C" fn(*mut c_void),
	pub(crate) notify_backtrack: unsafe extern "C" fn(*mut c_void, usize, bool),
	pub(crate) check_found_model: unsafe extern "C" fn(*mut c_void, *const i32, usize) -> bool,
	pub(crate) has_external_clause: unsafe extern "C" fn(*mut c_void, *mut bool) -> bool,
	pub(crate) add_external_clause_lit: unsafe extern "C" fn(*mut c_void) -> i32,
	pub(crate) is_lazy: bool,
	pub(crate) forgettable_reasons: bool,
	pub(crate) notify_fixed: bool,
	pub(crate) decide: unsafe extern "C" fn(*mut c_void) -> i32,
	pub(crate) propagate: unsafe extern "C" fn(*mut c_void) -> i32,
	pub(crate) add_reason_clause_lit: unsafe extern "C" fn(*mut c_void, i32) -> i32,
	pub(crate) notify_fixed_assignment: unsafe extern "C" fn(*mut c_void, i32),
}

impl<Impl: AccessIpasirStore + IpasirSolverMethods + IpasirUserPropagationMethods> PropagatingSolver
	for Impl
where
	Impl::Store: BasicIpasirStorage + IpasirPropagatorStorage,
{
	fn add_observed_var(&mut self, var: Var) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_ADD_OBSERVED_VAR function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Self::IPASIR_ADD_OBSERVED_VAR(self.ipasir_store_mut().solver_ptr(), var.into());
		}
	}

	fn connect_propagator<P: PropagatorDefinition + 'static>(
		&mut self,
		propagator: Rc<RefCell<P>>,
	) {
		// Disconnect previous propagator (if any)
		self.disconnect_propagator();

		// Store the propagator and receive the data pointer and callback pointers
		let (data_ptr, vtable) = self.ipasir_store_mut().set_propagator(propagator);

		// Connect the wrapped propagator to the solver
		//
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_CONNECT_EXTERNAL_PROPAGATOR function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Self::IPASIR_CONNECT_EXTERNAL_PROPAGATOR(
				self.ipasir_store().solver_ptr(),
				data_ptr,
				vtable.notify_assignments,
				vtable.notify_new_decision_level,
				vtable.notify_backtrack,
				vtable.check_found_model,
				vtable.has_external_clause,
				vtable.add_external_clause_lit,
				vtable.is_lazy,
				vtable.forgettable_reasons,
				vtable.notify_fixed,
				vtable.decide,
				vtable.propagate,
				vtable.add_reason_clause_lit,
				vtable.notify_fixed_assignment,
			);
		}
	}

	fn disconnect_propagator(&mut self) {
		if self.ipasir_store().has_propagator() {
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_DISCONNECT_EXTERNAL_PROPAGATOR function is expected to abide by
			// the IPASIR-UP interface specification.
			unsafe { Self::IPASIR_DISCONNECT_EXTERNAL_PROPAGATOR(self.ipasir_store().solver_ptr()) }
			self.ipasir_store_mut().reset_propagator();
		}
	}

	fn remove_observed_var(&mut self, var: Var) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_REMOVE_OBSERVED_VAR function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Self::IPASIR_REMOVE_OBSERVED_VAR(self.ipasir_store_mut().solver_ptr(), var.into());
		}
	}

	fn reset_observed_vars(&mut self) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_RESET_OBSERVED_VARS function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Self::IPASIR_RESET_OBSERVED_VARS(self.ipasir_store_mut().solver_ptr());
		}
	}
}

impl<Impl: AccessIpasirStore + IpasirSolverMethods + IpasirUserPropagationMethods> SolvingActions
	for Impl
where
	Impl::Store: BasicIpasirStorage + IpasirPropagatorStorage,
{
	fn is_decision(&mut self, lit: Lit) -> bool {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_IS_DECISION function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe { Self::IPASIR_IS_DECISION(self.ipasir_store_mut().solver_ptr(), lit.into()) }
	}
	fn new_observed_var(&mut self) -> Var {
		let var = self.ipasir_store_mut().vars_mut().next_var.unwrap();
		self.add_observed_var(var);
		var
	}
}

impl IpasirPropagator {
	/// Borrow the propagator in the `external_propagator` field, as a specific
	/// type `P`.
	///
	/// This method is unsafe because it requires that the propagator is of type
	/// `P` and the cell is not borrowed. If the propagator is not of type `P` or
	/// if the cell is already borrowed, this method will panic.
	unsafe fn borrow_propagator_mut<P>(&self) -> RefMut<'_, P> {
		let cell: *const _ = Rc::as_ptr(self.external_propagator.as_ref().unwrap());
		let ptr = cell as *const RefCell<P>;
		(&*ptr).borrow_mut()
	}
}

impl fmt::Debug for IpasirPropagator {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("IpasirPropagator")
			.field(
				"ptr",
				&self.external_propagator.as_ref().map(|x| {
					let x: *const _ = x.as_ref();
					x as *const c_void
				}),
			)
			.field("reason_queue", &self.reason_queue)
			.field("explaining", &self.explaining)
			.field("clause_queue", &self.clause_queue)
			.finish()
	}
}

impl<Impl: IpasirUserPropagationMethods> ExtendedSolvingActions for IpasirSolvingActions<'_, Impl> {
	fn force_backtrack(&mut self, level: usize) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_FORCE_BACKTRACK function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe { Impl::IPASIR_FORCE_BACKTRACK(self.ptr, level) }
	}
}

impl<Impl: IpasirUserPropagationMethods> SolvingActions for IpasirSolvingActions<'_, Impl> {
	fn is_decision(&mut self, lit: Lit) -> bool {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_IS_DECISION function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe { Impl::IPASIR_IS_DECISION(self.ptr, lit.into()) }
	}
	fn new_observed_var(&mut self) -> Var {
		let var = self.vars.next_var_range(1).next().unwrap();
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_ADD_OBSERVED_VAR function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe { Impl::IPASIR_ADD_OBSERVED_VAR(self.ptr, var.into()) }
		var
	}
}

impl<
		Impl: IpasirSolverMethods + IpasirUserPropagationMethods,
		const LRN: usize,
		const TRM: usize,
	> IpasirStore<Impl, LRN, TRM, 1>
{
	unsafe extern "C" fn add_external_clause_lit(store: *mut c_void) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let prop = &mut store.propagator.some_mut();
		let Some(queue) = &mut prop.clause_queue else {
			debug_assert!(false, "has_external_clause did not return true");
			return 0;
		};
		if let Some(l) = queue.pop_front() {
			l.0.get()
		} else {
			prop.clause_queue = None;
			0 // End of clause
		}
	}

	unsafe extern "C" fn add_reason_clause_lit<P: Propagator>(
		store: *mut c_void,
		propagated_lit: i32,
	) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let prop = &mut store.propagator.some_mut();
		let lit = Lit(NonZeroI32::new(propagated_lit).unwrap());
		debug_assert!(prop.explaining.is_none() || prop.explaining == Some(lit));
		// // TODO: Can this be prop.explaining.is_none()?
		if prop.explaining != Some(lit) {
			let new_reason = {
				let mut user_prop: RefMut<P> = prop.borrow_propagator_mut();
				user_prop.add_reason_clause(lit)
			};
			prop.reason_queue = new_reason.into();
			prop.explaining = Some(lit);
		}
		if let Some(l) = prop.reason_queue.pop_front() {
			l.0.into()
		} else {
			// End of explanation
			prop.explaining = None;
			0
		}
	}

	unsafe extern "C" fn check_model<P: Propagator>(
		store: *mut c_void,
		model: *const i32,
		len: usize,
	) -> bool {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let sol = if len > 0 {
			slice::from_raw_parts(model, len)
		} else {
			&[]
		};
		let sol: FxHashMap<Var, bool> = sol
			.iter()
			.map(|&i| (Var(NonZeroI32::new(i.abs()).unwrap()), i >= 0))
			.collect();
		let value = |l: Lit| sol.get(&l.var()).copied().unwrap_or(false);
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: &mut store.vars,
			_methods: PhantomData,
		};
		store
			.propagator
			.as_ref()
			.unwrap()
			.borrow_propagator_mut::<P>()
			.check_solution(&mut slv, &value)
	}
	unsafe extern "C" fn decide<P: Propagator>(store: *mut c_void) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: &mut store.vars,
			_methods: PhantomData,
		};
		match store
			.propagator
			.as_ref()
			.unwrap()
			.borrow_propagator_mut::<P>()
			.decide(&mut slv)
		{
			SearchDecision::Assign(lit) => lit.0.into(),
			SearchDecision::Backtrack(level) => {
				slv.force_backtrack(level);
				0
			}
			SearchDecision::Free => 0,
		}
	}

	unsafe extern "C" fn has_external_clause<P: Propagator>(
		store: *mut c_void,
		is_forgettable: *mut bool,
	) -> bool {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: &mut store.vars,
			_methods: PhantomData,
		};
		let prop = store.propagator.some_mut();
		let ext_clause = prop
			.borrow_propagator_mut::<P>()
			.add_external_clause(&mut slv);
		if let Some((clause, p)) = ext_clause {
			*is_forgettable = p == ClausePersistence::Forgettable;
			prop.clause_queue = Some(clause.into());
		}
		prop.clause_queue.is_some()
	}

	unsafe extern "C" fn notify_assignments<P: Propagator>(
		store: *mut c_void,
		lits: *const i32,
		len: usize,
	) {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		if len > 0 {
			let lits = slice::from_raw_parts(lits as *mut Lit, len);
			store
				.propagator
				.some_ref()
				.borrow_propagator_mut::<P>()
				.notify_assignments(lits);
		};
	}

	unsafe extern "C" fn notify_backtrack<P: Propagator>(
		store: *mut c_void,
		level: usize,
		restart: bool,
	) {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let prop = store.propagator.some_mut();
		prop.explaining = None;
		prop.reason_queue.clear();
		prop.clause_queue = None;
		prop.borrow_propagator_mut::<P>()
			.notify_backtrack(level, restart);
	}

	unsafe extern "C" fn notify_new_decision_level<P: Propagator>(store: *mut c_void) {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		store
			.propagator
			.some_ref()
			.borrow_propagator_mut::<P>()
			.notify_new_decision_level();
	}

	unsafe extern "C" fn notify_persistent_assignments<P: Propagator>(
		store: *mut c_void,
		lit: i32,
	) {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let lit = Lit(NonZeroI32::new(lit).unwrap());
		store
			.propagator
			.some_ref()
			.borrow_propagator_mut::<P>()
			.notify_persistent_assignment(lit);
	}

	unsafe extern "C" fn propagate<P: Propagator>(store: *mut c_void) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<LRN, TRM, 1>);
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: &mut store.vars,
			_methods: PhantomData,
		};
		if let Some(l) = store
			.propagator
			.some_ref()
			.borrow_propagator_mut::<P>()
			.propagate(&mut slv)
		{
			l.0.into()
		} else {
			0 // No propagation
		}
	}
}

impl<Impl, const LRN: usize, const TRM: usize> IpasirPropagatorStorage
	for IpasirStore<Impl, LRN, TRM, 1>
where
	Impl: IpasirSolverMethods + IpasirUserPropagationMethods,
{
	fn has_propagator(&self) -> bool {
		self.store
			.propagator
			.some_ref()
			.external_propagator
			.is_some()
	}

	fn reset_propagator(&mut self) {
		let prop_store = self.store.propagator.some_mut();
		prop_store.external_propagator = None;
		prop_store.reason_queue.clear();
		prop_store.explaining = None;
		prop_store.clause_queue = None;
	}

	fn set_propagator<P: PropagatorDefinition + 'static>(
		&mut self,
		propagator: Rc<RefCell<P>>,
	) -> (*mut c_void, IpasirVTable) {
		// Set the propagator
		self.store.propagator.some_mut().external_propagator = Some(propagator);
		// Crate the data pointer that the IPASIR UP solver will use for all
		// propagator callbacks.
		let store_ptr: *mut _ = &mut *self.store;
		// Construct a table will all callbacks (specific) to the propagator and the
		// specific [`IpasirSolver`] instance.
		let vtable = IpasirVTable {
			notify_assignments: Self::notify_assignments::<P>,
			notify_new_decision_level: Self::notify_new_decision_level::<P>,
			notify_backtrack: Self::notify_backtrack::<P>,
			check_found_model: Self::check_model::<P>,
			has_external_clause: Self::has_external_clause::<P>,
			add_external_clause_lit: Self::add_external_clause_lit,
			is_lazy: P::CHECK_ONLY,
			forgettable_reasons: P::REASON_PERSISTENCE == ClausePersistence::Forgettable,
			notify_fixed: P::PERSISTENT_ASSIGNMENTS,
			decide: Self::decide::<P>,
			propagate: Self::propagate::<P>,
			add_reason_clause_lit: Self::add_reason_clause_lit::<P>,
			notify_fixed_assignment: Self::notify_persistent_assignments::<P>,
		};
		(store_ptr as *mut c_void, vtable)
	}
}
