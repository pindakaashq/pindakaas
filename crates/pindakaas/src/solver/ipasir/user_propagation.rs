use std::{
	cell::{RefCell, RefMut},
	ffi::c_void,
	fmt,
	marker::PhantomData,
	num::NonZeroI32,
	rc::Rc,
	slice,
};

use pindakaas_cadical::{CExternalPropagator, CFixedAssignmentListener};

use crate::{
	solver::{
		ipasir::{
			AccessIpasirStore, BasicIpasirStorage, IpasirLiteralMethods, IpasirSolverMethods,
			IpasirStore, IpasirStoreInner,
		},
		propagation::{
			ClauseBuilder, ClausePersistence, ExternalPropagation, PersistentAssignmentListener,
			PersistentAssignmentNotifier, Propagator, PropagatorConfig, SearchDecision, Solution,
			SolvingActions,
		},
	},
	Lit, Var,
};

pub(crate) trait IpasirFixedAssignmentMethods {
	const IPASIR_CONNECT_FIXED_ASSIGNMENT_LISTENER: unsafe extern "C" fn(
		slv: *mut c_void,
		listener: CFixedAssignmentListener,
	);
	const IPASIR_DISCONNECT_FIXED_ASSIGNMENT_LISTENER: unsafe extern "C" fn(slv: *mut c_void);
}

#[derive(Default)]
/// Storage struct containing a [`Propagator`] and helper data to translate
/// between IPASIR-UP propagator callbacks and the Rust [`Propagator`].
pub(crate) struct IpasirPropagator {
	/// An external propagator used by the solver.
	///
	/// This attribute ensures that the [`Propagator`] is correctly released
	/// (and dropped) when the [`IpasirSolver`] is dropped. It is given by the
	/// solver using a pointer.
	external_propagator: Option<Rc<RefCell<dyn Propagator>>>,
	/// An persistent assignment listener being notified by the solver.
	///
	/// This attribute ensures that the [`PersistentAssignmentListener`] is
	/// correctly released (and dropped) when the [`IpasirSolver`] is dropped.
	/// It is given by the solver using a pointer.
	persistent_assignment_listener: Option<Rc<RefCell<dyn PersistentAssignmentListener>>>,
	/// Reusable buffer holding the clause currently being yielded to the
	/// solver: a reason clause when `explaining` is set, or an external clause
	/// when `clause_active` is set. At most one of the two is yielded at a
	/// time, so a single buffer suffices.
	clause: Vec<Lit>,
	/// The literal whose reason clause is currently in `clause`, or `None` when
	/// a reason clause is not being yielded.
	explaining: Option<Lit>,
	/// Whether an external clause is currently being yielded from `clause`.
	clause_active: bool,
}

/// Helper trait that allows abstraction over different [`IpasirStore`] generics
/// as long as `UP` is set to 1.
pub(crate) trait IpasirPropagatorStorage {
	/// Returns whether a persistent assignment listener is currently connected.
	fn has_persistent_assignment_listener(&self) -> bool;

	/// Returns whether a propagator is currently connected.
	fn has_propagator(&self) -> bool;

	/// Resets the persistent listener storage, dropping the connected listener
	/// (if any).
	fn reset_persistent_listener(&mut self);

	/// Resets the propagator storage, dropping the connected propagator (if
	/// any).
	fn reset_propagator(&mut self);

	/// Stores a new persistent listener in the storage, returning the
	/// [`CFixedAssignmentListener`] that can be passed to the solver's C
	/// methods to register the listener.
	fn set_persistent_listener<L: PersistentAssignmentListener + 'static>(
		&mut self,
		listener: Rc<RefCell<L>>,
	) -> CFixedAssignmentListener;

	/// Stores a new propagator in the storage, returning the
	/// [`CExternalPropagator`] that can be passed to the solver's C methods to
	/// register the propagator.
	fn set_propagator<P: PropagatorConfig + 'static>(
		&mut self,
		propagator: Rc<RefCell<P>>,
	) -> CExternalPropagator;
}

/// Helping wrapper struct to provide [`ExtendedSolvingActions`] to propagators
/// when connected to an IPASIR-UP solver.
struct IpasirSolvingActions<Impl> {
	ptr: *mut c_void,
	vars: *mut c_void,
	_methods: PhantomData<Impl>,
}

/// Trait implemented by IPASIR solvers that support the extended IPASIR-UP
/// interface for external propagation.
///
/// When a type implements this trait and [`AccessIpasirSolver`] yielding a
/// [`IpasirStore`] with `UP = 1`, then [`PropagatingSolver`] is implemented
/// automatically.
pub(crate) trait IpasirUserPropagationMethods {
	const IPASIR_ADD_OBSERVED_VAR: unsafe extern "C" fn(slv: *mut c_void, lit: i32);
	const IPASIR_CONNECT_EXTERNAL_PROPAGATOR: unsafe extern "C" fn(
		slv: *mut c_void,
		propagator: CExternalPropagator,
	);
	const IPASIR_DISCONNECT_EXTERNAL_PROPAGATOR: unsafe extern "C" fn(slv: *mut c_void);
	const IPASIR_FORCE_BACKTRACK: unsafe extern "C" fn(slv: *mut c_void, level: usize);
	const IPASIR_IS_DECISION: unsafe extern "C" fn(slv: *mut c_void, lit: i32) -> bool;
	const IPASIR_PHASE: unsafe extern "C" fn(slv: *mut c_void, lit: i32);
	const IPASIR_REMOVE_OBSERVED_VAR: unsafe extern "C" fn(slv: *mut c_void, lit: i32);
	const IPASIR_RESET_OBSERVED_VARS: unsafe extern "C" fn(slv: *mut c_void);
	const IPASIR_UNPHASE: unsafe extern "C" fn(slv: *mut c_void, lit: i32);
}

impl<
		Impl: AccessIpasirStore
			+ IpasirSolverMethods
			+ IpasirLiteralMethods
			+ IpasirUserPropagationMethods,
	> ExternalPropagation for Impl
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

	fn connect_propagator<P: PropagatorConfig + 'static>(&mut self, propagator: Rc<RefCell<P>>) {
		// Disconnect previous propagator (if any)
		self.disconnect_propagator();

		// Store the propagator and receive the data pointer and callback pointers
		let c_prop = self.ipasir_store_mut().set_propagator(propagator);

		// Connect the wrapped propagator to the solver
		//
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_CONNECT_EXTERNAL_PROPAGATOR function is expected to abide by the
		// IPASIR-UP interface specification.
		unsafe {
			Self::IPASIR_CONNECT_EXTERNAL_PROPAGATOR(self.ipasir_store().solver_ptr(), c_prop);
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

	fn phase(&mut self, lit: Lit) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_PHASE function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Self::IPASIR_PHASE(self.ipasir_store_mut().solver_ptr(), lit.into());
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

	fn unphase(&mut self, lit: Lit) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_UNPHASE function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Self::IPASIR_UNPHASE(self.ipasir_store_mut().solver_ptr(), lit.into());
		}
	}
}

impl<
		Impl: AccessIpasirStore
			+ IpasirSolverMethods
			+ IpasirLiteralMethods
			+ IpasirFixedAssignmentMethods,
	> PersistentAssignmentNotifier for Impl
where
	Impl::Store: BasicIpasirStorage + IpasirPropagatorStorage,
{
	fn connect_persistent_assignment_listener<L: PersistentAssignmentListener + 'static>(
		&mut self,
		listener: Rc<RefCell<L>>,
	) {
		// Disconnect previous listener (if any)
		self.disconnect_persistent_assignment_listener();

		// Store the propagator and receive the data pointer and callback pointers
		let c_listener = self.ipasir_store_mut().set_persistent_listener(listener);

		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_CONNECT_FIXED_ASSIGNMENT_LISTENER function is expected to abide by
		// the IPASIR-UP interface specification.
		unsafe {
			Self::IPASIR_CONNECT_FIXED_ASSIGNMENT_LISTENER(
				self.ipasir_store_mut().solver_ptr(),
				c_listener,
			);
		}
	}

	fn disconnect_persistent_assignment_listener(&mut self) {
		if self.ipasir_store().has_persistent_assignment_listener() {
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_DISCONNECT_FIXED_ASSIGNMENT_LISTENER function is expected to
			// abide by the IPASIR-UP interface specification.
			unsafe {
				Self::IPASIR_DISCONNECT_FIXED_ASSIGNMENT_LISTENER(self.ipasir_store().solver_ptr());
			}
			self.ipasir_store_mut().reset_persistent_listener();
		}
	}
}

impl IpasirPropagator {
	/// Borrow the connected propagator, stored in the given `cell`, as a
	/// specific type `P`.
	///
	/// This method is unsafe because it requires that the propagator is of type
	/// `P` and the cell is not borrowed. If the propagator is not of type `P`
	/// or if the cell is already borrowed, this method will panic.
	unsafe fn borrow_cell<P>(cell: &Rc<RefCell<dyn Propagator>>) -> RefMut<'_, P> {
		let ptr = Rc::as_ptr(cell) as *const RefCell<P>;
		(&*ptr).borrow_mut()
	}

	/// Borrow the propagator in the `external_propagator` field, as a specific
	/// type `P`.
	///
	/// See [`Self::borrow_cell`] for the safety requirements.
	unsafe fn borrow_propagator_mut<P>(&self) -> RefMut<'_, P> {
		Self::borrow_cell(self.external_propagator.as_ref().unwrap())
	}

	/// Call `f` with the propagator (as a specific type `P`) and a mutable
	/// reference to the reusable `clause` buffer.
	///
	/// Building a reason or external clause needs both at once: the propagator
	/// writes its literals into the buffer through the builder. Scoping the
	/// borrows to `f` keeps the pointer handling of [`Self::borrow_cell`] in a
	/// single place (rather than inlined at each call site) and releases the
	/// propagator borrow before the caller touches `self` again.
	///
	/// See [`Self::borrow_cell`] for the safety requirements.
	unsafe fn with_propagator_and_clause<P, R>(
		&mut self,
		f: impl FnOnce(&mut P, &mut Vec<Lit>) -> R,
	) -> R {
		let mut propagator = Self::borrow_cell::<P>(self.external_propagator.as_ref().unwrap());
		f(&mut propagator, &mut self.clause)
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
			.field("clause", &self.clause)
			.field("explaining", &self.explaining)
			.field("clause_active", &self.clause_active)
			.finish()
	}
}

impl<Impl: IpasirUserPropagationMethods + IpasirLiteralMethods> SolvingActions
	for IpasirSolvingActions<Impl>
{
	fn is_decision(&mut self, lit: Lit) -> bool {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_IS_DECISION function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe { Impl::IPASIR_IS_DECISION(self.ptr, lit.into()) }
	}

	fn new_observed_var(&mut self) -> Var {
		let var = Impl::IPASIR_NEW_VAR(self.ptr, self.vars);
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_ADD_OBSERVED_VAR function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe { Impl::IPASIR_ADD_OBSERVED_VAR(self.ptr, var) };
		Var(NonZeroI32::new(var).unwrap())
	}

	fn phase(&mut self, lit: Lit) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_PHASE function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Impl::IPASIR_PHASE(self.ptr, lit.into());
		}
	}

	fn unphase(&mut self, lit: Lit) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_UNPHASE function is expected to abide by the IPASIR-UP
		// interface specification.
		unsafe {
			Impl::IPASIR_UNPHASE(self.ptr, lit.into());
		}
	}
}

impl<
		Impl: IpasirSolverMethods + IpasirLiteralMethods + IpasirUserPropagationMethods,
		VarStore,
		const LRN: usize,
		const TRM: usize,
	> IpasirStore<Impl, VarStore, LRN, TRM, 1>
{
	unsafe extern "C" fn add_external_clause_lit(store: *mut c_void) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		let prop = store.propagator.some_mut();
		if !prop.clause_active {
			debug_assert!(false, "has_external_clause did not return true");
			return 0;
		}
		match prop.clause.pop() {
			Some(l) => l.0.get(),
			None => {
				prop.clause_active = false;
				0 // End of clause
			}
		}
	}

	unsafe extern "C" fn add_reason_clause_lit<P: Propagator>(
		store: *mut c_void,
		propagated_lit: i32,
	) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		let prop = store.propagator.some_mut();
		let lit = Lit(NonZeroI32::new(propagated_lit).unwrap());
		// A reason and an external clause share `clause` and are never yielded
		// simultaneously.
		debug_assert!(!prop.clause_active);

		// If we are not already yielding `lit`'s reason, make the propagator
		// construct the reason clause.
		if prop.explaining != Some(lit) {
			prop.clause.clear();
			prop.with_propagator_and_clause::<P, _>(|propagator, clause| {
				propagator.explain_propagation(lit, ClauseBuilder::new(clause));
			});
			debug_assert!(
				prop.clause.contains(&lit),
				"the reason clause must contain the propagated literal"
			);
			prop.explaining = Some(lit);
		}

		// Yield the members of the constructed clause, then the end-of-clause `0`.
		match prop.clause.pop() {
			Some(lit) => lit.0.get(),
			None => {
				prop.explaining = None;
				0
			}
		}
	}

	unsafe extern "C" fn check_model<P: Propagator>(
		store: *mut c_void,
		model: *const i32,
		len: usize,
	) -> bool {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		let model: &[Lit] = if len > 0 {
			// SAFETY: `model` points to `len` model literals provided by the solver,
			// each a non-zero `i32`. `Lit` is `#[repr(transparent)]` over
			// `NonZeroI32` (and thus over `i32`), so reinterpreting the non-zero
			// literals as `Lit` is sound.
			unsafe { slice::from_raw_parts(model as *const Lit, len) }
		} else {
			&[]
		};
		let solution = Solution::new(model);
		let vars: *mut VarStore = &mut store.vars;
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: vars as *mut c_void,
			_methods: PhantomData,
		};
		store
			.propagator
			.as_ref()
			.unwrap()
			.borrow_propagator_mut::<P>()
			.check_solution(&mut slv, solution)
	}
	unsafe extern "C" fn decide<P: Propagator>(store: *mut c_void) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		let vars: *mut VarStore = &mut store.vars;
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: vars as *mut c_void,
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
				// Safety: Pointer is a valid (non-null) pointer to the solver, and the
				// IPASIR_FORCE_BACKTRACK function is expected to abide by the IPASIR-UP
				// interface specification.
				unsafe { Impl::IPASIR_FORCE_BACKTRACK(store.ptr, level) }
				0
			}
			SearchDecision::Free => 0,
		}
	}

	unsafe extern "C" fn has_external_clause<P: Propagator>(
		store: *mut c_void,
		is_forgettable: *mut bool,
	) -> bool {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		let vars: *mut VarStore = &mut store.vars;
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: vars as *mut c_void,
			_methods: PhantomData,
		};
		let prop = store.propagator.some_mut();
		// A reason and an external clause share `clause` and are never yielded
		// simultaneously.
		debug_assert!(prop.explaining.is_none());
		debug_assert!(prop.clause.is_empty());
		debug_assert!(!prop.clause_active);
		prop.clause.clear();
		let persistence = prop.with_propagator_and_clause::<P, _>(|propagator, clause| {
			propagator.provide_clause(&mut slv, ClauseBuilder::new(clause))
		});
		if let Some(p) = persistence {
			*is_forgettable = p == ClausePersistence::Forgettable;
			prop.clause_active = true;
			true
		} else {
			prop.clause_active = false;
			false
		}
	}

	unsafe extern "C" fn notify_assignment<P: Propagator>(
		store: *mut c_void,
		lits: *const i32,
		len: usize,
	) {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		if len > 0 {
			// SAFETY: `lits` points to `len` assigned literals provided by the
			// solver, each a non-zero `i32`. `Lit` is `#[repr(transparent)]` over
			// `NonZeroI32` (and thus over `i32`), so reinterpreting the non-zero
			// literals as `Lit` is sound. A `0` from the solver would make an
			// invalid `NonZeroI32` and is undefined behaviour.
			let lits = unsafe { slice::from_raw_parts(lits as *mut Lit, len) };
			store
				.propagator
				.some_ref()
				.borrow_propagator_mut::<P>()
				.notify_assignment(lits);
		};
	}

	unsafe extern "C" fn notify_backtrack<P: Propagator>(
		store: *mut c_void,
		level: usize,
		restart: bool,
	) {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		let prop = store.propagator.some_mut();
		prop.clause.clear();
		prop.explaining = None;
		prop.clause_active = false;
		prop.borrow_propagator_mut::<P>()
			.notify_backtrack(level, restart);
	}

	unsafe extern "C" fn notify_new_decision_level<P: Propagator>(store: *mut c_void) {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		store
			.propagator
			.some_ref()
			.borrow_propagator_mut::<P>()
			.notify_new_decision_level();
	}

	unsafe extern "C" fn notify_persistent_assignment<L: PersistentAssignmentListener>(
		rc: *mut c_void,
		lit: i32,
	) {
		let cell = &mut *(rc as *mut RefCell<L>);
		let lit = Lit(NonZeroI32::new(lit).unwrap());
		let mut listener = cell.borrow_mut();
		listener.notify_persistent_assignment(lit);
	}

	unsafe extern "C" fn propagate<P: Propagator>(store: *mut c_void) -> i32 {
		let store = &mut *(store as *mut IpasirStoreInner<VarStore, LRN, TRM, 1>);
		let vars: *mut VarStore = &mut store.vars;
		let mut slv = IpasirSolvingActions::<Impl> {
			ptr: store.ptr,
			vars: vars as *mut c_void,
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

impl<Impl, VarStore, const LRN: usize, const TRM: usize> IpasirPropagatorStorage
	for IpasirStore<Impl, VarStore, LRN, TRM, 1>
where
	Impl: IpasirSolverMethods + IpasirLiteralMethods + IpasirUserPropagationMethods,
{
	fn has_persistent_assignment_listener(&self) -> bool {
		self.store
			.propagator
			.some_ref()
			.persistent_assignment_listener
			.is_some()
	}

	fn has_propagator(&self) -> bool {
		self.store
			.propagator
			.some_ref()
			.external_propagator
			.is_some()
	}

	fn reset_persistent_listener(&mut self) {
		self.store
			.propagator
			.some_mut()
			.persistent_assignment_listener = None;
	}

	fn reset_propagator(&mut self) {
		let prop_store = self.store.propagator.some_mut();
		prop_store.external_propagator = None;
		prop_store.clause.clear();
		prop_store.explaining = None;
		prop_store.clause_active = false;
	}

	fn set_persistent_listener<L: PersistentAssignmentListener + 'static>(
		&mut self,
		listener: Rc<RefCell<L>>,
	) -> CFixedAssignmentListener {
		// Track the memory of the listener
		self.store
			.propagator
			.some_mut()
			.persistent_assignment_listener = Some(listener);
		// Create the data pointer that the IPASIR UP solver will use for the
		// listener callbacks.
		let listener_ptr: *const RefCell<_> = Rc::as_ptr(
			self.store
				.propagator
				.some_ref()
				.persistent_assignment_listener
				.as_ref()
				.unwrap(),
		);

		// Construct the object with the listener callbacks
		CFixedAssignmentListener {
			data: listener_ptr as *mut c_void,
			notify_fixed_assignment: Self::notify_persistent_assignment::<L>,
		}
	}

	fn set_propagator<P: PropagatorConfig + 'static>(
		&mut self,
		propagator: Rc<RefCell<P>>,
	) -> CExternalPropagator {
		// Track the memory of the listener
		self.store.propagator.some_mut().external_propagator = Some(propagator);
		// Create the data pointer that the IPASIR UP solver will use for all
		// propagator callbacks.
		let store_ptr: *mut _ = &mut *self.store;
		// Construct the object will all callbacks (specific) to the propagator and
		// the specific [`IpasirSolver`] instance.
		CExternalPropagator {
			data: store_ptr as *mut c_void,
			is_lazy: P::CHECK_ONLY,
			are_reasons_forgettable: P::REASON_PERSISTENCE == ClausePersistence::Forgettable,
			notify_assignment: Self::notify_assignment::<P>,
			notify_new_decision_level: Self::notify_new_decision_level::<P>,
			notify_backtrack: Self::notify_backtrack::<P>,
			check_found_model: Self::check_model::<P>,
			decide: Self::decide::<P>,
			propagate: Self::propagate::<P>,
			add_reason_clause_lit: Self::add_reason_clause_lit::<P>,
			has_external_clause: Self::has_external_clause::<P>,
			add_external_clause_lit: Self::add_external_clause_lit,
		}
	}
}
