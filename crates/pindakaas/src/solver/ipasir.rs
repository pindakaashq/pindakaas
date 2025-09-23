#[cfg(feature = "external-propagation")]
pub(crate) mod user_propagation;

use std::{
	ffi::{c_int, c_void},
	fmt,
	marker::PhantomData,
	num::NonZeroI32,
	ptr,
};

use crate::{
	helpers::opt_field::OptField,
	solver::{
		Assumptions, FailedAssumptions, LearnCallback, SolveResult, Solver, TermSignal,
		TerminateCallback, VarFactory,
	},
	ClauseDatabase, Lit, Result, Unsatisfiable, Valuation, VarRange,
};

/// Helper trait implemented by IPASIR solvers to access the underlying
/// [`IpasirStore`].
pub(crate) trait AccessIpasirStore {
	/// The type of [`IpasirStore`] used by the IPASIR solver.
	type Store;

	/// Access [`Self::Store`].
	fn ipasir_store(&self) -> &Self::Store;

	/// Mutable access [`Self::Store`].
	fn ipasir_store_mut(&mut self) -> &mut Self::Store;
}

/// Helper trait that allows abstraction over all different generic attributes
/// of [`IpasirStore`].
pub(crate) trait BasicIpasirStorage {
	/// Access the raw pointer of the IPASIR solver.
	fn solver_ptr(&self) -> *mut c_void;

	/// Access the [`VarFactory`].
	fn vars(&self) -> &VarFactory;

	/// Mutable access to the [`VarFactory`].
	fn vars_mut(&mut self) -> &mut VarFactory;
}

/// Generic callback function type used by [`get_trampoline0`].
type CB0<R> = unsafe extern "C" fn(*mut c_void) -> R;

/// Generic callback function type used by [`get_trampoline1`].
type CB1<R, A> = unsafe extern "C" fn(*mut c_void, A) -> R;

#[derive(Debug, Clone, Copy)]
/// Iterator over the elements of a null-terminated i32 array
pub(crate) struct ExplIter(pub(crate) *const i32);

/// Trait to be implemented by IPASIR solvers that support assumptions.
///
/// If a type implements this trait and [`AccessIpasirSolver`], then
/// [`SolveAssuming`] is implemented automatically.
pub(crate) trait IpasirAssumptionMethods: IpasirSolverMethods {
	const IPASIR_ASSUME: unsafe extern "C" fn(slv: *mut c_void, lit: i32);
	const IPASIR_FAILED: unsafe extern "C" fn(slv: *mut c_void, lit: i32) -> c_int;
}

#[derive(Debug)]
/// Object that allows querying which assumptions were responsible for the
/// unsatisfiability of the formula for a given IPASIR solver.
pub struct IpasirFailedAssumptions<Impl: IpasirSolverMethods> {
	ptr: *mut c_void,
	_methods: PhantomData<Impl>,
}

/// Trait implemented by IPASIR solvers that support a callback used when a
/// clause is learned.
///
/// When a type implements this trait and [`AccessIpasirSolver`] yielding a
/// [`IpasirStore`] with `LRN = 1`, then [`LearnCallback`] is implemented
/// automatically.
pub(crate) trait IpasirLearnCallbackMethod {
	const IPASIR_SET_LEARN_CALLBACK: unsafe extern "C" fn(
		*mut c_void,
		*mut c_void,
		c_int,
		Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
	);
}

/// The type for a callback function that can be used by IPASIR solver when
/// learning new clauses.
pub(crate) type IpasirLearnCb = Box<dyn FnMut(*const i32)>;

/// Trait that must be implemented by all IPASIR solvers, providing basic
/// functionality of initilization, instantiation, and solving.
///
/// If a type implements this trait and [`AccessIpasirSolver`], then
/// [`Solver`] is implemented automatically.
pub trait IpasirSolverMethods {
	const IPASIR_INIT: unsafe extern "C" fn() -> *mut c_void;
	const IPASIR_RELEASE: unsafe extern "C" fn(slv: *mut c_void);
	const IPASIR_ADD: unsafe extern "C" fn(slv: *mut c_void, lit_or_zero: i32);
	const IPASIR_SOLVE: unsafe extern "C" fn(slv: *mut c_void) -> c_int;
	const IPASIR_VAL: unsafe extern "C" fn(slv: *mut c_void, lit: i32) -> i32;
}

/// Internal structure used to capture all necessary data for an IPASIR solver.
///
/// Depending on the capabilities of the solver, the following generics can be
/// used:
/// - `LRN`: Set to 1 if the solver supports a callback for learned clauses and
///   implement [`IpasirLearnCallbackMethod`]. Set to 0 otherwise.
/// - `TRM`: Set to 1 if the solver supports a callback to check whether to
///   terminate the solving process, and implement
///   [`IpasirTerminateCallbackMethod`]. Set to 0 otherwise.
/// - `UP`: Set to 1 if the solver supports the IPASIR-UP interface for external
///   propagation, and implement [`IpasirUserPropagationMethods`]. Set to 0
///   otherwise.
pub(crate) struct IpasirStore<
	Impl: IpasirSolverMethods,
	const LRN: usize,
	const TRM: usize,
	const UP: usize,
> {
	/// Wrapped inner storage to ensure stable heap allocations for callbacks.
	pub(crate) store: Box<IpasirStoreInner<LRN, TRM, UP>>,
	/// Phantom data to allow the usage of `Impl` type, which must implement the
	/// different solver methods.
	pub(crate) _methods: PhantomData<Impl>,
}

/// Inner storage for [`IpasirStore`] to allow unmoved heap allocation using
/// [`Box`].
pub(crate) struct IpasirStoreInner<const LRN: usize, const TRM: usize, const UP: usize> {
	/// The raw pointer to the IPASIRs solver.
	pub(crate) ptr: *mut c_void,
	/// The variable factory for the solver.
	pub(crate) vars: VarFactory,
	/// The callback used when a clause is learned.
	///
	/// This attribute ensures that the callback is correctly dropped when the
	/// [`IpasirSolver`] is dropped, but is already known to the
	/// [`IpasirSolver`] by pointer.
	pub(crate) learn_cb: OptField<LRN, Option<IpasirLearnCb>>,
	/// The callback used to check whether the solver should terminate.
	///
	/// This attribute ensures that the callback is correctly dropped when the
	/// [`IpasirSolver`] is dropped, but is already known to the
	/// [`IpasirSolver`] by pointer.
	pub(crate) term_cb: OptField<TRM, Option<IpasirTerminationCb>>,
	#[cfg(feature = "external-propagation")]
	/// Data structures used for the IPASIR-UP external propagator interface.
	pub(crate) propagator: OptField<UP, user_propagation::IpasirPropagator>,
	#[cfg(not(feature = "external-propagation"))]
	/// Zero-sized member to allow `UP` generic member when not using the
	/// `external-propagation` feature.
	pub(crate) _propagator: PhantomData<[(); UP]>,
}
/// Trait implemented by IPASIR solvers that support a callback to check whether
/// to terminate.
///
/// When a type implements this trait and [`AccessIpasirSolver`] yielding a
/// [`IpasirStore`] with `TRM = 1`, then [`TerminateCallback`] is implemented
/// automatically.
pub(crate) trait IpasirTermCallbackMethod {
	const IPASIR_SET_TERMINATE_CALLBACK: unsafe extern "C" fn(
		*mut c_void,
		*mut c_void,
		Option<unsafe extern "C" fn(*mut c_void) -> c_int>,
	);
}

/// The type for a callback function that can be used by IPASIR solver to check
/// whether it should terminate.
pub(crate) type IpasirTerminationCb = Box<dyn FnMut() -> c_int>;

#[derive(Debug)]
/// Object that can be queried about the values that each variable has been
/// assigned in the solution yielded by an IPASIR solver.
pub struct IpasirValuation<Impl: IpasirSolverMethods> {
	ptr: *mut c_void,
	_methods: PhantomData<Impl>,
}

/// Helper trait that allows abstraction over different [`IpasirStore`] generics
/// as long as `LRN` is set to 1.
trait LearnCallbackIpasirStorage {
	/// Provide access to the storage for the learn callback.
	fn learn_callback(&mut self) -> &mut Option<IpasirLearnCb>;
}

/// Helper trait that allows abstraction over different [`IpasirStore`] generics
/// as long as `TRM` is set to 1.
trait TerminationCallbackIpasirStorage {
	/// Provide access to the storage for the termination callback.
	fn termination_callback(&mut self) -> &mut Option<IpasirTerminationCb>;
}

/// Function used to split a closure with no arguments into a thin data pointer
/// and a thin function pointer.
pub(crate) fn get_trampoline0<R, F: FnMut() -> R>(closure: &mut F) -> (*mut c_void, CB0<R>) {
	let ptr: *mut F = closure;
	(ptr as *mut c_void, trampoline0::<R, F>)
}
/// Function used to split a closure with a single arguments into a thin data
/// pointer and a thin function pointer.
pub(crate) fn get_trampoline1<R, A, F: FnMut(A) -> R>(closure: &mut F) -> (*mut c_void, CB1<R, A>) {
	let ptr: *mut F = closure;
	(ptr as *mut c_void, trampoline1::<R, A, F>)
}

/// Generic function yielded as a pointer by [`get_trampoline0`].
unsafe extern "C" fn trampoline0<R, F: FnMut() -> R>(user_data: *mut c_void) -> R {
	let user_data = &mut *(user_data as *mut F);
	user_data()
}
/// Generic function yielded as a pointer by [`get_trampoline1`].
unsafe extern "C" fn trampoline1<R, A, F: FnMut(A) -> R>(user_data: *mut c_void, arg1: A) -> R {
	let user_data = &mut *(user_data as *mut F);
	user_data(arg1)
}

impl Iterator for ExplIter {
	type Item = i32;

	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
		// SAFETY: ExplIter is assumed to be constructed using a valid pointer to an
		// correctly aligned and null-terminated array of i32.
		unsafe {
			if *self.0 == 0 {
				None
			} else {
				let ptr = self.0;
				self.0 = ptr.offset(1);
				Some(*ptr)
			}
		}
	}
}

impl<Impl: AccessIpasirStore + IpasirAssumptionMethods> Assumptions for Impl
where
	Impl::Store: BasicIpasirStorage,
{
	fn solve_assuming<I: IntoIterator<Item = Lit>>(
		&mut self,
		assumptions: I,
	) -> SolveResult<impl Valuation + '_, impl FailedAssumptions + '_> {
		for i in assumptions {
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_ASSUME function is expected to abide by the
			// IPASIR interface specification.
			unsafe {
				Self::IPASIR_ASSUME(self.ipasir_store().solver_ptr(), i.into());
			}
		}
		self.solve()
	}
}

impl<Impl: AccessIpasirStore + IpasirSolverMethods> ClauseDatabase for Impl
where
	Impl::Store: BasicIpasirStorage,
{
	fn add_clause_from_slice(&mut self, clause: &[Lit]) -> Result {
		for &lit in clause {
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_ADD function is expected to abide by the IPASIR interface
			// specification.
			unsafe { Self::IPASIR_ADD(self.ipasir_store().solver_ptr(), lit.into()) };
		}
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_ADD function is expected to abide by the IPASIR interface
		// specification.
		unsafe { Self::IPASIR_ADD(self.ipasir_store().solver_ptr(), 0) };
		if clause.is_empty() {
			Err(Unsatisfiable)
		} else {
			Ok(())
		}
	}

	fn new_var_range(&mut self, len: usize) -> VarRange {
		self.ipasir_store_mut().vars_mut().next_var_range(len)
	}
}

impl<Impl: AccessIpasirStore + IpasirSolverMethods + IpasirLearnCallbackMethod> LearnCallback
	for Impl
where
	Impl::Store: BasicIpasirStorage + LearnCallbackIpasirStorage,
{
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		const MAX_LEN: c_int = 512;

		if let Some(mut cb) = cb {
			let mut wrapped_cb = Box::new(move |clause: *const i32| {
				let mut iter = ExplIter(clause).map(|i: i32| Lit(NonZeroI32::new(i).unwrap()));
				cb(&mut iter);
			});
			let (data_ptr, fn_ptr) = get_trampoline1(wrapped_cb.as_mut());
			*self.ipasir_store_mut().learn_callback() = Some(wrapped_cb);
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_SET_LEARN_CALLBACK function is expected to abide by the IPASIR
			// interface specification.
			unsafe {
				Self::IPASIR_SET_LEARN_CALLBACK(
					self.ipasir_store().solver_ptr(),
					data_ptr,
					MAX_LEN,
					Some(fn_ptr),
				);
			}
		} else {
			*self.ipasir_store_mut().learn_callback() = None;
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_SET_LEARN_CALLBACK function is expected to abide by the IPASIR
			// interface specification.
			unsafe {
				Self::IPASIR_SET_LEARN_CALLBACK(
					self.ipasir_store().solver_ptr(),
					ptr::null_mut(),
					MAX_LEN,
					None,
				);
			}
		}
	}
}

impl<Impl: AccessIpasirStore + IpasirSolverMethods> Solver for Impl
where
	Impl::Store: BasicIpasirStorage,
{
	#[expect(
		refining_impl_trait,
		reason = "more specific type used by solve_assuming when assumptions are possible"
	)]
	fn solve(&mut self) -> SolveResult<IpasirValuation<Impl>, IpasirFailedAssumptions<Impl>> {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_SOLVE function is expected to abide by the
		// IPASIR interface specification.
		let res = unsafe { Self::IPASIR_SOLVE(self.ipasir_store().solver_ptr()) };
		match res {
			10 => {
				// 10 -> Sat
				SolveResult::Satisfied(IpasirValuation::<Impl> {
					ptr: self.ipasir_store().solver_ptr(),
					_methods: PhantomData,
				})
			}
			20 => {
				// 20 -> Unsat
				SolveResult::Unsatisfiable(IpasirFailedAssumptions::<Impl> {
					ptr: self.ipasir_store().solver_ptr(),
					_methods: PhantomData,
				})
			}
			_ => {
				debug_assert_eq!(res, 0); // According to spec should be 0, unknown
				SolveResult::Unknown
			}
		}
	}
}

impl<Impl: AccessIpasirStore + IpasirSolverMethods + IpasirTermCallbackMethod> TerminateCallback
	for Impl
where
	Impl::Store: BasicIpasirStorage + TerminationCallbackIpasirStorage,
{
	fn set_terminate_callback<F: FnMut() -> TermSignal + 'static>(&mut self, cb: Option<F>) {
		if let Some(mut cb) = cb {
			let mut wrapped_cb = Box::new(move || -> c_int {
				match cb() {
					TermSignal::Continue => c_int::from(0),
					TermSignal::Terminate => c_int::from(1),
				}
			});
			let (data_ptr, fn_ptr) = get_trampoline0(wrapped_cb.as_mut());
			*self.ipasir_store_mut().termination_callback() = Some(wrapped_cb);
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_SET_TERMINATE_CALLBACK function is expected to abide by the
			// IPASIR interface specification.
			unsafe {
				Self::IPASIR_SET_TERMINATE_CALLBACK(
					self.ipasir_store().solver_ptr(),
					data_ptr,
					Some(fn_ptr),
				);
			}
		} else {
			*self.ipasir_store_mut().termination_callback() = None;
			// Safety: Pointer is a valid (non-null) pointer to the solver, and the
			// IPASIR_SET_TERMINATE_CALLBACK function is expected to abide by the
			// IPASIR interface specification.
			unsafe {
				Self::IPASIR_SET_TERMINATE_CALLBACK(
					self.ipasir_store().solver_ptr(),
					ptr::null_mut(),
					None,
				);
			}
		}
	}
}

impl<Impl: IpasirAssumptionMethods> FailedAssumptions for IpasirFailedAssumptions<Impl> {
	fn fail(&self, lit: Lit) -> bool {
		let lit: i32 = lit.into();
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_FAILED function is expected to abide by the IPASIR interface
		// specification.
		let failed = unsafe { Impl::IPASIR_FAILED(self.ptr, lit) };
		failed != 0
	}
}

impl<Impl: IpasirSolverMethods, const LRN: usize, const TRM: usize, const UP: usize>
	BasicIpasirStorage for IpasirStore<Impl, LRN, TRM, UP>
{
	fn solver_ptr(&self) -> *mut c_void {
		self.store.ptr
	}

	fn vars(&self) -> &VarFactory {
		&self.store.vars
	}

	fn vars_mut(&mut self) -> &mut VarFactory {
		&mut self.store.vars
	}
}

impl<Impl: IpasirSolverMethods, const LRN: usize, const TRM: usize, const UP: usize> Default
	for IpasirStore<Impl, LRN, TRM, UP>
{
	fn default() -> Self {
		// Safety: The IPASIR_INIT function is expected to abide by the IPASIR
		// interface specification and return a valid (non-null) pointer to the
		// solver.
		let p = unsafe { Impl::IPASIR_INIT() };
		debug_assert_ne!(p, ptr::null_mut());
		Self {
			store: Box::new(IpasirStoreInner {
				ptr: p,
				vars: VarFactory::default(),
				learn_cb: OptField::default(),
				term_cb: OptField::default(),
				#[cfg(feature = "external-propagation")]
				propagator: OptField::default(),
				#[cfg(not(feature = "external-propagation"))]
				_propagator: PhantomData,
			}),
			_methods: PhantomData,
		}
	}
}

impl<Impl: IpasirSolverMethods, const LRN: usize, const TRM: usize, const UP: usize> Drop
	for IpasirStore<Impl, LRN, TRM, UP>
{
	fn drop(&mut self) {
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_RELEASE function is expected to abide by the IPASIR interface
		// specification.
		unsafe { Impl::IPASIR_RELEASE(self.store.ptr) };
	}
}

impl<Impl: IpasirSolverMethods, const TRM: usize, const UP: usize> LearnCallbackIpasirStorage
	for IpasirStore<Impl, 1, TRM, UP>
{
	fn learn_callback(&mut self) -> &mut Option<IpasirLearnCb> {
		self.store.learn_cb.some_mut()
	}
}

impl<Impl: IpasirSolverMethods, const LRN: usize, const UP: usize> TerminationCallbackIpasirStorage
	for IpasirStore<Impl, LRN, 1, UP>
{
	fn termination_callback(&mut self) -> &mut Option<IpasirTerminationCb> {
		self.store.term_cb.some_mut()
	}
}

impl<Impl: IpasirSolverMethods, const LRN: usize, const TRM: usize, const UP: usize> fmt::Debug
	for IpasirStore<Impl, LRN, TRM, UP>
{
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let mut builder = f.debug_struct("IpasirSolver");
		let _ = builder
			.field("ptr", &self.store.ptr)
			.field("vars", &self.store.vars);
		if let Some(lrn) = self.store.learn_cb.as_ref() {
			let _ = builder.field(
				"learn_cb",
				&lrn.as_ref().map(|x| {
					let x: *const _ = x.as_ref();
					x as *const c_void
				}),
			);
		}
		if let Some(trm) = self.store.term_cb.as_ref() {
			let _ = builder.field(
				"term_cb",
				&trm.as_ref().map(|x| {
					let x: *const _ = x.as_ref();
					x as *const c_void
				}),
			);
		}
		#[cfg(feature = "external-propagation")]
		if let Some(propagator) = self.store.propagator.as_ref() {
			let _ = builder.field("propagator", &propagator);
		}
		builder.finish()
	}
}

// Safety: No one besides us has the raw solver pointer, so we can safely
// transfer the solver to another thread.
unsafe impl<const LRN: usize, const TRM: usize> Send for IpasirStoreInner<LRN, TRM, 0> {}

#[cfg(not(feature = "external-propagation"))]
// Safety: No one besides us has the raw solver pointer, so we can safely
// transfer the solver to another thread.
unsafe impl<const LRN: usize, const TRM: usize> Send for IpasirStoreInner<LRN, TRM, 1> {}

impl<Impl: IpasirSolverMethods> Valuation for IpasirValuation<Impl> {
	fn value(&self, lit: Lit) -> bool {
		let var: i32 = lit.var().into();
		// WARN: Always ask about variable (positive) literal, otherwise solvers
		// sometimes seem incorrect
		//
		// Safety: Pointer is a valid (non-null) pointer to the solver, and the
		// IPASIR_VAL function is expected to abide by the IPASIR interface
		// specification.
		let ret = unsafe { Impl::IPASIR_VAL(self.ptr, var) };
		match ret {
			_ if ret == var => !lit.is_negated(),
			_ if ret == -var => lit.is_negated(),
			_ => {
				debug_assert_eq!(ret, 0); // zero according to spec, both value are valid
				false
			}
		}
	}
}
