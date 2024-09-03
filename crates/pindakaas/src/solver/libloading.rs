#[cfg(feature = "ipasir-up")]
use std::collections::VecDeque;
use std::{
	ffi::{c_char, c_int, c_void, CStr},
	num::NonZeroI32,
	ptr,
};

use libloading::{Library, Symbol};

use super::{
	FailedAssumtions, LearnCallback, SlvTermSignal, SolveAssuming, SolveResult, Solver,
	TermCallback, VarFactory,
};
#[cfg(feature = "ipasir-up")]
use super::{Propagator, SolvingActions};
use crate::{ClauseDatabase, ConditionalDatabase, Lit, Result, Valuation, Var};

#[derive(Debug)]
pub struct IpasirLibrary {
	lib: Library,
}

pub type SymResult<'a, S, E = libloading::Error> = std::result::Result<Symbol<'a, S>, E>;

impl IpasirLibrary {
	fn ipasir_signature_sym(&self) -> SymResult<extern "C" fn() -> *const c_char> {
		unsafe { self.lib.get(b"ipasir_signature") }
	}

	fn ipasir_init_sym(&self) -> SymResult<extern "C" fn() -> *mut c_void> {
		unsafe { self.lib.get(b"ipasir_init") }
	}

	fn ipasir_release_sym(&self) -> SymResult<extern "C" fn(*mut c_void)> {
		unsafe { self.lib.get(b"ipasir_release") }
	}

	fn ipasir_add_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		unsafe { self.lib.get(b"ipasir_add") }
	}

	fn ipasir_assume_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32)> {
		unsafe { self.lib.get(b"ipasir_assume") }
	}

	fn ipasir_solve_sym(&self) -> SymResult<extern "C" fn(*mut c_void) -> c_int> {
		unsafe { self.lib.get(b"ipasir_solve") }
	}
	fn ipasir_value_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> i32> {
		unsafe { self.lib.get(b"ipasir_val") }
	}

	fn ipasir_failed_sym(&self) -> SymResult<extern "C" fn(*mut c_void, i32) -> c_int> {
		unsafe { self.lib.get(b"ipasir_failed") }
	}

	fn ipasir_set_terminate_sym(
		&self,
	) -> SymResult<
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	> {
		unsafe { self.lib.get(b"ipasir_set_terminate") }
	}

	fn ipasir_set_learn_sym(
		&self,
	) -> SymResult<
		extern "C" fn(
			*mut c_void,
			*mut c_void,
			c_int,
			Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
		),
	> {
		unsafe { self.lib.get(b"ipasir_set_learn") }
	}

	pub fn signature(&self) -> &str {
		unsafe { CStr::from_ptr((self.ipasir_signature_sym().unwrap())()) }
			.to_str()
			.unwrap()
	}

	pub fn new_solver(&self) -> IpasirSolver<'_> {
		IpasirSolver {
			slv: (self.ipasir_init_sym().unwrap())(),
			vars: VarFactory::default(),
			learn_cb: FFIPointer::default(),
			term_cb: FFIPointer::default(),
			signature_fn: self.ipasir_signature_sym().unwrap(),
			release_fn: self.ipasir_release_sym().unwrap(),
			add_fn: self.ipasir_add_sym().unwrap(),
			assume_fn: self.ipasir_assume_sym().unwrap(),
			solve_fn: self.ipasir_solve_sym().unwrap(),
			value_fn: self.ipasir_value_sym().unwrap(),
			failed_fn: self.ipasir_failed_sym().unwrap(),
			set_terminate_fn: self.ipasir_set_terminate_sym().unwrap(),
			set_learn_fn: self.ipasir_set_learn_sym().unwrap(),
		}
	}
}

impl TryFrom<Library> for IpasirLibrary {
	type Error = libloading::Error;

	fn try_from(lib: Library) -> Result<Self, Self::Error> {
		let lib = IpasirLibrary { lib };
		lib.ipasir_signature_sym()?;
		lib.ipasir_init_sym()?;
		lib.ipasir_release_sym()?;
		lib.ipasir_add_sym()?;
		lib.ipasir_assume_sym()?;
		lib.ipasir_solve_sym()?;
		lib.ipasir_value_sym()?;
		lib.ipasir_failed_sym()?;
		lib.ipasir_set_terminate_sym()?;
		lib.ipasir_set_learn_sym()?;
		Ok(lib)
	}
}

#[derive(Debug)]
pub struct IpasirSolver<'lib> {
	/// The raw pointer to the Intel SAT solver.
	slv: *mut c_void,
	/// The variable factory for this solver.
	vars: VarFactory,

	/// The callback used when a clause is learned.
	learn_cb: FFIPointer,
	/// The callback used to check whether the solver should terminate.
	term_cb: FFIPointer,

	signature_fn: Symbol<'lib, extern "C" fn() -> *const c_char>,
	release_fn: Symbol<'lib, extern "C" fn(*mut c_void)>,
	add_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32)>,
	assume_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32)>,
	solve_fn: Symbol<'lib, extern "C" fn(*mut c_void) -> c_int>,
	value_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> i32>,
	failed_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> c_int>,
	set_terminate_fn: Symbol<
		'lib,
		extern "C" fn(*mut c_void, *mut c_void, Option<unsafe extern "C" fn(*mut c_void) -> c_int>),
	>,
	set_learn_fn: Symbol<
		'lib,
		extern "C" fn(
			*mut c_void,
			*mut c_void,
			c_int,
			Option<unsafe extern "C" fn(*mut c_void, *const i32)>,
		),
	>,
}

impl<'lib> Drop for IpasirSolver<'lib> {
	fn drop(&mut self) {
		// Release the solver.
		(self.release_fn)(self.slv);
	}
}

impl<'lib> ClauseDatabase for IpasirSolver<'lib> {
	fn new_var(&mut self) -> Var {
		self.vars.next().expect("variable pool exhaused")
	}

	fn add_clause<I: IntoIterator<Item = Lit>>(&mut self, clause: I) -> Result {
		let mut added = false;
		for lit in clause.into_iter() {
			(self.add_fn)(self.slv, lit.into());
			added = true;
		}
		if added {
			(self.add_fn)(self.slv, 0);
		}
		Ok(())
	}

	type CondDB = Self;
	fn with_conditions(&mut self, conditions: Vec<Lit>) -> ConditionalDatabase<Self::CondDB> {
		ConditionalDatabase {
			db: self,
			conditions,
		}
	}
}

impl<'lib> Solver for IpasirSolver<'lib> {
	type ValueFn = IpasirSol<'lib>;

	fn signature(&self) -> &str {
		unsafe { CStr::from_ptr((self.signature_fn)()) }
			.to_str()
			.unwrap()
	}

	fn solve<SolCb: FnOnce(&Self::ValueFn)>(&mut self, on_sol: SolCb) -> SolveResult {
		let res = (self.solve_fn)(self.slv);
		match res {
			10 => {
				// 10 -> Sat
				on_sol(&self.sol_obj());
				SolveResult::Sat
			}
			20 => SolveResult::Unsat, // 20 -> Unsat
			_ => {
				debug_assert_eq!(res, 0); // According to spec should be 0, unknown
				SolveResult::Unknown
			}
		}
	}
}

impl<'lib> SolveAssuming for IpasirSolver<'lib> {
	type FailFn = IpasirFailed<'lib>;

	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&<Self as Solver>::ValueFn),
		FailCb: FnOnce(&Self::FailFn),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult {
		for i in assumptions {
			(self.assume_fn)(self.slv, i.into());
		}
		match self.solve(on_sol) {
			SolveResult::Unsat => {
				on_fail(&self.failed_obj());
				SolveResult::Unsat
			}
			r => r,
		}
	}
}

impl<'lib> IpasirSolver<'lib> {
	fn sol_obj(&self) -> IpasirSol<'lib> {
		IpasirSol {
			slv: self.slv,
			value_fn: self.value_fn.clone(),
		}
	}
	fn failed_obj(&self) -> IpasirFailed<'lib> {
		IpasirFailed {
			slv: self.slv,
			failed_fn: self.failed_fn.clone(),
		}
	}
}

#[derive(Debug)]
pub struct IpasirSol<'lib> {
	slv: *mut c_void,
	value_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> i32>,
}

impl Valuation for IpasirSol<'_> {
	fn value(&self, lit: Lit) -> Option<bool> {
		let lit: i32 = lit.into();
		let val = (self.value_fn)(self.slv, lit);
		match val {
			_ if val == lit => Some(true),
			_ if val == -lit => Some(false),
			_ => {
				debug_assert_eq!(val, 0); // zero according to spec, both value are valid
				None
			}
		}
	}
}

#[derive(Debug)]
pub struct IpasirFailed<'lib> {
	slv: *mut c_void,
	failed_fn: Symbol<'lib, extern "C" fn(*mut c_void, i32) -> c_int>,
}

impl FailedAssumtions for IpasirFailed<'_> {
	fn fail(&self, lit: Lit) -> bool {
		let lit: i32 = lit.into();
		let failed = (self.failed_fn)(self.slv, lit);
		failed != 0
	}
}

impl<'lib> TermCallback for IpasirSolver<'lib> {
	fn set_terminate_callback<F: FnMut() -> SlvTermSignal + 'static>(&mut self, cb: Option<F>) {
		if let Some(mut cb) = cb {
			let wrapped_cb = move || -> c_int {
				match cb() {
					SlvTermSignal::Continue => c_int::from(0),
					SlvTermSignal::Terminate => c_int::from(1),
				}
			};
			let trampoline = get_trampoline0(&wrapped_cb);
			self.term_cb = FFIPointer::new(wrapped_cb);
			(self.set_terminate_fn)(self.slv, self.term_cb.get_ptr(), Some(trampoline));
		} else {
			self.term_cb = FFIPointer::default();
			(self.set_terminate_fn)(self.slv, ptr::null_mut(), None);
		}
	}
}

impl<'lib> LearnCallback for IpasirSolver<'lib> {
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + 'static>(
		&mut self,
		cb: Option<F>,
	) {
		const MAX_LEN: std::ffi::c_int = 512;
		if let Some(mut cb) = cb {
			let wrapped_cb = move |clause: *const i32| {
				let mut iter = ExplIter(clause).map(|i: i32| Lit(NonZeroI32::new(i).unwrap()));
				cb(&mut iter)
			};

			let trampoline = get_trampoline1(&wrapped_cb);
			self.learn_cb = FFIPointer::new(wrapped_cb);
			(self.set_learn_fn)(self.slv, self.learn_cb.get_ptr(), MAX_LEN, Some(trampoline));
		} else {
			self.learn_cb = FFIPointer::default();
			(self.set_learn_fn)(self.slv, ptr::null_mut(), MAX_LEN, None);
		}
	}
}
type CB0<R> = unsafe extern "C" fn(*mut c_void) -> R;
unsafe extern "C" fn trampoline0<R, F: FnMut() -> R>(user_data: *mut c_void) -> R {
	let user_data = &mut *(user_data as *mut F);
	user_data()
}
pub(crate) fn get_trampoline0<R, F: FnMut() -> R>(_closure: &F) -> CB0<R> {
	trampoline0::<R, F>
}
type CB1<R, A> = unsafe extern "C" fn(*mut c_void, A) -> R;
unsafe extern "C" fn trampoline1<R, A, F: FnMut(A) -> R>(user_data: *mut c_void, arg1: A) -> R {
	let user_data = &mut *(user_data as *mut F);
	user_data(arg1)
}
pub(crate) fn get_trampoline1<R, A, F: FnMut(A) -> R>(_closure: &F) -> CB1<R, A> {
	trampoline1::<R, A, F>
}

/// Iterator over the elements of a null-terminated i32 array
#[derive(Debug, Clone, Copy)]
pub(crate) struct ExplIter(pub(crate) *const i32);
impl Iterator for ExplIter {
	type Item = i32;
	#[inline]
	fn next(&mut self) -> Option<Self::Item> {
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

#[cfg(feature = "ipasir-up")]
pub(crate) struct IpasirPropStore<P, A> {
	/// Rust Propagator
	pub(crate) prop: P,
	/// IPASIR solver pointer
	pub(crate) slv: A,
	/// Propagation queue
	pub(crate) pqueue: VecDeque<crate::Lit>,
	/// Reason clause queue
	pub(crate) rqueue: VecDeque<crate::Lit>,
	pub(crate) explaining: Option<Lit>,
	/// External clause queue
	pub(crate) cqueue: Option<VecDeque<crate::Lit>>,
}

#[cfg(feature = "ipasir-up")]
impl<P, A> IpasirPropStore<P, A> {
	pub(crate) fn new(prop: P, slv: A) -> Self {
		Self {
			prop,
			slv,
			pqueue: VecDeque::default(),
			rqueue: VecDeque::default(),
			explaining: None,
			cqueue: None,
		}
	}
}

// --- Helpers for C interface ---
pub(crate) fn get_drop_fn<T>(_: &T) -> fn(*mut std::ffi::c_void) {
	|ptr: *mut std::ffi::c_void| {
		let b = unsafe { Box::<T>::from_raw(ptr as *mut T) };
		drop(b);
	}
}

#[derive(Debug, PartialEq)]
pub(crate) struct FFIPointer {
	pub(crate) ptr: *mut std::ffi::c_void,
	pub(crate) drop_fn: fn(*mut std::ffi::c_void),
}

impl FFIPointer {
	pub(crate) fn new<T: 'static>(obj: T) -> Self {
		let drop_fn = get_drop_fn(&obj);
		let ptr = Box::leak(Box::new(obj)) as *mut _ as *mut std::ffi::c_void;
		Self { ptr, drop_fn }
	}

	/// Get the FFI pointer to the contained object
	///
	/// # WARNING
	/// This pointer is only valid until the FFIPointer object is dropped.
	pub(crate) fn get_ptr(&self) -> *mut std::ffi::c_void {
		self.ptr
	}
}

impl Default for FFIPointer {
	fn default() -> Self {
		Self {
			ptr: std::ptr::null_mut(),
			drop_fn: |_: *mut std::ffi::c_void| {},
		}
	}
}

impl Drop for FFIPointer {
	fn drop(&mut self) {
		if !self.ptr.is_null() {
			(self.drop_fn)(self.ptr);
		}
	}
}

#[cfg(feature = "ipasir-up")]
pub(crate) struct PropagatorPointer {
	ptr: FFIPointer,
	pub(crate) access_prop: fn(*mut c_void) -> *mut dyn std::any::Any,
}

#[cfg(feature = "ipasir-up")]
impl PropagatorPointer {
	pub(crate) fn new<P, A>(prop: P, slv: A) -> Self
	where
		P: Propagator + 'static,
		A: SolvingActions + 'static,
	{
		// Construct wrapping structures
		let store = IpasirPropStore::new(prop, slv);
		let prop = FFIPointer::new(store);
		let access_prop = |x: *mut std::ffi::c_void| -> *mut dyn std::any::Any {
			let store =
				unsafe { &mut *(x as *mut crate::solver::libloading::IpasirPropStore<P, A>) };
			(&mut store.prop) as *mut dyn std::any::Any
		};
		Self {
			ptr: prop,
			access_prop,
		}
	}

	pub(crate) fn get_raw_ptr(&self) -> *mut std::ffi::c_void {
		self.ptr.get_ptr()
	}

	pub(crate) unsafe fn access_propagator<P: 'static>(&self) -> Option<&P> {
		(*(self.access_prop)(self.get_raw_ptr())).downcast_ref::<P>()
	}

	pub(crate) unsafe fn access_propagator_mut<P: 'static>(&self) -> Option<&mut P> {
		(*(self.access_prop)(self.get_raw_ptr())).downcast_mut::<P>()
	}
}

// --- Callback functions for C propagator interface ---

#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_notify_assignment_cb<P: Propagator, A>(
	state: *mut c_void,
	lit: i32,
	is_fixed: bool,
) {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let lit = crate::Lit(std::num::NonZeroI32::new(lit).unwrap());
	prop.prop.notify_assignment(lit, is_fixed)
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_notify_new_decision_level_cb<P: Propagator, A>(
	state: *mut c_void,
) {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	prop.prop.notify_new_decision_level()
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_notify_backtrack_cb<P: Propagator, A>(
	state: *mut c_void,
	level: usize,
	restart: bool,
) {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	prop.pqueue.clear();
	prop.explaining = None;
	prop.rqueue.clear();
	prop.cqueue = None;
	prop.prop.notify_backtrack(level, restart);
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_check_model_cb<P: Propagator, A: SolvingActions>(
	state: *mut c_void,
	model: *const i32,
	len: usize,
) -> bool {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let sol = if len > 0 {
		std::slice::from_raw_parts(model, len)
	} else {
		&[]
	};
	let sol: std::collections::HashMap<Var, bool> = sol
		.iter()
		.map(|&i| (Var(NonZeroI32::new(i.abs()).unwrap()), i >= 0))
		.collect();
	let value = |l: Lit| sol.get(&l.var()).copied();
	prop.prop.check_model(&mut prop.slv, &value)
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_decide_cb<P: Propagator, A: SolvingActions>(
	state: *mut c_void,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let slv = &mut prop.slv;
	if let Some(l) = prop.prop.decide(slv) {
		l.0.into()
	} else {
		0
	}
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_propagate_cb<P: Propagator, A: SolvingActions>(
	state: *mut c_void,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	if prop.pqueue.is_empty() {
		let slv = &mut prop.slv;
		prop.pqueue = prop.prop.propagate(slv).into()
	}
	if let Some(l) = prop.pqueue.pop_front() {
		l.0.into()
	} else {
		0 // No propagation
	}
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_add_reason_clause_lit_cb<
	P: Propagator,
	A: SolvingActions,
>(
	state: *mut c_void,
	propagated_lit: i32,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	let lit = crate::Lit(std::num::NonZeroI32::new(propagated_lit).unwrap());
	debug_assert!(prop.explaining.is_none() || prop.explaining == Some(lit));
	// TODO: Can this be prop.explaining.is_none()?
	if prop.explaining != Some(lit) {
		prop.rqueue = prop.prop.add_reason_clause(lit).into();
		prop.explaining = Some(lit);
	}
	if let Some(l) = prop.rqueue.pop_front() {
		l.0.into()
	} else {
		// End of explanation
		prop.explaining = None;
		0
	}
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_has_external_clause_cb<P: Propagator, A: SolvingActions>(
	state: *mut c_void,
) -> bool {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	prop.cqueue = prop.prop.add_external_clause(&mut prop.slv).map(Vec::into);
	prop.cqueue.is_some()
}
#[cfg(feature = "ipasir-up")]
pub(crate) unsafe extern "C" fn ipasir_add_external_clause_lit_cb<
	P: Propagator,
	A: SolvingActions,
>(
	state: *mut c_void,
) -> i32 {
	let prop = &mut *(state as *mut IpasirPropStore<P, A>);
	if prop.cqueue.is_none() {
		debug_assert!(false);
		// This function shouldn't be called when "has_clause" returned false.
		prop.cqueue = prop.prop.add_external_clause(&mut prop.slv).map(Vec::into);
	}
	if let Some(queue) = &mut prop.cqueue {
		if let Some(l) = queue.pop_front() {
			l.0.get()
		} else {
			prop.cqueue = None;
			0 // End of clause
		}
	} else {
		debug_assert!(false);
		// Even after re-assessing, no additional clause was found. Just return 0
		0
	}
}
