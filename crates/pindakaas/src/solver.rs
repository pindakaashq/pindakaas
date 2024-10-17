#[cfg(any(feature = "cadical", test))]
pub mod cadical;
#[cfg(feature = "intel-sat")]
pub mod intel_sat;
#[cfg(feature = "kissat")]
pub mod kissat;
#[cfg(feature = "libloading")]
pub mod libloading;
#[cfg(feature = "external-propagation")]
pub mod propagation;
#[cfg(feature = "splr")]
pub mod splr;

use std::{ffi::c_void, num::NonZeroI32, ptr};

use crate::{ClauseDatabase, Lit, Valuation, Var, VarRange};

type CB0<R> = unsafe extern "C" fn(*mut c_void) -> R;
type CB1<R, A> = unsafe extern "C" fn(*mut c_void, A) -> R;

#[derive(Debug, Clone, Copy)]
/// Iterator over the elements of a null-terminated i32 array
struct ExplIter(*const i32);

#[derive(Debug, PartialEq)]
struct FFIPointer {
	ptr: *mut c_void,
	drop_fn: fn(*mut c_void),
}

/// Trait implemented by the object given to the callback on detecting failure
pub trait FailedAssumtions {
	/// Check if the given assumption literal was used to prove the unsatisfiability
	/// of the formula under the assumptions used for the last SAT search.
	///
	/// Note that for literals 'lit' which are not assumption literals, the behavior
	/// of is not specified.
	fn fail(&self, lit: Lit) -> bool;
}

pub trait LearnCallback: Solver {
	/// Set a callback function used to extract learned clauses up to a given
	/// length from the solver.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = Lit>) + 'static>(
		&mut self,
		cb: Option<F>,
	);
}

/// Allow request for sequential ranges of variables.
pub trait NextVarRange {
	/// Request the next sequential range of variables.
	///
	/// The method is can return [`None`] if the range of the requested [`size`] is not
	/// available.
	fn next_var_range(&mut self, size: usize) -> Option<VarRange>;
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum SlvTermSignal {
	Continue,
	Terminate,
}

pub trait SolveAssuming: Solver {
	type FailFn: FailedAssumtions;

	/// Solve the formula with specified clauses under the given assumptions.
	///
	/// If the search is interrupted (see [`set_terminate_callback`]) the function
	/// returns unknown
	fn solve_assuming<
		I: IntoIterator<Item = Lit>,
		SolCb: FnOnce(&Self::ValueFn),
		FailCb: FnOnce(&Self::FailFn),
	>(
		&mut self,
		assumptions: I,
		on_sol: SolCb,
		on_fail: FailCb,
	) -> SolveResult;
}

#[derive(PartialEq, Eq, Clone, Copy, Hash, Debug)]
pub enum SolveResult {
	Sat,
	Unsat,
	Unknown,
}

pub trait Solver: ClauseDatabase {
	type ValueFn: Valuation;
	/// Return the name and the version of SAT solver.
	fn signature(&self) -> &str;

	/// Solve the formula with specified clauses.
	///
	/// If the search is interrupted (see [`set_terminate_callback`]) the function
	/// returns unknown
	fn solve<SolCb: FnOnce(&Self::ValueFn)>(&mut self, on_sol: SolCb) -> SolveResult;
}

pub trait TermCallback: Solver {
	/// Set a callback function used to indicate a termination requirement to the
	/// solver.
	///
	/// The solver will periodically call this function and check its return value
	/// during the search. Subsequent calls to this method override the previously
	/// set callback function.
	///
	/// # Warning
	///
	/// Subsequent calls to this method override the previously set
	/// callback function.
	fn set_terminate_callback<F: FnMut() -> SlvTermSignal + 'static>(&mut self, cb: Option<F>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarFactory {
	pub(crate) next_var: Option<Var>,
}

fn get_drop_fn<T>(_: &T) -> fn(*mut c_void) {
	|ptr: *mut c_void| {
		// SAFETY: This drop function assumes that the pointer was created by Box::leak
		let b = unsafe { Box::<T>::from_raw(ptr as *mut T) };
		drop(b);
	}
}

fn get_trampoline0<R, F: FnMut() -> R>(_closure: &F) -> CB0<R> {
	trampoline0::<R, F>
}

fn get_trampoline1<R, A, F: FnMut(A) -> R>(_closure: &F) -> CB1<R, A> {
	trampoline1::<R, A, F>
}

unsafe extern "C" fn trampoline0<R, F: FnMut() -> R>(user_data: *mut c_void) -> R {
	let user_data = &mut *(user_data as *mut F);
	user_data()
}

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

impl FFIPointer {
	/// Get the FFI pointer to the contained object
	///
	/// # WARNING
	/// This pointer is only valid until the FFIPointer object is dropped.
	fn get_ptr(&self) -> *mut c_void {
		self.ptr
	}
	fn new<T: 'static>(obj: T) -> Self {
		let drop_fn = get_drop_fn(&obj);
		let ptr: *mut T = Box::leak(Box::new(obj));
		Self {
			ptr: ptr as *mut c_void,
			drop_fn,
		}
	}
}

impl Default for FFIPointer {
	fn default() -> Self {
		Self {
			ptr: ptr::null_mut(),
			drop_fn: |_: *mut c_void| {},
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

impl VarFactory {
	const MAX_VARS: usize = NonZeroI32::MAX.get() as usize;

	pub fn emited_vars(&self) -> usize {
		if let Some(x) = self.next_var {
			x.0.get() as usize - 1
		} else {
			Self::MAX_VARS
		}
	}
}

impl Default for VarFactory {
	fn default() -> Self {
		Self {
			next_var: Some(Var(NonZeroI32::new(1).unwrap())),
		}
	}
}

impl Iterator for VarFactory {
	type Item = Var;

	fn next(&mut self) -> Option<Self::Item> {
		let var = self.next_var;
		if let Some(var) = var {
			self.next_var = var.next_var();
		}
		var
	}
}

impl NextVarRange for VarFactory {
	fn next_var_range(&mut self, size: usize) -> Option<VarRange> {
		let start = self.next_var?;
		match size {
			0 => Some(VarRange::new(
				Var(NonZeroI32::new(2).unwrap()),
				Var(NonZeroI32::new(1).unwrap()),
			)),
			1 => {
				self.next_var = start.next_var();
				Some(VarRange::new(start, start))
			}
			_ if size > NonZeroI32::MAX.get() as usize => None,
			_ => {
				// Size is reduced by 1 since it includes self.next_var
				let size = NonZeroI32::new((size - 1) as i32).unwrap();
				if let Some(end) = start.checked_add(size) {
					// Set self.next_var to one after end
					self.next_var = end.next_var();
					Some(VarRange::new(start, end))
				} else {
					None
				}
			}
		}
	}
}
