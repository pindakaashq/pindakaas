use darling::FromDeriveInput;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Ident};

#[derive(FromDeriveInput)]
#[darling(attributes(ipasir))]
struct IpasirOpts {
	krate: Ident,
	#[darling(default)]
	ptr: Option<Ident>,
	#[darling(default)]
	vars: Option<Ident>,
	#[darling(default)]
	assumptions: bool,
	#[darling(default)]
	learn_callback: bool,
	#[darling(default)]
	term_callback: bool,
}

#[proc_macro_derive(IpasirSolver, attributes(ipasir))]
pub fn ipasir_solver_derive(input: TokenStream) -> TokenStream {
	let input = parse_macro_input!(input);
	let opts = IpasirOpts::from_derive_input(&input).expect("Invalid options");
	let DeriveInput { ident, .. } = input;

	let krate = opts.krate;
	let ptr = match opts.ptr {
		Some(x) => quote! { self. #x },
		None => quote! { self.ptr },
	};
	let vars = match opts.vars {
		Some(x) => quote! { self. #x },
		None => quote! { self.vars },
	};

	let assumptions = if opts.assumptions {
		quote! {
			impl crate::solver::SolveAssuming for #ident {
				fn solve_assuming<
					I: IntoIterator<Item = crate::Lit>,
					SolCb: FnOnce(&dyn crate::Valuation),
					FailCb: FnOnce(&crate::solver::FailFn<'_>),
				>(
					&mut self,
					assumptions: I,
					on_sol: SolCb,
					on_fail: FailCb,
				) -> crate::solver::SolveResult {
					use crate::solver::Solver;
					for i in assumptions {
						unsafe { #krate::ipasir_assume(#ptr, i.into()) }
					}
					match self.solve(on_sol) {
						crate::solver::SolveResult::Unsat => {
							let fail_fn = |lit: crate::Lit| {
								let lit: i32 = lit.into();
								let failed = unsafe { #krate::ipasir_failed(#ptr, lit) };
								failed != 0
							};
							on_fail(&fail_fn);
							crate::solver::SolveResult::Unsat
						}
						r => r,
					}
				}
			}
		}
	} else {
		quote!()
	};

	let term_callback = if opts.term_callback {
		quote! {
			impl crate::solver::TermCallback for #ident {
				fn set_terminate_callback<F: FnMut() -> crate::solver::SolverAction>(
					&mut self,
					cb: Option<F>,
				) {
					if let Some(mut cb) = cb {
						let mut wrapped_cb = || -> std::ffi::c_int {
							match cb() {
								crate::solver::SolverAction::Continue => std::ffi::c_int::from(0),
								crate::solver::SolverAction::Terminate => std::ffi::c_int::from(1),
							}
						};
						let data = &mut wrapped_cb as *mut _ as *mut std::ffi::c_void;
						unsafe {
							#krate::ipasir_set_terminate(
								#ptr,
								data,
								Some(crate::solver::get_trampoline0(&wrapped_cb)),
							)
						}
					} else {
						unsafe { #krate::ipasir_set_terminate(#ptr, std::ptr::null_mut(), None) }
					}
				}
			}
		}
	} else {
		quote!()
	};

	let learn_callback = if opts.learn_callback {
		quote! {
			impl crate::solver::LearnCallback for #ident {
				fn set_learn_callback<F: FnMut(&mut dyn Iterator<Item = crate::Lit>)>(
					&mut self,
					cb: Option<F>,
				) {
					const MAX_LEN: std::ffi::c_int = 512;
					if let Some(mut cb) = cb {
						let mut wrapped_cb = |clause: *const i32| {
							let mut iter = crate::solver::ExplIter(clause)
								.map(|i: i32| crate::Lit(std::num::NonZeroI32::new(i).unwrap()));
							cb(&mut iter)
						};
						let data = &mut wrapped_cb as *mut _ as *mut std::ffi::c_void;
						unsafe {
							#krate::ipasir_set_learn(
								#ptr,
								data,
								MAX_LEN,
								Some(crate::solver::get_trampoline1(&wrapped_cb)),
							)
						}
					} else {
						unsafe { #krate::ipasir_set_learn(#ptr, std::ptr::null_mut(), MAX_LEN, None) }
					}
				}
			}
		}
	} else {
		quote!()
	};

	quote! {
		impl Drop for #ident {
			fn drop(&mut self) {
				unsafe { #krate::ipasir_release( #ptr ) }
			}
		}

		impl crate::ClauseDatabase for #ident {
			fn new_var(&mut self) -> crate::Lit {
				#vars .next().expect("variable pool exhaused").into()
			}

			fn add_clause<I: IntoIterator<Item = crate::Lit>>(
				&mut self,
				clause: I,
			) -> crate::Result {
				let mut added = false;
				for lit in clause.into_iter() {
					unsafe { #krate::ipasir_add( #ptr , lit.into()) };
					added = true;
				}
				if added {
					unsafe { #krate::ipasir_add( #ptr , 0) };
				}
				Ok(())
			}
		}

		impl crate::solver::Solver for #ident {
			fn signature(&self) -> &str {
				unsafe { std::ffi::CStr::from_ptr(#krate::ipasir_signature()) }
					.to_str()
					.unwrap()
			}

			fn solve<SolCb: FnOnce(&dyn crate::Valuation)>(
				&mut self,
				on_sol: SolCb,
			) -> crate::solver::SolveResult {
				let res = unsafe { #krate::ipasir_solve( #ptr ) };
				match res {
					10 => {
						// 10 -> Sat
						let val_fn = |lit: crate::Lit| {
							let var: i32 = lit.var().into();
							// WARN: Always ask about variable (positive) literal, otherwise solvers sometimes seem incorrect
							let ret = unsafe { #krate::ipasir_val( #ptr , var) };
							match ret {
								_ if ret == var => Some(!lit.is_negated()),
								_ if ret == -var => Some(lit.is_negated()),
								_ => {
									debug_assert_eq!(ret, 0); // zero according to spec, both value are valid
									None
								}
							}
						};
						on_sol(&val_fn);
						crate::solver::SolveResult::Sat
					}
					20 => crate::solver::SolveResult::Unsat, // 20 -> Unsat
					_ => {
						debug_assert_eq!(res, 0); // According to spec should be 0, unknown
						crate::solver::SolveResult::Unknown
					}
				}
			}
		}

		#assumptions
		#term_callback
		#learn_callback
	}
	.into()
}
