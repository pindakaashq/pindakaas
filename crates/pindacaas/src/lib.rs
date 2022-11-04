use libc::size_t;
use pindakaas::{ClauseDatabase, Result, Unsatisfiable};
use std::{ffi::c_void, slice};

/// The type used to represent Literals in the C Pindakaas library
pub type Lit = i32;
/// The type used to represent Coefficients in the C Pindakaas library
pub type Coeff = i32;

#[derive(Debug, Eq, PartialEq)]
#[repr(C)]
pub enum Comparator {
	LessEq,
	Equal,
	GreaterEq,
}

/// Callback type used when a clause is emitted by the encoder.
///
/// The first argument will always be the `db` pointer given to the encoding function. The second
/// argument is the pointer to the start of the "slice" of literals that form the clause. The third
/// and final argument gives the number of literals in the clause. The callback function can return
/// `false` to signal when the problem is proven now be unsatisfiable, or `true` otherwise.
///
/// # Safety
/// The clause given to the callback exists only in temporary memory. If the clause is later
/// used in the same form, then it MUST be copied to persistent memory.
type AddClauseCB = extern "C" fn(*mut c_void, *const Lit, size_t) -> bool;

/// Callback type used when a new, unused, Boolean Literal must be created for an encoding.
///
/// The first argument will always be the `db` pointer given to the encoding function. The return
/// type should be a `Lit` reprenting an unused Boolean Literal.
type NewVarCB = extern "C" fn(*mut c_void) -> Lit;

/// Encodes a Boolean linear expressions into Boolean clauses. TODO: ...
///
/// # Safety
/// This function depends on receiving valid pointers to arrays of coefficients and literals, and
/// their correct length.
#[no_mangle]
pub unsafe extern "C" fn encode_bool_lin(
	db: *mut c_void,
	add_clause_cb: AddClauseCB,
	new_var_cb: NewVarCB,
	coeff: *const Coeff,
	coeff_len: size_t,
	lit: *const Lit,
	lit_len: size_t,
	cmp: Comparator,
	_k: Coeff,
) -> bool {
	let mut _cdb = CClauseDatabase {
		db,
		add_clause_cb,
		new_var_cb,
	};

	// (unsafe) Dereference raw ptr arguments, segmentation fault if given bad arguments.
	let _coeff = slice::from_raw_parts(coeff, coeff_len);
	let _lit = slice::from_raw_parts(lit, lit_len);

	let _cmp = match cmp {
		Comparator::LessEq => pindakaas::Comparator::LessEq,
		Comparator::Equal => pindakaas::Comparator::Equal,
		Comparator::GreaterEq => pindakaas::Comparator::GreaterEq,
	};
	// cdb.encode_bool_lin::<i32, u32>(coeff, lit, cmp, k, &[])
	// 	.is_ok()
	unimplemented!()
}

struct CClauseDatabase {
	db: *mut c_void,
	add_clause_cb: AddClauseCB,
	new_var_cb: NewVarCB,
}

#[cfg(feature = "label")]
unimplemented!("The feature `label` is not implemented for pindacaas crate");

impl ClauseDatabase for CClauseDatabase {
	type Lit = Lit;

	fn add_clause(&mut self, cl: &[Self::Lit]) -> Result {
		if (self.add_clause_cb)(self.db, cl.as_ptr(), cl.len() as size_t) {
			Ok(())
		} else {
			Err(Unsatisfiable)
		}
	}
	fn new_var(&mut self) -> Self::Lit {
		(self.new_var_cb)(self.db)
	}
}

#[cfg(test)]
mod tests {}
