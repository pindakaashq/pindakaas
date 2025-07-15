//! Compile time optional field implementation.

use std::hash::{Hash, Hasher};

#[derive(Debug)]
/// Compile time optional field.
///
/// This is used to represent fields that may or may not be present in a struct,
/// based on a compile time constant.
///
/// Note that `B` is a `usize` constant because of implementation limitations in
/// Rust. It should, however, be a `bool` and only the values `0` and `1` should
/// be used.
pub(crate) struct OptField<const B: usize, T> {
	/// Content of the field, if any.
	value: [T; B],
}

impl<T> OptField<1, T> {
	/// Mutable access to the field that is known to exist.
	pub(crate) fn some_mut(&mut self) -> &mut T {
		&mut self.value[0]
	}

	/// Access the field that is known to exist.
	#[cfg(feature = "external-propagation")]
	pub(crate) fn some_ref(&self) -> &T {
		&self.value[0]
	}
}

impl<const B: usize, T> OptField<B, T> {
	/// Return the value of the `OptField`, if it exists.
	pub(crate) fn as_ref(&self) -> Option<&T> {
		self.value.first()
	}
}

impl<const B: usize, T: Clone> Clone for OptField<B, T> {
	fn clone(&self) -> Self {
		Self {
			value: self.value.clone(),
		}
	}
}

impl<const B: usize, T: Default> Default for OptField<B, T> {
	fn default() -> Self {
		Self {
			value: [(); B].map(|_| T::default()),
		}
	}
}

impl<const B: usize, T: Eq> Eq for OptField<B, T> {}

impl<const B: usize, T: Hash> Hash for OptField<B, T> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.value.iter().for_each(|v| v.hash(state));
	}
}

impl<const B: usize, T: PartialEq> PartialEq for OptField<B, T> {
	fn eq(&self, other: &Self) -> bool {
		self.value == other.value
	}
}
