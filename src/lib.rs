use std::ops::Neg;
use std::cmp::Eq;

trait Literal: Eq + Neg<Output = Self> {}
impl<T> Literal for T where T: Eq + Neg<Output = Self> {}

#[cfg(test)]
mod tests {
    use crate::*;

    fn is_lit<Lit: Literal>() {}
    #[test]
    fn integer_literals() {
        is_lit::<i8>();
        is_lit::<i16>();
        is_lit::<i32>();
        is_lit::<i64>();
        is_lit::<i128>();
    }
}
