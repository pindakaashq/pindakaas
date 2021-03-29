use std::ops::Neg;
use std::cmp::Eq;

pub trait Literal: Eq + Neg<Output = Self> {}
impl<T> Literal for T where T: Eq + Neg<Output = Self> {}

pub trait ClauseSink {
    type Lit: Literal;
    fn add_clause(self, cl: &[Self::Lit]) -> bool;
}

pub trait LiteralGenerator {
    type Lit: Literal;
    fn new_lit(self) -> Self::Lit;
}



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
