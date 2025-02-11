use vstd::prelude::*; verus! {
    spec fn is_even(a: i64) -> bool {
        a % 2 == 0
    }

    fn main() {}
}
