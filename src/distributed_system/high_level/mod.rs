use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub counter: int,
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.counter == 0
    }
}
