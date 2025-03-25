use vstd::prelude::*;

verus! {
    pub struct Constants {
        pub id: int,
    }

    pub struct Variables {
        pub holds_counter: bool,
        pub counter: int,
    }
}
