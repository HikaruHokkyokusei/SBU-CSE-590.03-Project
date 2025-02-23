use vstd::prelude::*;

verus! {
    struct Constants {
        z: i64
    }

    struct Variables {
        x: i64,
        y: i64
    }

    spec fn init(u: Variables) -> bool {
        u.x == 0 && u.y == 5
    }

    fn main() { }
}
