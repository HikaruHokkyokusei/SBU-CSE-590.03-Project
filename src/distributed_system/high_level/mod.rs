use super::Event;
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub counter: int,
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.counter == 0
    }

    pub open spec fn increment_counter(c: &Constants, u: &Variables, v: &Variables) -> bool {
        &&& v.counter == u.counter + 1
    }

    pub open spec fn next(c: &Constants, u: &Variables, v: &Variables, event: Event) -> bool {
        match event {
            Event::Increment => { increment_counter(c, u, v) },
            Event::NoOp => { v == u },
        }
    }
}
