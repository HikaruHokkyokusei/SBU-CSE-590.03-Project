use super::{Event, Value};
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub decided_value: Map<nat, Value>,
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.decided_value.is_empty()
    }

    pub open spec fn decide(c: &Constants, u: &Variables, v: &Variables, key: nat, value: Value) -> bool {
        &&& u.decided_value.contains_key(key) ==> u.decided_value[key] == value
        &&& v.decided_value == u.decided_value.insert(key, value)
    }

    pub open spec fn next(c: &Constants, u: &Variables, v: &Variables, event: Event) -> bool {
        match event {
            Event::Decide { key, value } => { decide(c, u, v, key, value) },
            Event::NoOp => { v == u },
        }
    }
}
