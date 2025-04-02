use super::{Event, Value};
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub decided_value: Option<Value>,
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.decided_value.is_none()
    }

    pub open spec fn decide(c: &Constants, u: &Variables, v: &Variables, value: Value) -> bool {
        &&& u.decided_value.is_some() ==> u.decided_value == Some(value)
        &&& v.decided_value == Some(value)
    }

    pub open spec fn next(c: &Constants, u: &Variables, v: &Variables, event: Event) -> bool {
        match event {
            Event::Decide { value } => { decide(c, u, v, value) },
            Event::NoOp => { v == u },
        }
    }
}
