use super::Value;
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub decided_value: Option<Value>,
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.decided_value.is_none()
    }
}
