use super::Value;
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub decided_value: Option<Value>,
    }
}
