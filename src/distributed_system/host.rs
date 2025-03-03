use super::Decision;
use vstd::prelude::*;

verus! {
    pub(crate) struct Constants {
        pub(crate) id: u64
    }

    pub(crate) struct Variables {
        pub(crate) decision: Decision
    }
}
