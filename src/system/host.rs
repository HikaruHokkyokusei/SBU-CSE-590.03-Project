use vstd::prelude::*;

verus! {
    pub(crate) struct Constants {
        pub(crate) ids: Vec<i64>
    }

    pub(crate) struct Variables {
        pub(crate) max_received_ids: Vec<i64>
    }
}
