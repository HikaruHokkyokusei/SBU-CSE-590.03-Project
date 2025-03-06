use super::Decision;
use vstd::prelude::*;

verus! {
    pub(crate) enum Vote {
        Yes,
        No
    }

    pub(crate) struct Constants {
        pub(crate) id: int,
        pub(crate) vote: Vote
    }

    pub(crate) struct Variables {
        pub(crate) decision: Option<Decision>
    }
}
