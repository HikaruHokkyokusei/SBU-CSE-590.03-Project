use super::{host::Vote, Decision};
use vstd::prelude::*;

verus! {
    pub(crate) struct Constants {
        pub(crate) num_hosts: int
    }

    pub(crate) struct Variables {
        pub(crate) decision: Option<Decision>,
        pub(crate) votes: Seq<Option<Vote>>
    }
}
