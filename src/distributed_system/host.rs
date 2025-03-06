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

    impl Constants {
        pub(crate) open spec fn well_formed(&self, id: int) -> bool {
            &&& id >= 0
            &&& self.id == id
        }
    }

    impl Variables {
        pub(crate) open spec fn well_formed(&self, c: &Constants, id: int) -> bool {
            &&& c.well_formed(id)
        }
    }

    pub(crate) open spec fn init(c: &Constants, u: &Variables, host_id: int) -> bool {
        &&& u.well_formed(c, host_id)
        &&& u.decision.is_none()
    }
}
