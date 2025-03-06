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

    impl Constants {
        pub(crate) open spec fn well_formed(&self, num_hosts: int) -> bool {
            self.num_hosts == num_hosts
        }
    }

    impl Variables {
        pub(crate) open spec fn well_formed(&self, c: &Constants, num_hosts: int) -> bool {
            &&& c.well_formed(num_hosts)
            &&& self.votes.len() == num_hosts
        }
    }

    pub(crate) open spec fn init(c: &Constants, u: &Variables, num_hosts: int) -> bool {
        &&& u.well_formed(c, num_hosts)
        &&& u.decision.is_none()
        &&& forall |i: int| 0 <= i < u.votes.len() ==> u.votes[i].is_none()
    }
}
