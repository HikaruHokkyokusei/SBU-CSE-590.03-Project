use crate::distributed_system::Value;
use vstd::prelude::*;

verus! {
    pub struct Ballot {
        pub num: nat,
        pub pid: nat,
    }

    impl Ballot {
        pub open spec fn cmp(&self, other: &Ballot) -> int {
            if (self.num < other.num) {
                -1
            } else if (self.num > other.num) {
                1
            } else if (self.pid < other.pid) {
                -1
            } else if (self.pid > other.pid) {
                1
            } else {
                0
            }
        }
    }

    pub struct Constants {
        pub id: nat,
        pub num_hosts: nat,
        pub num_failures: nat,
    }

    pub struct Variables {
        pub current_ballot: Ballot,
        pub promised: Map<Ballot, Map<nat, Option<(Ballot, Value)>>>,
        pub proposed_value: Map<Ballot, Value>,
        pub accepted: Map<Ballot, Set<nat>>,
        pub accept_ballot: Option<Ballot>,
        pub accept_value: Option<Value>,
        pub decide_value: Option<Value>,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& 0 <= self.id < self.num_hosts
            &&& self.num_hosts == ((2 * self.num_failures) + 1)
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.accept_ballot.is_some() == self.accept_value.is_some()
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables, host_id: nat, num_hosts: nat) -> bool {
        &&& u.well_formed(c)
        &&& c.id == host_id
        &&& c.num_hosts == num_hosts
        &&& u.current_ballot == Ballot { num: 0, pid: 0 }
        &&& u.promised.is_empty()
        &&& u.proposed_value.is_empty()
        &&& u.accepted.is_empty()
        &&& u.accept_ballot.is_none()
        &&& u.accept_value.is_none()
        &&& u.decide_value.is_none()
    }
}
