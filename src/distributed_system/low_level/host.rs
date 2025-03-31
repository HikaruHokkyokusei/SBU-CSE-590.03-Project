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
}
