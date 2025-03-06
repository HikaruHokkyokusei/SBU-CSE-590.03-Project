pub(crate) mod coordinator;
pub(crate) mod host;
pub(crate) mod network;

use vstd::prelude::*;

verus! {
    pub(crate) enum Decision {
        Commit,
        Abort
    }

    pub(crate) enum Message {
        VoteRequest,
        Vote{ sender: int, vote: host::Vote },
        Decision{ decision: Decision }
    }

    pub(crate) struct Constants {
        pub(crate) num_hosts: int,
        pub(crate) coordinator: coordinator::Constants,
        pub(crate) hosts: Seq<host::Constants>,
        pub(crate) network: network::Constants,
    }

    pub(crate) struct Variables {
        pub(crate) coordinator: coordinator::Variables,
        pub(crate) hosts: Seq<host::Variables>,
        pub(crate) network: network::Variables,
    }

    impl Constants {
        pub(crate) open spec fn well_formed(&self) -> bool {
            &&& self.num_hosts > 0
            &&& self.hosts.len() == self.num_hosts
        }
    }

    impl Variables {
        pub(crate) open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.hosts.len() == c.hosts.len()
            &&& self.coordinator.well_formed(&c.coordinator, c.num_hosts)
            &&& forall |idx: int| 0 <= idx < self.hosts.len() ==> self.hosts[idx].well_formed(&c.hosts[idx], idx)
            &&& self.network.well_formed(&c.network)
        }
    }

    pub(crate) open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& coordinator::init(&c.coordinator, &u.coordinator, c.num_hosts)
        &&& forall |idx: int| 0 <= idx < u.hosts.len() ==> host::init(&c.hosts[idx], &u.hosts[idx], idx)
        &&& network::init(&c.network, &u.network)
    }
}
