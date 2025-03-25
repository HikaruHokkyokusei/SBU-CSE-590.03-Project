pub mod host;
pub mod network;

use vstd::prelude::*;

verus! {
    pub enum Message {
        Transfer { counter: int },
    }

    pub struct NetworkOperation {
        pub send: Option<Message>,
        pub recv: Option<Message>,
    }

    pub struct Constants {
        pub num_hosts: int,
        pub hosts: Seq<host::Constants>,
        pub network: network::Constants,
    }

    pub struct Variables {
        pub hosts: Seq<host::Variables>,
        pub network: network::Variables,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.num_hosts > 0
            &&& self.hosts.len() == self.num_hosts
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.hosts.len() == c.hosts.len()
            &&& forall |idx: int| #![auto] 0 <= idx < self.hosts.len() ==> self.hosts[idx].well_formed(&c.hosts[idx], idx)
            &&& self.network.well_formed(&c.network)
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |idx: int| #![auto] 0 <= idx < u.hosts.len() ==> host::init(&c.hosts[idx], &u.hosts[idx], idx) && if (idx == 0) { u.hosts[idx].holds_counter } else { !u.hosts[idx].holds_counter }
        &&& network::init(&c.network, &u.network)
    }
}
