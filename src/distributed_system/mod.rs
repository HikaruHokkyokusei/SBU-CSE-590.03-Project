pub(crate) mod coordinator;
pub(crate) mod host;
pub(crate) mod network;

use vstd::prelude::*;

verus! {
    pub(crate) enum Decision {
        Commit,
        Abort,
    }

    pub(crate) enum Message {
        VoteRequest,
        Vote { sender: int, vote: host::Vote },
        Decision { decision: Decision },
    }

    pub(crate) struct MessageOps {
        pub(crate) send: Option<Message>,
        pub(crate) recv: Option<Message>,
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

    pub(crate) enum Transition {
        CoordinatorStep { message_ops: MessageOps },
        HostStep { host_id: int, message_ops: MessageOps }
    }

    pub(crate) open spec fn coordinator_step(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c)
        &&& coordinator::step(&c.coordinator, &u.coordinator, &v.coordinator, message_ops)
        &&& network::step(&c.network, &u.network, &v.network, message_ops)
        &&& v.well_formed(c)
    }

    pub(crate) open spec fn host_step(c: &Constants, u: &Variables, v: &Variables, host_id: int, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c)
        &&& {
            &&& 0 <= host_id < u.hosts.len()
            &&& host::step(&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id], message_ops)
            &&& forall |i: int| 0 <= i < v.hosts.len() && i != host_id ==> u.hosts[i] == v.hosts[i]
        }
        &&& network::step(&c.network, &u.network, &v.network, message_ops)
        &&& v.well_formed(c)
    }

    pub(crate) open spec fn is_valid_transition(c: &Constants, u: &Variables, v: &Variables, transition: Transition) -> bool {
        match transition {
            Transition::CoordinatorStep { message_ops } => coordinator_step(c, u, v, message_ops),
            Transition::HostStep { host_id, message_ops } => host_step(c, u, v, host_id, message_ops)
        }
    }

    pub(crate) open spec fn next(c: &Constants, u: &Variables, v: &Variables, host_id: int, message_ops: MessageOps) -> bool {
        exists |transition: Transition| is_valid_transition(c, u, v, transition)
    }
}
