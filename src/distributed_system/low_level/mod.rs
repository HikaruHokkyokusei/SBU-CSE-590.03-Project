use super::{Event, Value};
use vstd::prelude::*;

verus! {
    pub mod host;
    pub mod network;

    pub enum Message {
        Prepare { ballot: host::Ballot },
        Promise { sender: nat, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)> },
        Accept { ballot: host::Ballot, value: Value },
        Accepted { sender: nat, ballot: host::Ballot },
        Decide { ballot: host::Ballot, value: Value },
    }

    pub struct NetworkOperation {
        pub send: Option<Message>,
        pub recv: Option<Message>,
    }

    pub struct Constants {
        pub num_failures: nat,
        pub num_hosts: nat,
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
            &&& self.num_hosts == ((2 * self.num_failures) + 1)
            &&& self.hosts.len() == self.num_hosts
            &&& forall |i: nat| #![auto]
                    0 <= i < self.num_hosts ==>
                    self.hosts[i as int].id == i &&
                    self.hosts[i as int].num_failures == self.num_failures
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.hosts.len() == c.hosts.len()
            &&& forall |idx: nat| #![auto] 0 <= idx < self.hosts.len() ==> self.hosts[idx as int].well_formed(&c.hosts[idx as int])
            &&& self.network.well_formed(&c.network)
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |idx: nat| #![auto]
                0 <= idx < u.hosts.len() ==>
                host::init(&c.hosts[idx as int], &u.hosts[idx as int], idx, u.hosts.len())
        &&& network::init(&c.network, &u.network)
    }

    pub enum Transition {
        HostStep { host_id: int, net_op: NetworkOperation }
    }

    pub open spec fn host_step(c: &Constants, u: &Variables, v: &Variables, host_id: int, net_op: NetworkOperation, event: Event) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        &&& {
            &&& 0 <= host_id < u.hosts.len()
            &&& host::step(&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id], net_op, event)
            &&& forall |i: int| 0 <= i < v.hosts.len() && i != host_id ==> u.hosts[i] == v.hosts[i]
        }
        &&& network::step(&c.network, &u.network, &v.network, net_op)
    }

    pub open spec fn is_valid_transition(c: &Constants, u: &Variables, v: &Variables, transition: Transition, event: Event) -> bool {
        &&& u.well_formed(c)
        &&& v.well_formed(c)
        &&& match transition {
            Transition::HostStep { host_id, net_op } => host_step(c, u, v, host_id, net_op, event)
        }
    }

    pub open spec fn next(c: &Constants, u: &Variables, v: &Variables, event: Event) -> bool {
        exists |transition: Transition| is_valid_transition(c, u, v, transition, event)
    }
}
