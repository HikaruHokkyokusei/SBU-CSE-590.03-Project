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

    pub open spec fn safety(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |i: int, j: int| #![auto]
                0 <= i < j < u.hosts.len() &&
                u.hosts[i].decide_value.is_some() &&
                u.hosts[j].decide_value.is_some() ==>
                u.hosts[i].decide_value == u.hosts[j].decide_value
    }

    pub open spec fn all_ballot_pids_in_host_maps_is_same_as_corresponding_host_id(c: &Constants, u: &Variables) -> bool {
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].promised.contains_key(ballot) ==>
                ballot.pid == c.hosts[i].id
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].proposed_value.contains_key(ballot) ==>
                ballot.pid == c.hosts[i].id
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].accepted.contains_key(ballot) ==>
                ballot.pid == c.hosts[i].id
    }

    pub open spec fn promised_has_promise_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int, ballot: host::Ballot, sender: nat| #![auto]
            0 <= i < u.hosts.len() &&
            u.hosts[i].promised.dom().contains(ballot) &&
            u.hosts[i].promised[ballot].dom().contains(sender) ==>
            u.network.in_flight_messages.contains(Message::Promise { sender, ballot, accepted: u.hosts[i].promised[ballot][sender] })
    }

    pub open spec fn accept_has_accept_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int| #![auto]
            0 <= i < u.hosts.len() &&
            (u.hosts[i].accept_ballot.is_some() || u.hosts[i].accept_value.is_some()) ==>
            u.hosts[i].accept_ballot.is_some() &&
            u.hosts[i].accept_value.is_some() &&
            u.network.in_flight_messages.contains(Message::Accept { ballot: u.hosts[i].accept_ballot.unwrap(), value: u.hosts[i].accept_value.unwrap() })
    }

    pub open spec fn accepted_has_accepted_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int, ballot: host::Ballot, sender: nat| #![auto]
            0 <= i < u.hosts.len() &&
            u.hosts[i].accepted.dom().contains(ballot) &&
            u.hosts[i].accepted[ballot].contains(sender) ==>
            u.network.in_flight_messages.contains(Message::Accepted { sender, ballot })
    }

    pub open spec fn decide_has_decide_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int| #![auto]
            0 <= i < u.hosts.len() &&
            u.hosts[i].decide_value.is_some() ==>
            exists |ballot: host::Ballot| #![auto] u.network.in_flight_messages.contains(Message::Decide { ballot, value: u.hosts[i].decide_value.unwrap() })
    }

    pub open spec fn all_decide_messages_hold_same_value(c: &Constants, u: &Variables) -> bool {
        forall |msg1: Message, msg2: Message| #![auto]
            u.network.in_flight_messages.contains(msg1) &&
            u.network.in_flight_messages.contains(msg2) ==>
            match (msg1, msg2) {
                (Message::Decide { value: value1, .. }, Message::Decide { value: value2, .. }) => { value1 == value2 },
                _ => { true }
            }
    }

    pub open spec fn inductive(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& u.network.in_flight_messages.finite()
        &&& all_ballot_pids_in_host_maps_is_same_as_corresponding_host_id(c, u)
        &&& promised_has_promise_message_in_network(c, u)
        &&& accept_has_accept_message_in_network(c, u)
        &&& accepted_has_accepted_message_in_network(c, u)
        &&& decide_has_decide_message_in_network(c, u)
        &&& all_decide_messages_hold_same_value(c, u)
        &&& true
    }

    pub proof fn inductive_next_implies_decide_has_decide_message_in_network(c: &Constants, u: &Variables, v: &Variables, event: Event)
    requires
        inductive(c, u),
        next(c, u, v, event),
    ensures
        decide_has_decide_message_in_network(c, v),
    {
        assert(u.network.in_flight_messages.finite());
        assert(v.network.in_flight_messages.finite());

        let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, v, transition, event);
        let (host_c, host_u, host_v) = (&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id]);

        assert forall |i: int| #![auto]
            0 <= i < v.hosts.len() &&
            v.hosts[i].decide_value.is_some() implies
            exists |ballot: host::Ballot| #![auto] v.network.in_flight_messages.contains(Message::Decide { ballot, value: v.hosts[i].decide_value.unwrap() })
        by {
            match ((event, net_op.recv)) {
                (Event::Decide { value }, Some(Message::Decide { ballot: recv_bal, value: recv_val }))
                if (i == host_id) => {
                    assert(host::decide(host_c, host_u, host_v, net_op, value));
                    assert(recv_val == v.hosts[i].decide_value.unwrap());
                    assert(v.network.in_flight_messages.contains(Message::Decide { ballot: recv_bal, value: recv_val }));
                    assert(exists |ballot: host::Ballot| #![auto] v.network.in_flight_messages.contains(Message::Decide { ballot, value: v.hosts[i].decide_value.unwrap() }));
                },
                _ => { }
            }
        };
    }
}
