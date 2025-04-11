use super::{Message, NetworkOperation};
use crate::distributed_system::{Event, Value};
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
            &&& self.num_hosts > 0
            &&& self.num_failures > 0
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

    pub open spec fn send_prepare(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        let new_ballot = Ballot { num: u.current_ballot.num + 1, pid: c.id };

        &&& u.decide_value.is_none()
        &&& net_op.recv.is_none()
        &&& !u.promised.dom().contains(new_ballot)
        &&& !u.accepted.dom().contains(new_ballot)
        &&& v.current_ballot == u.current_ballot
        &&& v.promised == u.promised.insert(new_ballot, Map::empty())
        &&& v.proposed_value == u.proposed_value
        &&& v.accepted == u.accepted.insert(new_ballot, Set::empty())
        &&& v.accept_ballot == u.accept_ballot
        &&& v.accept_value == u.accept_value
        &&& v.decide_value == u.decide_value
        &&& net_op.send == Some(Message::Prepare { ballot: new_ballot })
    }

    pub open spec fn promise(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Prepare { ballot }) = net_op.recv {
            &&& ballot.cmp(&u.current_ballot) == 1
            &&& v.current_ballot == ballot
            &&& v.promised == u.promised
            &&& v.proposed_value == u.proposed_value
            &&& v.accepted == u.accepted
            &&& v.accept_ballot == u.accept_ballot
            &&& v.accept_value == u.accept_value
            &&& v.decide_value == u.decide_value
            &&& net_op.send == if (u.accept_ballot.is_some()) {
                    Some(Message::Promise { sender: c.id, ballot, accepted: Some((u.accept_ballot.unwrap(), u.accept_value.unwrap())) })
                } else {
                    Some(Message::Promise { sender: c.id, ballot, accepted: None })
                }
        } else {
            &&& false
        }
    }

    pub open spec fn promised(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Promise { sender, ballot, accepted }) = net_op.recv {
            &&& u.promised.dom().contains(ballot)
            &&& !u.proposed_value.contains_key(ballot)
            &&& v.current_ballot == u.current_ballot
            &&& v.promised == u.promised.insert(ballot, u.promised[ballot].insert(sender, accepted))
            &&& v.proposed_value == u.proposed_value
            &&& v.accepted == u.accepted
            &&& v.accept_ballot == u.accept_ballot
            &&& v.accept_value == u.accept_value
            &&& v.decide_value == u.decide_value
            &&& net_op.send.is_none()
        } else {
            &&& false
        }
    }

    pub open spec fn max_accepted_value_by_ballot(a: Option<(Ballot, Value)>, b: Option<(Ballot, Value)>) -> Option<(Ballot, Value)> {
        if (a.is_none() && b.is_none()) {
            None
        } else if (a.is_none()) {
            b
        } else if (b.is_none()) {
            a
        } else {
            let (a, b) = (a.unwrap(), b.unwrap());
            if (a.0.cmp(&b.0) >= 0) {
                Some(a)
            } else {
                Some(b)
            }
        }
    }

    pub open spec fn get_max_accepted_value(accepted_map: Map<nat, Option<(Ballot, Value)>>) -> Option<(Ballot, Value)>
    recommends
        accepted_map.dom().finite()
    decreases
        accepted_map.dom().len()
    {
        if (accepted_map.dom().finite() && accepted_map.dom().len() > 0) {
            let key = accepted_map.dom().choose();
            let value = accepted_map[key];
            max_accepted_value_by_ballot(value, get_max_accepted_value(accepted_map.remove(key)))
        } else {
            None
        }
    }

    pub open spec fn send_accept(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        &&& net_op.recv.is_none()
        &&& u.promised.contains_key(u.current_ballot)
        &&& u.promised[u.current_ballot].len() > c.num_failures
        &&& !u.proposed_value.contains_key(u.current_ballot)
        &&& v.current_ballot == u.current_ballot
        &&& v.promised == u.promised
        &&& v.proposed_value == u.proposed_value.insert(
                u.current_ballot,
                if let Some((_, value)) = get_max_accepted_value(u.promised[u.current_ballot]) { value } else { c.id as Value }
            )
        &&& v.accepted == u.accepted
        &&& v.accept_ballot == u.accept_ballot
        &&& v.accept_value == u.accept_value
        &&& v.decide_value == u.decide_value
        &&& net_op.send == Some(Message::Accept { ballot: v.current_ballot, value: v.proposed_value[v.current_ballot] })
    }

    pub open spec fn accept(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Accept { ballot, value }) = net_op.recv {
            &&& ballot.cmp(&u.current_ballot) == 1
            &&& v.current_ballot == ballot
            &&& v.promised == u.promised
            &&& v.proposed_value == u.proposed_value
            &&& v.accepted == u.accepted
            &&& v.accept_ballot == Some(ballot)
            &&& v.accept_value == Some(value)
            &&& v.decide_value == u.decide_value
            &&& net_op.send == Some(Message::Accepted { sender: c.id, ballot })
        } else {
            &&& false
        }
    }

    pub open spec fn accepted(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Accepted { sender, ballot }) = net_op.recv {
            &&& u.accepted.dom().contains(ballot)
            &&& v.current_ballot == u.current_ballot
            &&& v.promised == u.promised
            &&& v.proposed_value == u.proposed_value
            &&& v.accepted == u.accepted.insert(ballot, u.accepted[ballot].insert(sender))
            &&& v.accept_ballot == u.accept_ballot
            &&& v.accept_value == u.accept_value
            &&& v.decide_value == u.decide_value
            &&& net_op.send.is_none()
        } else {
            &&& false
        }
    }

    pub open spec fn send_decide(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        &&& net_op.recv.is_none()
        &&& u.accept_ballot == Some(u.current_ballot)
        &&& u.proposed_value.contains_key(u.current_ballot)
        &&& u.accepted.contains_key(u.current_ballot)
        &&& u.accepted[u.current_ballot].len() > c.num_failures
        &&& v.current_ballot == u.current_ballot
        &&& v.promised == u.promised
        &&& v.proposed_value == u.proposed_value
        &&& v.accepted == u.accepted
        &&& v.accept_ballot == u.accept_ballot
        &&& v.accept_value == u.accept_value
        &&& v.decide_value == u.decide_value
        &&& net_op.send == Some(Message::Decide { ballot: u.current_ballot, value: u.proposed_value[u.current_ballot] })
    }

    pub open spec fn decide(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation, expected_value: Value) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Decide { ballot, value }) = net_op.recv {
            &&& ballot.cmp(&u.current_ballot) == 1
            &&& value == expected_value
            &&& v.current_ballot == ballot
            &&& v.promised == u.promised
            &&& v.proposed_value == u.proposed_value
            &&& v.accepted == u.accepted
            &&& v.accept_ballot == u.accept_ballot
            &&& v.accept_value == u.accept_value
            &&& v.decide_value == Some(value)
            &&& net_op.send.is_none()
        } else {
            &&& false
        }
    }

    pub open spec fn step(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation, event: Event) -> bool {
        &&& u.well_formed(c)
        &&& v.well_formed(c)
        &&& match event {
                Event::Decide { value } => decide(c, u, v, net_op, value),
                Event::NoOp => {
                    ||| send_prepare(c, u, v, net_op)
                    ||| promise(c, u, v, net_op)
                    ||| promised(c, u, v, net_op)
                    ||| send_accept(c, u, v, net_op)
                    ||| accept(c, u, v, net_op)
                    ||| accepted(c, u, v, net_op)
                    ||| send_decide(c, u, v, net_op)
                },
            }
    }
}
