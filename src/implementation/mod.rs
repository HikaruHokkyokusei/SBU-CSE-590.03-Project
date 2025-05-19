use crate::distributed_system::{
    low_level::{
        host::{
            init_request as low_init_request, promise as low_promise, promised as low_promised,
            send_accept as low_send_accept, send_prepare as low_send_prepare, Ballot as LowBallot,
        },
        host_step as low_host_step, inductive as low_inductive, init as low_init,
        is_valid_transition, next, Constants as LowConstants, Message as LowMessage,
        NetworkOperation as LowNetworkOperation, Transition, Variables as LowVariables,
    },
    refinement_next, Event, Value as SpecValue,
};
use vstd::prelude::*;

verus! {
    pub mod host;
    pub mod network;

    pub type Value = usize;

    #[derive(Eq, PartialEq, std::hash::Hash)]
    pub enum Message {
        Prepare { key: u64, ballot: host::Ballot },
        Promise { key: u64, sender: usize, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)> },
        Accept { key: u64, ballot: host::Ballot, value: Value },
        Accepted { key: u64, sender: usize, ballot: host::Ballot },
        Decide { key: u64, ballot: host::Ballot, value: Value },
    }

    impl Clone for Message {
        exec fn clone(&self) -> (clone: Self)
        ensures
            clone == self,
        {
            match (self) {
                Message::Prepare { key, ballot } => Self::Prepare {
                    key: key.clone(),
                    ballot: ballot.clone(),
                },
                Message::Promise { key, sender, ballot, accepted } => Self::Promise {
                    key: key.clone(),
                    sender: sender.clone(),
                    ballot: ballot.clone(),
                    accepted: if let Some((ballot, value)) = accepted { Some((ballot.clone(), value.clone())) } else { None },
                },
                Message::Accept { key, ballot, value } => Self::Accept {
                    key: key.clone(),
                    ballot: ballot.clone(),
                    value: value.clone(),
                },
                Message::Accepted { key, sender, ballot } => Self::Accepted {
                    key: key.clone(),
                    sender: sender.clone(),
                    ballot: ballot.clone(),
                },
                Message::Decide { key, ballot, value } => Self::Decide {
                    key: key.clone(),
                    ballot: ballot.clone(),
                    value: value.clone(),
                },
            }
        }
    }

    impl Message {
        pub open spec fn valid_spec(message: LowMessage) -> bool {
            match (message) {
                LowMessage::Prepare { key, ballot } => {
                    &&& key <= u64::MAX
                    &&& host::Ballot::valid_spec(ballot)
                },
                LowMessage::Promise { key, sender, ballot, accepted } => {
                    &&& key <= u64::MAX
                    &&& sender <= usize::MAX
                    &&& host::Ballot::valid_spec(ballot)
                    &&& if let Some((ballot, value)) = accepted {
                        &&& host::Ballot::valid_spec(ballot)
                        &&& Value::MIN <= value <= Value::MAX
                    } else { true }
                }
                LowMessage::Accept { key, ballot, value } => {
                    &&& key <= u64::MAX
                    &&& host::Ballot::valid_spec(ballot)
                    &&& Value::MIN <= value <= Value::MAX
                },
                LowMessage::Accepted { key, sender, ballot } => {
                    &&& key <= u64::MAX
                    &&& sender <= usize::MAX
                    &&& host::Ballot::valid_spec(ballot)
                },
                LowMessage::Decide { key, ballot, value } => {
                    &&& key <= u64::MAX
                    &&& host::Ballot::valid_spec(ballot)
                    &&& Value::MIN <= value <= Value::MAX
                },
            }
        }

        pub open spec fn from_spec(message: LowMessage) -> Self
        recommends
            Message::valid_spec(message),
        {
            match (message) {
                LowMessage::Prepare { key, ballot } => Message::Prepare {
                    key: key as u64,
                    ballot: host::Ballot::from_spec(ballot),
                },
                LowMessage::Promise { key, sender, ballot, accepted } => Message::Promise {
                    key: key as u64,
                    sender: sender as usize,
                    ballot: host::Ballot::from_spec(ballot),
                    accepted: if let Some((ballot, value)) = accepted {
                        Some((host::Ballot::from_spec(ballot), value as Value))
                    } else {
                        None
                    },
                },
                LowMessage::Accept { key, ballot, value } => Message::Accept {
                    key: key as u64,
                    ballot: host::Ballot::from_spec(ballot),
                    value: value as usize,
                },
                LowMessage::Accepted { key, sender, ballot } => Message::Accepted {
                    key: key as u64,
                    sender: sender as usize,
                    ballot: host::Ballot::from_spec(ballot),
                },
                LowMessage::Decide { key, ballot, value } => Message::Decide {
                    key: key as u64,
                    ballot: host::Ballot::from_spec(ballot),
                    value: value as Value,
                },
            }
        }

        pub open spec fn into_spec(&self) -> LowMessage {
            match(self) {
                Message::Prepare { key, ballot } => LowMessage::Prepare {
                    key: key as nat,
                    ballot: ballot.into_spec(),
                },
                Message::Promise { key, sender, ballot, accepted } => LowMessage::Promise {
                    key: key as nat,
                    sender: sender as nat,
                    ballot: ballot.into_spec(),
                    accepted: if let Some((ballot, value)) = accepted {
                        Some((ballot.into_spec(), value as SpecValue))
                    } else {
                        None
                    },
                },
                Message::Accept { key, ballot, value } => LowMessage::Accept {
                    key: key as nat,
                    ballot: ballot.into_spec(),
                    value: value as SpecValue,
                },
                Message::Accepted { key, sender, ballot } => LowMessage::Accepted {
                    key: key as nat,
                    sender: sender as nat,
                    ballot: ballot.into_spec(),
                },
                Message::Decide { key, ballot, value } => LowMessage::Decide {
                    key: key as nat,
                    ballot: ballot.into_spec(),
                    value: value as SpecValue,
                },
            }
        }
    }

    pub struct NetworkOperation {
        pub recv: Option<Message>,
        pub send: Option<Message>,
    }

    impl NetworkOperation {
        pub open spec fn into_spec(&self) -> LowNetworkOperation {
            LowNetworkOperation {
                recv: if let Some(recv) = self.recv { Some(recv.into_spec()) } else { None },
                send: if let Some(send) = self.send { Some(send.into_spec()) } else { None },
            }
        }

        pub open spec fn from_messages_as_spec(recv: Option<Message>, send: Option<Message>) -> LowNetworkOperation
        {
            LowNetworkOperation {
                recv: if let Some(recv) = recv { Some(recv.into_spec()) } else { None },
                send: if let Some(send) = send { Some(send.into_spec()) } else { None },
            }
        }

        pub exec fn from_messages(recv: Option<Message>, send: Option<Message>) -> (res: Self)
        ensures
            res.recv == recv,
            res.send == send,
        {
            Self { recv, send }
        }
    }

    pub struct Constants {
        pub num_failures: usize,
        pub num_hosts: usize,
        pub hosts: Vec<host::Constants>,
        pub network: network::Constants,
    }

    pub struct Variables {
        pub hosts: Vec<host::Variables>,
        pub network: network::Variables,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.num_hosts > 0
            &&& self.num_failures > 0
            &&& self.num_hosts == ((2 * self.num_failures) + 1)
            &&& self.hosts.len() == self.num_hosts
            &&& forall |i: usize| #![auto]
                    0 <= i < self.num_hosts ==>
                    self.hosts[i as int].id == i &&
                    self.hosts[i as int].num_failures == self.num_failures
        }

        pub open spec fn into_spec(&self) -> LowConstants {
            LowConstants {
                num_failures: self.num_failures as nat,
                num_hosts: self.num_hosts as nat,
                hosts: self.hosts@.map(|i: int, c: host::Constants| c.into_spec()),
                network: self.network.into_spec(),
            }
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.hosts.len() == c.hosts.len()
            &&& forall |idx: nat| #![auto] 0 <= idx < self.hosts.len() ==> self.hosts[idx as int].well_formed(&c.hosts[idx as int])
            &&& self.network.well_formed(&c.network)
        }

        pub open spec fn into_spec(&self) -> LowVariables {
            LowVariables {
                hosts: Seq::new(self.hosts@.len(), |i: int| self.hosts@[i].into_spec()),
                network: self.network.into_spec(),
            }
        }

        pub proof fn spec_network_equivalance(&self, other: &Self)
        ensures
            other.network.into_spec() == self.network.into_spec() <==> other.into_spec().network == self.into_spec().network,
        { }

        pub proof fn spec_hosts_equivalance(&self, other: &Self, base: int)
        requires
            0 <= base <= self.hosts.len(),
        ensures
            (
                (other.hosts.len() == self.hosts.len()) &&
                (forall |i: int| #![auto] base <= i < self.hosts.len() ==> other.hosts@[i].into_spec() == self.hosts@[i].into_spec())
            )
            <==>
            (
                (other.into_spec().hosts.len() == self.into_spec().hosts.len()) &&
                (forall |i: int| #![auto] base <= i < self.hosts.len() ==> other.into_spec().hosts[i] == self.into_spec().hosts[i])
            )
        {
            let (other_sepc, self_spec) = (other.into_spec(), self.into_spec());
            assert(other_sepc.hosts.len() == other.hosts.len() && self_spec.hosts.len() == self.hosts.len());
            assert(forall |i: int| #![auto] 0 <= i < other.hosts.len() ==> other_sepc.hosts[i] == other.hosts@[i].into_spec());
            assert(forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self_spec.hosts[i] == self.hosts@[i].into_spec());

            if (
                (other.into_spec().hosts.len() == self.into_spec().hosts.len()) &&
                (forall |i: int| #![auto] base <= i < self.hosts.len() ==> other.into_spec().hosts[i] == self.into_spec().hosts[i])
            ) {
                assert(other.hosts.len() == self.hosts.len());

                assert forall |i: int| #![auto]
                    base <= i < other.hosts.len() implies
                    other.hosts@[i].into_spec() == self.hosts@[i].into_spec()
                by {
                    assert(base <= i < self.hosts.len());
                    assert(self_spec.hosts[i]  == self.hosts@[i].into_spec());
                    assert(other.hosts@[i].into_spec() == self.hosts@[i].into_spec());
                };
            }
        }

        pub proof fn spec_equivalance(&self, other: &Self)
        ensures
            (
                other.network.into_spec() == self.network.into_spec() &&
                other.hosts.len() == self.hosts.len() &&
                (forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> other.hosts@[i].into_spec() == self.hosts@[i].into_spec())
            )
            <==>
            other.into_spec() == self.into_spec(),
        {
            self.spec_network_equivalance(other);
            self.spec_hosts_equivalance(other, 0);

            let (other_sepc, self_spec) = (other.into_spec(), self.into_spec());
            assert(other_sepc.hosts.len() == other.hosts.len() && self_spec.hosts.len() == self.hosts.len());
            assert(forall |i: int| #![auto] 0 <= i < other.hosts.len() ==> other_sepc.hosts[i] == other.hosts@[i].into_spec());
            assert(forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self_spec.hosts[i] == self.hosts@[i].into_spec());

            if (other_sepc == self_spec) {
                assert(other.hosts.len() == self.hosts.len());

                assert forall |i: int| #![auto]
                    0 <= i < other.hosts.len() implies
                    other.hosts@[i].into_spec() == self.hosts@[i].into_spec()
                by {
                    assert(0 <= i < self.hosts.len());
                    assert(self_spec.hosts[i]  == self.hosts@[i].into_spec());
                    assert(other.hosts@[i].into_spec() == self.hosts@[i].into_spec());
                };
            }

            if (
                (other.network.into_spec() == self.network.into_spec()) &&
                (other.hosts.len() == self.hosts.len()) &&
                (forall |i: int| #![auto] 0 <= i < other.hosts.len() ==> other.hosts@[i].into_spec() == self.hosts@[i].into_spec())
            ) {
                assert(other_sepc.hosts.len() == self_spec.hosts.len());
                assert(other_sepc.hosts == self_spec.hosts);
                assert(other_sepc.network == self_spec.network);
                assert(other_sepc == self_spec);
            }
        }
    }

    impl Clone for Variables {
        exec fn clone(&self) -> (clone: Self)
        ensures
            clone.hosts.len() == self.hosts.len(),
            forall |i: int| #![auto] 0 <= i < clone.hosts.len() ==> clone.hosts[i] == self.hosts[i],
            clone.network == self.network,
        {
            Self {
                hosts: self.hosts.clone(),
                network: self.network.clone(),
            }
        }
    }

    pub open spec fn constants_abstraction(c: &Constants) -> LowConstants { c.into_spec() }

    pub open spec fn variables_abstraction(c: &Constants, v: &Variables) -> LowVariables { v.into_spec() }

    impl Constants {
        pub exec fn new(num_failures: usize) -> (res: Self)
        requires
            num_failures > 0,
            ((2 * num_failures) + 1) <= usize::MAX,
        ensures
            res.well_formed(),
            forall |i: usize| #![auto] 0 <= i < res.hosts.len() ==> res.hosts[i as int].well_formed(),
            res.network.well_formed(),
        {
            let num_hosts = ((2 * num_failures) + 1);
            let mut hosts = Vec::<host::Constants>::with_capacity(num_hosts);

            for id in 0..num_hosts
            invariant
                num_failures > 0,
                num_hosts == ((2 * num_failures) + 1),
                hosts.len() == id,
                forall |i: usize| #![auto]
                    0 <= i < id ==>
                    hosts[i as int].id == i &&
                    hosts[i as int].num_hosts == num_hosts &&
                    hosts[i as int].num_failures == num_failures,
            {
                hosts.push(host::Constants::new(id, num_hosts, num_failures));
            }

            Self {
                num_failures,
                num_hosts,
                hosts,
                network: network::Constants::new(),
            }
        }
    }

    impl Variables {
        pub exec fn new(c: &Constants) -> (res: Self)
        requires
            c.well_formed(),
            forall |i: usize| #![auto] 0 <= i < c.hosts.len() ==> c.hosts[i as int].well_formed(),
            c.network.well_formed(),
        ensures
            res.well_formed(c),
            forall |i: usize| #![auto] 0 <= i < res.hosts.len() ==> res.hosts[i as int].current_instance == 0,
            low_init(&constants_abstraction(c), &variables_abstraction(c, &res)),
        {
            let mut hosts: Vec<host::Variables> = Vec::with_capacity(c.num_hosts);

            for id in 0..c.num_hosts
            invariant
                c.well_formed(),
                hosts.len() == id,
                forall |i: usize| #![auto] 0 <= i < c.hosts.len() ==> c.hosts[i as int].well_formed(),
                forall |i: usize| #![auto] 0 <= i < hosts.len() ==> hosts[i as int].current_instance == 0,
                forall |i: usize| #![auto] 0 <= i < hosts.len() ==> hosts[i as int].into_spec().instances =~= Map::empty(),
            {
                hosts.push(host::Variables::new(&c.hosts[id]));
            }

            Self {
               hosts,
               network: network::Variables::new(),
            }
        }

        pub exec fn all_host_next_intance(&mut self, c: &Constants)
        requires ({
            let old_spec = old(self).into_spec();

            &&& old(self).well_formed(c)
            &&& old_spec.well_formed(&c.into_spec())
            &&& forall |i: int| #![auto] 0 <= i < old(self).hosts.len() ==> old(self).hosts[i].current_instance < u64::MAX
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& self.well_formed(c)
            &&& new_spec.well_formed(&c.into_spec())
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance + 1
            &&& new_spec =~= old_spec
        })
        {
            let ghost old_spec = old(self).into_spec();

            for id in iter: 0..self.hosts.len()
            invariant
                iter.end == self.hosts.len(),
                self.well_formed(c),
                self.hosts.len() == old(self).hosts.len(),
                forall |i: int| #![auto] id <= i < self.hosts.len() ==> old(self).hosts@[i].current_instance == self.hosts[i].current_instance && self.hosts[i].current_instance < u64::MAX,
                forall |i: int| #![auto] 0 <= i < id ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance + 1,
                forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].into_spec() == old(self).hosts@[i].into_spec(),
                self.network == old(self).network,
                self.into_spec() =~= old(self).into_spec(),
            {
                let mut new_state = self.hosts[id].clone();
                new_state.next_instance(&c.hosts[id]);
                self.hosts[id] = new_state;
                proof! { self.spec_equivalance(&old(self)); };
            }
        }

        pub exec fn all_host_init_request(&mut self, c: &Constants)
        requires ({
            let old_spec = old(self).into_spec();

            &&& old(self).well_formed(c)
            &&& low_inductive(&c.into_spec(), &old_spec)
            &&& forall |i: int| #![auto] 0 <= i < old_spec.hosts.len() ==> !old_spec.hosts[i].instances.contains_key(old(self).hosts[i].current_instance as nat)
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& self.well_formed(c)
            &&& low_inductive(&c.into_spec(), &new_spec)
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance
            &&& forall |i: int| #![auto]
                    0 <= i < self.hosts.len() ==>
                    low_init_request(&c.into_spec().hosts[i], &old(self).into_spec().hosts[i], &self.into_spec().hosts[i], self.hosts@[i].current_instance as nat, NetworkOperation::from_messages_as_spec(None, None))
            &&& new_spec.network =~= old_spec.network
        })
        {
            let ghost mut prev_spec = old(self).into_spec();
            let ghost mut send_messages_spec: Seq<LowMessage> = Seq::empty();

            proof! { assert(forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> !self.into_spec().hosts[i].instances.contains_key(self.hosts@[i].current_instance as nat)); };

            for id in iter: 0..self.hosts.len()
            invariant
                iter.end == self.hosts.len(),
                self.well_formed(c),
                self.hosts.len() == old(self).hosts.len(),
                forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance,
                forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.into_spec().hosts[i].well_formed(&c.into_spec().hosts[i]),
                forall |i: int| #![auto] id <= i < self.hosts.len() ==> !self.into_spec().hosts[i].instances.contains_key(self.hosts@[i].current_instance as nat),
                forall |i: int| #![auto] id <= i < self.hosts.len() ==> old(self).into_spec().hosts[i] == self.hosts@[i].into_spec(),
                forall |i: int| #![auto] 0 <= i < id ==> low_init_request(&c.into_spec().hosts[i], &old(self).into_spec().hosts[i], &self.into_spec().hosts[i], self.hosts@[i].current_instance as nat, NetworkOperation::from_messages_as_spec(None, None)),
                self.into_spec().network =~= old(self).into_spec().network,
                low_inductive(&c.into_spec(), &self.into_spec()),
                prev_spec =~= self.into_spec(),
            {
                let mut new_state = self.hosts[id].clone();
                let ghost prev_host_state_spec = new_state.into_spec();
                proof! {
                    assert(new_state.into_spec().well_formed(&c.into_spec().hosts[id as int]));
                    assert(!new_state.into_spec().instances.contains_key(self.hosts@[id as int].current_instance as nat));
                };
                let send = new_state.init_request(&c.hosts[id], None);
                let net_op = NetworkOperation::from_messages(None, send);
                proof! {
                    assert(send.is_none());
                    assert(low_init_request(&c.into_spec().hosts[id as int], &prev_host_state_spec, &new_state.into_spec(), self.hosts@[id as int].current_instance as nat, net_op.into_spec()));
                    assert(old(self).into_spec().hosts[id as int] == prev_host_state_spec);
                };

                self.hosts[id] = new_state;
                proof! {
                    assert(low_init_request(&c.into_spec().hosts[id as int], &old(self).into_spec().hosts[id as int], &self.into_spec().hosts[id as int], self.hosts@[id as int].current_instance as nat, net_op.into_spec()));
                };

                proof! {
                    assert(low_host_step(&c.into_spec(), &prev_spec, &self.into_spec(), id as int, self.hosts@[id as int].current_instance as nat, net_op.into_spec(), Event::NoOp));
                    assert(is_valid_transition(&c.into_spec(), &prev_spec, &self.into_spec(), Transition::HostStep { host_id: id as int, instance: self.hosts@[id as int].current_instance as nat, net_op: net_op.into_spec() }, Event::NoOp));
                    assert(next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp));
                    refinement_next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp);
                    assert(low_inductive(&c.into_spec(), &self.into_spec()));
                    prev_spec = self.into_spec();
                };
            }
        }

        pub exec fn host_send_prepare(&mut self, c: &Constants, host_id: usize) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let i = host_id as int;

            &&& old(self).well_formed(c)
            &&& low_inductive(&c.into_spec(), &old_spec)
            &&& 0 <= host_id < old_spec.hosts.len()
            &&& old_spec.hosts[i].instances.contains_key(old(self).hosts[i].current_instance as nat)
            &&& old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].current_ballot.num < u64::MAX
            &&& !old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].promised.contains_key(LowBallot { num: old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].current_ballot.num + 1, pid: host_id as nat, })
            &&& !old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].proposed_value.contains_key(LowBallot { num: old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].current_ballot.num + 1, pid: host_id as nat, })
            &&& !old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].accepted.contains_key(LowBallot { num: old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].current_ballot.num + 1, pid: host_id as nat, })
            &&& old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].decide_value.is_none()
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& self.well_formed(c)
            &&& low_inductive(&c.into_spec(), &new_spec)
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() && i != host_id ==> new_spec.hosts[i] == old_spec.hosts[i]
            &&& low_send_prepare(&c.into_spec().hosts[host_id as int], &old_spec.hosts[host_id as int], &new_spec.hosts[host_id as int], self.hosts@[host_id as int].current_instance as nat, NetworkOperation::from_messages_as_spec(None, send))
            &&& send == Some(Message::Prepare { key: self.hosts@[host_id as int].current_instance, ballot: host::Ballot { num: (new_spec.hosts[host_id as int].instances[self.hosts@[host_id as int].current_instance as nat].current_ballot.num + 1) as u64, pid: c.hosts@[host_id as int].id } })
            &&& new_spec.network.in_flight_messages =~= old_spec.network.in_flight_messages.insert(send.unwrap().into_spec())
        })
        {
            let ghost prev_spec = self.into_spec();

            let mut new_state = self.hosts[host_id].clone();
            let ghost prev_host_state_spec = new_state.into_spec();
            proof! {
                assert(new_state.into_spec().well_formed(&c.into_spec().hosts[host_id as int]));
                assert(new_state.into_spec().instances.contains_key(self.hosts@[host_id as int].current_instance as nat));
            };

            let send = new_state.send_prepare(&c.hosts[host_id], None);
            let net_op = NetworkOperation::from_messages(None, send);
            self.network.step(&c.network, &net_op);
            proof! {
                assert(send.is_some());
                assert(low_send_prepare(&c.into_spec().hosts[host_id as int], &prev_host_state_spec, &new_state.into_spec(), self.hosts@[host_id as int].current_instance as nat, net_op.into_spec()));
                assert(old(self).into_spec().hosts[host_id as int] == prev_host_state_spec);
            };

            self.hosts[host_id] = new_state;
            proof! {
                assert(low_send_prepare(&c.into_spec().hosts[host_id as int], &old(self).into_spec().hosts[host_id as int], &self.into_spec().hosts[host_id as int], self.hosts@[host_id as int].current_instance as nat, net_op.into_spec()));
            };

            proof! {
                assert(low_host_step(&c.into_spec(), &prev_spec, &self.into_spec(), host_id as int, self.hosts@[host_id as int].current_instance as nat, net_op.into_spec(), Event::NoOp));
                assert(is_valid_transition(&c.into_spec(), &prev_spec, &self.into_spec(), Transition::HostStep { host_id: host_id as int, instance: self.hosts@[host_id as int].current_instance as nat, net_op: net_op.into_spec() }, Event::NoOp));
                assert(next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp));
                refinement_next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp);
                assert(low_inductive(&c.into_spec(), &self.into_spec()));
                prev_spec = self.into_spec();
            };

            net_op.send
        }

        pub exec fn all_host_promise(&mut self, c: &Constants, prepare_message: Message) -> (send_messages: Option<Vec<Option<Message>>>)
        requires ({
            let old_spec = old(self).into_spec();

            &&& old(self).well_formed(c)
            &&& low_inductive(&c.into_spec(), &old_spec)
            &&& prepare_message is Prepare
            &&& old_spec.network.in_flight_messages.contains(prepare_message.into_spec())
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
            let (key, ballot) = (prepare_message->Prepare_key as nat, prepare_message->Prepare_ballot.into_spec());

            &&& self.well_formed(c)
            &&& low_inductive(&c.into_spec(), &new_spec)
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance
            &&& forall |i: int, instance: nat| #![auto] 0 <= i < self.hosts.len() ==> self.into_spec().hosts[i].instances.contains_key(instance) == old(self).into_spec().hosts[i].instances.contains_key(instance)
            &&& forall |i: int| #![auto]
                    0 <= i < send_messages.unwrap().len() &&
                    (
                        old(self).hosts@[i].current_instance != key ||
                        !old_spec.hosts[i].instances.contains_key(key) ||
                        ballot.cmp(&old_spec.hosts[i].instances[key].current_ballot) != 1
                    ) ==>
                    send_messages.unwrap()@[i].is_none() && new_spec.hosts[i] == old_spec.hosts[i]
            &&& forall |i: int| #![auto]
                    0 <= i < send_messages.unwrap().len() &&
                    old(self).hosts@[i].current_instance == key &&
                    old_spec.hosts[i].instances.contains_key(key) &&
                    ballot.cmp(&old_spec.hosts[i].instances[key].current_ballot) == 1 ==>
                    send_messages.unwrap()@[i].is_some() &&
                    low_promise(&c.into_spec().hosts[i], &old_spec.hosts[i], &new_spec.hosts[i], key as nat, NetworkOperation::from_messages_as_spec(Some(prepare_message), send_messages.unwrap()@[i]))
            &&& send_messages.is_some()
            &&& send_messages.unwrap().len() == self.hosts.len()
            &&& forall |i: int| #![auto] 0 <= i < send_messages.unwrap().len() && send_messages.unwrap()@[i].is_some() ==> new_spec.network.in_flight_messages.contains(send_messages.unwrap()@[i].unwrap().into_spec())
        })
        {
            proof! { assert(forall |i: int, key: nat| #![auto] 0 <= i < self.hosts.len() && self.into_spec().hosts[i].instances.contains_key(key) ==> self.into_spec().accept_ballot_some_eq_accept_value_some(i, key)); };

            if let Message::Prepare { key, ballot } = &prepare_message {
                proof! { assert(prepare_message->Prepare_ballot == ballot); };
                let ghost mut prev_spec = old(self).into_spec();

                let mut send_messages: Vec<Option<Message>> = Vec::with_capacity(self.hosts.len());
                let ghost mut send_messages_spec: Seq<Option<LowMessage>> = Seq::empty();

                proof! {assert(send_messages_spec == Seq::new(send_messages.len() as nat, |i: int| if let Some(msg) = send_messages@[i] { Some(msg.into_spec()) } else { None })); };

                for id in iter: 0..self.hosts.len()
                invariant
                    iter.end == self.hosts.len(),
                    self.well_formed(c),
                    self.hosts.len() == old(self).hosts.len(),
                    forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.into_spec().hosts[i].well_formed(&c.into_spec().hosts[i]),
                    forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance,
                    prepare_message is Prepare && prepare_message->Prepare_ballot == ballot && prepare_message->Prepare_key == key && self.network.in_flight_messages@.contains(prepare_message),
                    forall |i: int| #![auto] id <= i < self.hosts.len() ==> old(self).into_spec().hosts[i] == self.hosts@[i].into_spec(),
                    forall |i: int, key: nat| #![auto] 0 <= i < self.hosts.len() && self.into_spec().hosts[i].instances.contains_key(key) ==> self.into_spec().accept_ballot_some_eq_accept_value_some(i, key),
                    forall |i: int| #![auto]
                        0 <= i < send_messages.len() &&
                        (
                            self.hosts@[i].current_instance != *key ||
                            !self.into_spec().hosts[i].instances.contains_key(*key as nat) ||
                            ballot.into_spec().cmp(&old(self).into_spec().hosts[i].instances[*key as nat].current_ballot) != 1
                        ) ==>
                        send_messages@[i].is_none() && self.into_spec().hosts[i] == old(self).into_spec().hosts[i],
                    forall |i: int| #![auto]
                        0 <= i < send_messages.len() &&
                        self.hosts@[i].current_instance == *key &&
                        self.into_spec().hosts[i].instances.contains_key(*key as nat) &&
                        ballot.into_spec().cmp(&old(self).into_spec().hosts[i].instances[*key as nat].current_ballot) == 1 ==>
                        send_messages@[i].is_some() &&
                        low_promise(&c.into_spec().hosts[i], &old(self).into_spec().hosts[i], &self.into_spec().hosts[i], key as nat, NetworkOperation::from_messages_as_spec(Some(prepare_message), send_messages@[i])),
                    send_messages.len() == id,
                    send_messages_spec.len() == send_messages.len(),
                    send_messages_spec == Seq::new(send_messages.len() as nat, |i: int| if let Some(msg) = send_messages@[i] { Some(msg.into_spec()) } else { None }),
                    forall |i: int| #![auto] 0 <= i < send_messages.len() && send_messages@[i].is_some() ==> self.into_spec().network.in_flight_messages.contains(send_messages@[i].unwrap().into_spec()),
                    low_inductive(&c.into_spec(), &self.into_spec()),
                    prev_spec =~= self.into_spec(),
                {
                    let send_message = if (self.hosts[id].current_instance == *key && self.hosts[id].instances.contains_key(&key) && ballot.cmp(&self.hosts[id].instances.get(&key).unwrap().current_ballot) == 1) {
                        let mut new_state = self.hosts[id].clone();
                        let recv = prepare_message.clone();

                        let ghost prev_host_state_spec = new_state.into_spec();
                        proof! {
                            assert(prev_host_state_spec.well_formed(&c.hosts@[id as int].into_spec()));

                            assert(self.hosts@[id as int].current_instance == key);
                            assert(prev_host_state_spec.instances.contains_key(*key as nat));
                            assert(recv->Prepare_ballot.into_spec().cmp(&prev_host_state_spec.instances[*key as nat].current_ballot) == 1);

                            assert(prev_spec.accept_ballot_some_eq_accept_value_some(id as int, *key as nat));
                        };

                        let send = new_state.promise(&c.hosts[id], Some(recv.clone()));
                        let net_op = NetworkOperation::from_messages(Some(recv), send);
                        self.network.step(&c.network, &net_op);
                        proof! {
                            let accepted = if (prev_host_state_spec.instances[*key as nat].accept_ballot.is_some()) {
                                let accept_ballot = host::Ballot::from_spec(prev_host_state_spec.instances[*key as nat].accept_ballot.unwrap());
                                let accept_value = prev_host_state_spec.instances[*key as nat].accept_value.unwrap() as Value;
                                Some((accept_ballot, accept_value))
                            } else {
                                None
                            };
                            assert(send == Some(Message::Promise { key: *key, sender: id, ballot: *ballot, accepted }));

                            assert(low_promise(&c.into_spec().hosts[id as int], &prev_host_state_spec, &new_state.into_spec(), self.hosts@[id as int].current_instance as nat, net_op.into_spec()));
                            assert(old(self).into_spec().hosts[id as int] == prev_host_state_spec);
                        };

                        self.hosts[id] = new_state;

                        proof! {
                            assert(low_promise(&c.into_spec().hosts[id as int], &prev_spec.hosts[id as int], &self.into_spec().hosts[id as int], *key as nat, net_op.into_spec()));
                            assert(low_host_step(&c.into_spec(), &prev_spec, &self.into_spec(), id as int, *key as nat, net_op.into_spec(), Event::NoOp));
                            assert(is_valid_transition(&c.into_spec(), &prev_spec, &self.into_spec(), Transition::HostStep { host_id: id as int, instance: *key as nat, net_op: net_op.into_spec() }, Event::NoOp));
                            assert(next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp));
                            refinement_next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp);
                            assert(low_inductive(&c.into_spec(), &self.into_spec()));
                        };

                        net_op.send
                    } else {
                        None
                    };

                    send_messages.push(send_message);
                    proof! {
                        send_messages_spec = send_messages_spec.push(if let Some(msg) = send_message { Some(msg.into_spec()) } else { None });
                        assert(send_messages_spec == Seq::new(send_messages.len() as nat, |i: int| if let Some(msg) = send_messages@[i] { Some(msg.into_spec()) } else { None }));
                        prev_spec = self.into_spec();
                    };
                }

                Some(send_messages)
            } else {
                proof! { assert(false); };
                None
            }

        }

        pub exec fn host_promised(&mut self, c: &Constants, host_id: usize, promise_message: Message) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let i = host_id as int;

            &&& old(self).well_formed(c)
            &&& low_inductive(&c.into_spec(), &old_spec)
            &&& 0 <= host_id < old_spec.hosts.len()
            &&& promise_message is Promise
            &&& old_spec.network.in_flight_messages.contains(promise_message.into_spec())
            &&& old(self).hosts@[i].current_instance == promise_message->Promise_key
            &&& old_spec.hosts[i].instances.contains_key(old(self).hosts@[i].current_instance as nat)
            &&& old_spec.hosts[i].instances[promise_message->Promise_key as nat].promised.contains_key(promise_message->Promise_ballot.into_spec())
            &&& !old_spec.hosts[i].instances[promise_message->Promise_key as nat].proposed_value.contains_key(promise_message->Promise_ballot.into_spec())
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& self.well_formed(c)
            &&& low_inductive(&c.into_spec(), &new_spec)
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() && i != host_id ==> new_spec.hosts[i] == old_spec.hosts[i]
            &&& low_promised(&c.into_spec().hosts[host_id as int], &old_spec.hosts[host_id as int], &new_spec.hosts[host_id as int], self.hosts@[host_id as int].current_instance as nat, NetworkOperation::from_messages_as_spec(Some(promise_message), send))
            &&& send.is_none()
            &&& new_spec.network.in_flight_messages =~= old_spec.network.in_flight_messages
        })
        {
            let ghost prev_spec = self.into_spec();

            let mut new_state = self.hosts[host_id].clone();
            let ghost prev_host_state_spec = new_state.into_spec();
            proof! {
                assert(new_state.into_spec().well_formed(&c.into_spec().hosts[host_id as int]));
                assert(new_state.into_spec().instances.contains_key(self.hosts@[host_id as int].current_instance as nat));
            };

            let send = new_state.promised(&c.hosts[host_id], Some(promise_message.clone()));
            let net_op = NetworkOperation::from_messages(Some(promise_message), send);
            proof! {
                assert(send.is_none());
                assert(low_promised(&c.into_spec().hosts[host_id as int], &prev_host_state_spec, &new_state.into_spec(), self.hosts@[host_id as int].current_instance as nat, net_op.into_spec()));
                assert(old(self).into_spec().hosts[host_id as int] == prev_host_state_spec);
            };

            self.hosts[host_id] = new_state;
            proof! {
                assert(low_promised(&c.into_spec().hosts[host_id as int], &old(self).into_spec().hosts[host_id as int], &self.into_spec().hosts[host_id as int], self.hosts@[host_id as int].current_instance as nat, net_op.into_spec()));
            };

            proof! {
                assert(low_host_step(&c.into_spec(), &prev_spec, &self.into_spec(), host_id as int, self.hosts@[host_id as int].current_instance as nat, net_op.into_spec(), Event::NoOp));
                assert(is_valid_transition(&c.into_spec(), &prev_spec, &self.into_spec(), Transition::HostStep { host_id: host_id as int, instance: self.hosts@[host_id as int].current_instance as nat, net_op: net_op.into_spec() }, Event::NoOp));
                assert(next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp));
                refinement_next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp);
                assert(low_inductive(&c.into_spec(), &self.into_spec()));
                prev_spec = self.into_spec();
            };

            net_op.send
        }

        pub exec fn host_send_accept(&mut self, c: &Constants, host_id: usize) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let i = host_id as int;

            &&& old(self).well_formed(c)
            &&& low_inductive(&c.into_spec(), &old_spec)
            &&& 0 <= host_id < old_spec.hosts.len()
            &&& old_spec.hosts[i].instances.contains_key(old(self).hosts[i].current_instance as nat)
            &&& old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].promised.contains_key(old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].current_ballot)
            &&& old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].promised[old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].current_ballot].len() > c.num_failures
            &&& !old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].proposed_value.contains_key(old_spec.hosts[i].instances[old(self).hosts[i].current_instance as nat].current_ballot)
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& self.well_formed(c)
            &&& low_inductive(&c.into_spec(), &new_spec)
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts@[i].current_instance == old(self).hosts@[i].current_instance
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() && i != host_id ==> new_spec.hosts[i] == old_spec.hosts[i]
            &&& low_send_accept(&c.into_spec().hosts[host_id as int], &old_spec.hosts[host_id as int], &new_spec.hosts[host_id as int], self.hosts@[host_id as int].current_instance as nat, NetworkOperation::from_messages_as_spec(None, send))
            &&& send == Some(Message::Accept {
                    key: self.hosts@[host_id as int].current_instance,
                    ballot: self.hosts@[host_id as int].instances@[self.hosts@[host_id as int].current_instance].current_ballot,
                    value: self.hosts@[host_id as int].instances@[self.hosts@[host_id as int].current_instance].proposed_value@[self.hosts@[host_id as int].instances@[self.hosts@[host_id as int].current_instance].current_ballot]
                })
            &&& new_spec.network.in_flight_messages =~= old_spec.network.in_flight_messages.insert(send.unwrap().into_spec())
        })
        {
            let ghost prev_spec = self.into_spec();

            let mut new_state = self.hosts[host_id].clone();
            let ghost prev_host_state_spec = new_state.into_spec();
            proof! {
                assert(new_state.into_spec().well_formed(&c.into_spec().hosts[host_id as int]));
                assert(new_state.into_spec().instances.contains_key(self.hosts@[host_id as int].current_instance as nat));
            };

            let send = new_state.send_accept(&c.hosts[host_id], None);
            let net_op = NetworkOperation::from_messages(None, send);
            self.network.step(&c.network, &net_op);
            proof! {
                assert(send.is_some());
                assert(low_send_accept(&c.into_spec().hosts[host_id as int], &prev_host_state_spec, &new_state.into_spec(), self.hosts@[host_id as int].current_instance as nat, net_op.into_spec()));
                assert(old(self).into_spec().hosts[host_id as int] == prev_host_state_spec);
            };

            self.hosts[host_id] = new_state;
            proof! {
                assert(low_send_accept(&c.into_spec().hosts[host_id as int], &old(self).into_spec().hosts[host_id as int], &self.into_spec().hosts[host_id as int], self.hosts@[host_id as int].current_instance as nat, net_op.into_spec()));
            };

            proof! {
                assert(low_host_step(&c.into_spec(), &prev_spec, &self.into_spec(), host_id as int, self.hosts@[host_id as int].current_instance as nat, net_op.into_spec(), Event::NoOp));
                assert(is_valid_transition(&c.into_spec(), &prev_spec, &self.into_spec(), Transition::HostStep { host_id: host_id as int, instance: self.hosts@[host_id as int].current_instance as nat, net_op: net_op.into_spec() }, Event::NoOp));
                assert(next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp));
                refinement_next(&c.into_spec(), &prev_spec, &self.into_spec(), Event::NoOp);
                assert(low_inductive(&c.into_spec(), &self.into_spec()));
                prev_spec = self.into_spec();
            };

            net_op.send
        }
    }
}
