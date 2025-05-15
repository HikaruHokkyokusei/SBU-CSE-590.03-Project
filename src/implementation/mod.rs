use crate::distributed_system::{
    low_level::{
        init as low_init, Constants as LowConstants, Message as LowMessage,
        NetworkOperation as LowNetworkOperation, Variables as LowVariables,
    },
    Value as SpecValue,
};
use vstd::prelude::*;

verus! {
    pub mod host;
    pub mod network;

    type Value = usize;

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
    }
}
