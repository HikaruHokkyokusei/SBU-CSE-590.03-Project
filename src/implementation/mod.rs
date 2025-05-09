use crate::distributed_system::{
    low_level::{
        init as low_init, Constants as LowConstants, Message as LowMessage,
        Variables as LowVariables,
    },
    Value as SpecValue,
};
use vstd::prelude::*;

verus! {
    pub mod host;
    pub mod network;

    type Value = usize;

    pub enum Message {
        Prepare { key: u64, ballot: host::Ballot },
        Promise { key: u64, sender: usize, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)> },
        Accept { key: u64, ballot: host::Ballot, value: Value },
        Accepted { key: u64, sender: usize, ballot: host::Ballot },
        Decide { key: u64, ballot: host::Ballot, value: Value },
    }

    impl Message {
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
                hosts: self.hosts@.map(|i: int, v: host::Variables| v.into_spec()),
                network: self.network.into_spec(),
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
            low_init(&constants_abstraction(c), &variables_abstraction(c, &res)),
        {
            let mut hosts: Vec<host::Variables> = Vec::with_capacity(c.num_hosts);

            for id in 0..c.num_hosts
            invariant
                c.well_formed(),
                hosts.len() == id,
                forall |i: usize| #![auto]
                    0 <= i < c.hosts.len() ==>
                    c.hosts[i as int].well_formed(),
                forall |i: usize| #![auto]
                    0 <= i < hosts.len() ==>
                    hosts[i as int].instances@.is_empty() &&
                    hosts[i as int].instances.len() == 0 &&
                    hosts[i as int].into_spec().instances.is_empty(),
            {
                hosts.push(host::Variables::new(&c.hosts[id]));
            }

            Self {
               hosts,
               network: network::Variables::new(),
            }
        }
    }
}
