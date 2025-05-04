use crate::distributed_system::{
    low_level::{Constants as LowConstants, Message as LowMessage, Variables as LowVariables},
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
        pub open spec fn into_spec(&self) -> LowVariables {
            LowVariables {
                hosts: self.hosts@.map(|i: int, v: host::Variables| v.into_spec()),
                network: self.network.into_spec(),
            }
        }
    }

    pub open spec fn constants_abstraction(c: &Constants) -> LowConstants { c.into_spec() }

    pub open spec fn variables_abstraction(c: &Constants, v: &Variables) -> LowVariables { v.into_spec() }
}
