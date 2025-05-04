use super::Value;
use crate::distributed_system::{
    low_level::host::{
        Ballot as LowBallot, Constants as LowConstants, Instance as LowInstance,
        Variables as LowVariables,
    },
    Value as SpecValue,
};
use std::collections::{HashMap, HashSet};
use vstd::prelude::*;

verus! {
    pub struct Ballot {
        pub num: u64,
        pub pid: usize,
    }

    impl Ballot {
        pub open spec fn into_spec(&self) -> LowBallot {
            LowBallot { num: self.num as nat, pid: self.pid as nat }
        }
    }

    pub struct Constants {
        pub id: usize,
        pub num_hosts: usize,
        pub num_failures: usize,
    }

    pub struct Instance {
        pub current_ballot: Ballot,
        pub promised: HashMap<Ballot, HashMap<usize, Option<(Ballot, Value)>>>,
        pub proposed_value: HashMap<Ballot, Value>,
        pub accepted: HashMap<Ballot, HashSet<usize>>,
        pub accept_ballot: Option<Ballot>,
        pub accept_value: Option<Value>,
        pub decide_value: Option<Value>,
    }

    pub struct Variables {
        pub instances: HashMap<u64, Instance>,
    }

    impl Constants {
        pub open spec fn into_spec(&self) -> LowConstants {
            LowConstants {
                id: self.id as nat,
                num_hosts: self.num_hosts as nat,
                num_failures: self.num_failures as nat,
            }
        }
    }

    impl Instance {
        pub open spec fn into_spec(&self) -> LowInstance {
            LowInstance {
                current_ballot: self.current_ballot.into_spec(),
                promised: self.promised@.dom().fold(
                    Map::empty(),
                    |acc: Map<LowBallot, Map<nat, Option<(LowBallot, SpecValue)>>>, ballot: Ballot| {
                        let promised_map = self.promised@[ballot];
                        acc.insert(ballot.into_spec(), promised_map@.dom().fold(
                            Map::empty(),
                            |acc: Map<nat, Option<(LowBallot, SpecValue)>>, sender: usize| {
                                acc.insert(sender as nat, if let Some((ballot, value)) = promised_map@[sender] { Some((ballot.into_spec(), value as SpecValue)) } else { None })
                            },
                        ))
                    },
                ),
                proposed_value: self.proposed_value@.dom().fold(
                    Map::empty(),
                    |acc: Map<LowBallot, SpecValue>, ballot: Ballot| {
                        acc.insert(ballot.into_spec(), self.proposed_value@[ballot] as SpecValue)
                    },
                ),
                accepted: self.accepted@.dom().fold(
                    Map::empty(),
                    |acc: Map<LowBallot, Set<nat>>, ballot: Ballot| {
                        let sender_set = self.accepted@[ballot];
                        acc.insert(ballot.into_spec(), sender_set@.map(|sender: usize| sender as nat))
                    },
                ),
                accept_ballot: if let Some(ballot) = self.accept_ballot { Some(ballot.into_spec()) } else { None },
                accept_value: if let Some(value) = self.accept_value { Some(value as SpecValue) } else { None },
                decide_value: if let Some(value) = self.decide_value { Some(value as SpecValue) } else { None },
            }
        }
    }

    impl Variables {
        pub open spec fn into_spec(&self) -> LowVariables {
            LowVariables {
                instances: self.instances@
                    .dom()
                    .fold(
                        Map::empty(),
                        |acc: Map<nat, LowInstance>, key: u64| {
                            let instance = self.instances@[key];
                            acc.insert(key as nat, instance.into_spec())
                        },
                    ),
            }
        }
    }
}
