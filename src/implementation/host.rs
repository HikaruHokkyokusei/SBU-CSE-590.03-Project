use super::Value;
use crate::distributed_system::{
    low_level::host::{
        Ballot as LowBallot, Constants as LowConstants, Instance as LowInstance,
        Variables as LowVariables,
    },
    Value as SpecValue,
};
use std::collections::{HashMap, HashSet};
use vstd::{
    prelude::*,
    std_specs::hash::{
        axiom_random_state_builds_valid_hashers, axiom_spec_hash_map_len,
        axiom_u64_obeys_hash_table_key_model,
    },
};

verus! {
    pub assume_specification<K, V, S> [std::collections::HashMap::is_empty] (hash_map: &HashMap<K, V, S>) -> (is_empty: bool)
    ensures
        is_empty == hash_map@.is_empty();
}

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
        pub current_instance: u64,
        pub instances: HashMap<u64, Instance>,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& 0 <= self.id < self.num_hosts
            &&& self.num_hosts > 0
            &&& self.num_failures > 0
            &&& self.num_hosts == ((2 * self.num_failures) + 1)
        }

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
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
        }

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

    impl Constants {
        pub exec fn new(id: usize, num_hosts: usize, num_failures: usize) -> (res: Self)
        requires
            num_failures > 0,
            num_hosts == ((2 * num_failures) + 1),
            0 <= id < num_hosts,
        ensures
            res.id == id,
            res.num_hosts == num_hosts,
            res.num_failures == num_failures,
        {
            Self {
                id,
                num_hosts,
                num_failures,
            }
        }
    }

    impl Variables {
        pub exec fn new(c: &Constants) -> (res: Self)
        requires
            c.well_formed(),
        ensures
            res.well_formed(c),
            res.current_instance == 0,
            res.instances@.is_empty(),
            res.instances.len() == 0,
            res.into_spec().instances.is_empty(),
        {
            let res = Self {
                current_instance: 0,
                instances: HashMap::new(),
            };

            let is_map_empty = res.instances.is_empty();
            let map_size = res.instances.len();

            proof! {
                assert(is_map_empty);
                broadcast use axiom_u64_obeys_hash_table_key_model;
                broadcast use axiom_random_state_builds_valid_hashers;
                broadcast use axiom_spec_hash_map_len;
                assert(map_size == res.instances@.len());
                assert(map_size == 0);
            };

            proof! {
                let spec_var = res.into_spec();
                assert(res.instances@.dom().finite());
                // TODO: Don't assume. Write valid proof.
                // Ref: https://github.com/verus-lang/verus/blob/f894e505a1c89dd36fe9eb01b51dc0b89e29c6a1/source/vstd/set.rs#L426C1-L453C6
                assume(spec_var.instances.dom().finite());
                assume(spec_var.instances.len() == map_size);
            };

            res
        }
    }
}
