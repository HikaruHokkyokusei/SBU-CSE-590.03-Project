use super::{Message, Value};
use crate::distributed_system::{
    low_level::{
        host::{
            init_request as low_init_request, send_prepare as low_send_prepare,
            Ballot as LowBallot, Constants as LowConstants, Instance as LowInstance,
            Variables as LowVariables,
        },
        NetworkOperation,
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
    pub assume_specification<K, V, S> [std::collections::HashMap::clone] (original: &HashMap<K, V, S>) -> (clone: std::collections::HashMap<K, V, S>)
    where
        K: Clone,
        V: Clone,
        S: Clone,
    ensures
        original == clone;

    pub assume_specification<K, V, S> [std::collections::HashMap::is_empty] (hash_map: &HashMap<K, V, S>) -> (is_empty: bool)
    ensures
        is_empty == hash_map@.is_empty();
}

verus! {
    #[derive(Eq, PartialEq, std::hash::Hash)]
    pub struct Ballot {
        pub num: u64,
        pub pid: usize,
    }

    impl Clone for Ballot {
        fn clone(&self) -> (clone: Self)
        ensures
            self == clone,
        {
            Self {
                num: self.num.clone(),
                pid: self.pid.clone(),
            }
        }
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

    impl Clone for Constants {
        fn clone(&self) -> (clone: Self)
        ensures
            self == clone,
        {
            Self {
                id: self.id.clone(),
                num_hosts: self.num_hosts.clone(),
                num_failures: self.num_failures.clone()
            }
        }
    }

    impl Clone for Instance {
        exec fn clone(&self) -> (clone: Self)
        ensures
            self == clone,
        {
            Self {
                current_ballot: self.current_ballot.clone(),
                promised: self.promised.clone(),
                proposed_value: self.proposed_value.clone(),
                accepted: self.accepted.clone(),
                accept_ballot: self.accept_ballot.clone(),
                accept_value: self.accept_value.clone(),
                decide_value: self.decide_value.clone(),
            }
        }
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

    impl Instance {
        pub exec fn new() -> (res: Instance)
        ensures
            (res.into_spec() == LowInstance {
                current_ballot: LowBallot { num: 0, pid: 0 },
                promised: Map::empty(),
                proposed_value: Map::empty(),
                accepted: Map::empty(),
                accept_ballot: None,
                accept_value: None,
                decide_value: None,
            })
        {
            let res = Instance {
                current_ballot: Ballot { num: 0, pid: 0 },
                promised: HashMap::new(),
                proposed_value: HashMap::new(),
                accepted: HashMap::new(),
                accept_ballot: None,
                accept_value: None,
                decide_value: None,
            };

            proof! {
                let instance_spec = res.into_spec();

                // TODO: Don't assume. Write valid proof.
                assume(instance_spec.promised =~= Map::empty());
                assume(instance_spec.proposed_value =~= Map::empty());
                assume(instance_spec.accepted =~= Map::empty());
            };

            res
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

    impl Variables {
        pub open spec fn net_op(recv: Option<Message>, send: Option<Message>) -> NetworkOperation {
            NetworkOperation {
                recv: if let Some(recv) = recv { Some(recv.into_spec()) } else { None },
                send: if let Some(send) = send { Some(send.into_spec()) } else { None },
            }
        }

        pub exec fn next_instance(&mut self, c: &Constants)
        requires ({
            &&& old(self).current_instance + 1 <= u64::MAX
        }),
        ensures ({
            &&& self == Variables { current_instance: (old(self).current_instance + 1) as u64, instances: old(self).instances }
            &&& self.into_spec() == old(self).into_spec()
        }),
        {
            self.current_instance = self.current_instance + 1;
        }

        pub exec fn init_request(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();

            &&& old_spec.well_formed(&c.into_spec())
            &&& !old_spec.instances.contains_key(old(self).current_instance as nat)
            &&& recv.is_none()
        }),
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send.is_none()
            &&& low_init_request(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        }),
        {
            let new_instance = Instance::new();
            self.instances.insert(self.current_instance, new_instance);

            proof! {
                let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

                // TODO: Don't assume. Write valid proof.
                assume(new_spec.instances == old_spec.instances.insert(self.current_instance as nat, new_instance.into_spec()));
            };

            None
        }

        pub exec fn send_prepare(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& old_spec.instances.contains_key(key)
            &&& old_spec.instances[key].current_ballot.num < u64::MAX
            &&& !old_spec.instances[key].promised.contains_key(LowBallot { num: old_spec.instances[key].current_ballot.num + 1, pid: c.id as nat, })
            &&& !old_spec.instances[key].proposed_value.contains_key(LowBallot { num: old_spec.instances[key].current_ballot.num + 1, pid: c.id as nat, })
            &&& !old_spec.instances[key].accepted.contains_key(LowBallot { num: old_spec.instances[key].current_ballot.num + 1, pid: c.id as nat, })
            &&& old_spec.instances[key].decide_value.is_none()
            &&& recv.is_none()
        }),
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
            let key = self.current_instance as nat;
            let new_ballot = Ballot { num: (new_spec.instances[key].current_ballot.num + 1) as u64, pid: c.id, };

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send == Some(Message::Prepare { key: self.current_instance, ballot: new_ballot })
            &&& low_send_prepare(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        }),
        {
            let current_instance = self.instances.get(&self.current_instance);
            // TODO: Don't assume. Write valid proof.
            proof! { assume(current_instance.is_some()); }; // Corresponds: old_spec.instances.contains_key(key)
            let current_instance = current_instance.unwrap();

            // TODO: Don't assume. Write valid proof.
            proof! { assume(current_instance.current_ballot.num == old(self).into_spec().instances[self.current_instance as nat].current_ballot.num); }; // Corresponds: old_spec.instances[key].current_ballot.num < u64::MAX
            let new_ballot = Ballot { num: current_instance.current_ballot.num + 1, pid: c.id, };

            let mut updated_instance = current_instance.clone();
            updated_instance.promised.insert(new_ballot.clone(), HashMap::new());
            updated_instance.accepted.insert(new_ballot.clone(), HashSet::new());

            self.instances.insert(self.current_instance, updated_instance);

            proof! {
                let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
                let key = self.current_instance as nat;
                let new_ballot_spec = new_ballot.into_spec();

                // TODO: Don't assume. Write valid proof.
                assume(new_spec.instances == old_spec.instances.insert(key, LowInstance {
                    current_ballot: old_spec.instances[key].current_ballot,
                    promised: old_spec.instances[key].promised.insert(new_ballot_spec, Map::empty()),
                    proposed_value: old_spec.instances[key].proposed_value,
                    accepted: old_spec.instances[key].accepted.insert(new_ballot_spec, Set::empty()),
                    accept_ballot: old_spec.instances[key].accept_ballot,
                    accept_value: old_spec.instances[key].accept_value,
                    decide_value: old_spec.instances[key].decide_value,
                }));
            };

            Some(Message::Prepare { key: self.current_instance, ballot: new_ballot })
        }
    }
}
