use super::{Message, Value};
use crate::distributed_system::{
    low_level::{
        host::{
            accept as low_accept, accepted as low_accepted, decide as low_decide,
            get_max_accepted_value as low_get_max_accepted_value, init_request as low_init_request,
            max_accepted_value_by_ballot as low_max_accepted_value_by_ballot,
            promise as low_promise, promised as low_promised, send_accept as low_send_accept,
            send_decide as low_send_decide, send_prepare as low_send_prepare, Ballot as LowBallot,
            Constants as LowConstants, Instance as LowInstance, Variables as LowVariables,
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
        axiom_u64_obeys_hash_table_key_model, group_hash_axioms, obeys_key_model,
    },
};

verus! {
    pub assume_specification<K, S> [std::collections::HashSet::clone] (original: &HashSet<K, S>) -> (clone: std::collections::HashSet<K, S>)
    where
        K: Clone,
        S: Clone,
    ensures
        original == clone;

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

        pub open spec fn valid_spec(ballot: LowBallot) -> bool {
            &&& ballot.num <= u64::MAX
            &&& ballot.pid <= usize::MAX
        }

        pub open spec fn from_spec(spec_ballot: LowBallot) -> (res: Self)
        recommends
            Ballot::valid_spec(spec_ballot),
        {
            Self {
                num: spec_ballot.num as u64,
                pid: spec_ballot.pid as usize,
            }
        }

        pub exec fn cmp(&self, other: &Ballot) -> (res: i8)
        ensures
            res == self.into_spec().cmp(&other.into_spec()),
        {
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
                promised: Map::new(
                    |ballot: LowBallot| Ballot::valid_spec(ballot) && self.promised@.contains_key(Ballot::from_spec(ballot)),
                    |ballot: LowBallot| Map::new(
                        |sender: nat| sender <= usize::MAX && self.promised@[Ballot::from_spec(ballot)]@.contains_key(sender as usize),
                        |sender: nat| if let Some((ballot, value)) = self.promised@[Ballot::from_spec(ballot)]@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
                    ),
                ),
                proposed_value: Map::new(
                    |ballot: LowBallot| Ballot::valid_spec(ballot) && self.proposed_value@.contains_key(Ballot::from_spec(ballot)),
                    |ballot: LowBallot| self.proposed_value@[Ballot::from_spec(ballot)] as SpecValue,
                ),
                accepted: Map::new(
                    |ballot: LowBallot| Ballot::valid_spec(ballot) && self.accepted@.contains_key(Ballot::from_spec(ballot)),
                    |ballot: LowBallot| Set::new(|sender: nat| sender <= usize::MAX && self.accepted@[Ballot::from_spec(ballot)]@.contains(sender as usize)),
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
                instances: Map::new(
                    |instance: nat| instance <= u64::MAX && self.instances@.contains_key(instance as u64),
                    |instance: nat| self.instances@[instance as u64].into_spec(),
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

    pub proof fn axiom_ballot_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<Ballot>(),
    { admit(); }

    impl Instance {
        pub exec fn new() -> (res: Self)
        ensures ({
            let res = res.into_spec();

            &&& res.current_ballot == LowBallot { num: 0, pid: 0 }
            &&& res.promised =~= Map::empty()
            &&& res.proposed_value =~= Map::empty()
            &&& res.accepted =~= Map::empty()
            &&& res.accept_ballot.is_none()
            &&& res.accept_value.is_none()
            &&& res.decide_value.is_none()
        })
        {
            Self {
                current_ballot: Ballot { num: 0, pid: 0 },
                promised: HashMap::new(),
                proposed_value: HashMap::new(),
                accepted: HashMap::new(),
                accept_ballot: None,
                accept_value: None,
                decide_value: None,
            }
        }

        pub exec fn fill_promised(&mut self, key: Ballot, value: HashMap<usize, Option<(Ballot, Value)>>)
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec =~= LowInstance {
                    current_ballot: old_spec.current_ballot,
                    promised: old_spec.promised.insert(key.into_spec(), Map::new(
                        |sender: nat| sender <= usize::MAX && value@.contains_key(sender as usize),
                        |sender: nat| if let Some((ballot, value)) = value@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
                    )),
                    proposed_value: old_spec.proposed_value,
                    accepted: old_spec.accepted,
                    accept_ballot: old_spec.accept_ballot,
                    accept_value: old_spec.accept_value,
                    decide_value: old_spec.decide_value,
                }
            &&& self.promised@ =~= old(self).promised@.insert(key, value)
        })
        {
            self.promised.insert(key, value);

            proof! {
                axiom_ballot_obeys_hash_table_key_model();
                broadcast use axiom_random_state_builds_valid_hashers;

                let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
                assert(new_spec.promised =~= old_spec.promised.insert(key.into_spec(), Map::new(
                    |sender: nat| sender <= usize::MAX && value@.contains_key(sender as usize),
                    |sender: nat| if let Some((ballot, value)) = value@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
                )));
            };
        }

        pub exec fn fill_proposed_value(&mut self, key: Ballot, value: Value)
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec =~= LowInstance {
                    current_ballot: old_spec.current_ballot,
                    promised: old_spec.promised,
                    proposed_value: old_spec.proposed_value.insert(key.into_spec(), value as SpecValue),
                    accepted: old_spec.accepted,
                    accept_ballot: old_spec.accept_ballot,
                    accept_value: old_spec.accept_value,
                    decide_value: old_spec.decide_value,
                }
            &&& self.proposed_value@ =~= self.proposed_value@.insert(key, value)
        })
        {
            self.proposed_value.insert(key, value);

            proof! {
                axiom_ballot_obeys_hash_table_key_model();
                broadcast use axiom_random_state_builds_valid_hashers;

                let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
                assert(new_spec.proposed_value =~= old_spec.proposed_value.insert(key.into_spec(), value as SpecValue));
            };
        }

        pub exec fn fill_accepted(&mut self, key: Ballot, value: HashSet<usize>)
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec =~= LowInstance {
                    current_ballot: old_spec.current_ballot,
                    promised: old_spec.promised,
                    proposed_value: old_spec.proposed_value,
                    accepted: old_spec.accepted.insert(key.into_spec(), Set::new(
                        |sender: nat| sender <= usize::MAX && value@.contains(sender as usize)
                    )),
                    accept_ballot: old_spec.accept_ballot,
                    accept_value: old_spec.accept_value,
                    decide_value: old_spec.decide_value,
                }
            &&& self.accepted@ =~= old(self).accepted@.insert(key, value)
        })
        {
            self.accepted.insert(key, value);

            proof! {
                axiom_ballot_obeys_hash_table_key_model();
                broadcast use axiom_random_state_builds_valid_hashers;

                let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
                assert(new_spec.accepted =~= old_spec.accepted.insert(key.into_spec(), Set::new(
                    |sender: nat| sender <= usize::MAX && value@.contains(sender as usize)
                )));
            };
        }
    }

    impl Variables {
        pub exec fn new(c: &Constants) -> (res: Self)
        requires
            c.well_formed(),
        ensures
            res.well_formed(c),
            res.current_instance == 0,
            res.into_spec().instances =~= Map::empty(),
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

            res
        }

        pub exec fn get_current_instance(&self) -> (res: &Instance)
        requires
            self.into_spec().instances.contains_key(self.current_instance as nat),
        ensures
            *res == self.instances@[self.current_instance],
        {
            let current_instance = self.instances.get(&self.current_instance);
            proof! { broadcast use group_hash_axioms; };
            current_instance.unwrap()
        }

        pub exec fn upsert_current_instance(&mut self, instance: Instance)
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& self.current_instance == old(self).current_instance
            &&& new_spec.instances == old_spec.instances.insert(self.current_instance as nat, instance.into_spec())
            &&& self.instances@ =~= old(self).instances@.insert(self.current_instance, instance)
        })
        {
            self.instances.insert(self.current_instance, instance);

            proof! {
                broadcast use axiom_u64_obeys_hash_table_key_model;
                broadcast use axiom_random_state_builds_valid_hashers;

                let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

                assert(self.current_instance == old(self).current_instance);
                assert(new_spec.instances =~= old_spec.instances.insert(self.current_instance as nat, instance.into_spec()));
            };
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
        })
        ensures ({
            &&& self == Variables { current_instance: (old(self).current_instance + 1) as u64, instances: old(self).instances }
            &&& self.into_spec() == old(self).into_spec()
        })
        {
            self.current_instance = self.current_instance + 1;
        }

        pub exec fn init_request(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();

            &&& old_spec.well_formed(&c.into_spec())
            &&& !old_spec.instances.contains_key(old(self).current_instance as nat)
            &&& recv.is_none()
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send.is_none()
            &&& low_init_request(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            self.upsert_current_instance(Instance::new());
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
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
            let key = self.current_instance as nat;
            let new_ballot = Ballot { num: (new_spec.instances[key].current_ballot.num + 1) as u64, pid: c.id, };

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send == Some(Message::Prepare { key: self.current_instance, ballot: new_ballot })
            &&& low_send_prepare(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            let current_instance = self.get_current_instance();
            let new_ballot = Ballot { num: current_instance.current_ballot.num + 1, pid: c.id, };

            let accepted_map = HashMap::<usize, Option<(Ballot, Value)>>::new();
            let acceptor_set = HashSet::<usize>::new();

            proof! {
                let accepted_map_spec = Map::new(
                    |sender: nat| sender <= usize::MAX && accepted_map@.contains_key(sender as usize),
                    |sender: nat| if let Some((ballot, value)) = accepted_map@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
                );

                assert(accepted_map_spec =~= Map::empty());
            };

            let mut updated_instance = current_instance.clone();
            updated_instance.fill_promised(new_ballot.clone(), accepted_map);
            updated_instance.fill_accepted(new_ballot.clone(), acceptor_set);

            self.upsert_current_instance(updated_instance);

            Some(Message::Prepare { key: self.current_instance, ballot: new_ballot })
        }

        pub exec fn promise(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& recv.is_some()
            &&& recv.unwrap() is Prepare
            &&& {
                    let recv = recv.unwrap();
                    let (msg_key, ballot) = (recv->Prepare_key as nat, recv->Prepare_ballot.into_spec());

                    &&& msg_key == key
                    &&& old_spec.instances.contains_key(key)
                    &&& ballot.cmp(&old_spec.instances[key].current_ballot) == 1
                }
            &&& old_spec.instances[key].accept_ballot.is_some() == old_spec.instances[key].accept_value.is_some()
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
            let key = self.current_instance as nat;
            let ballot = Ballot::from_spec(new_spec.instances[key].current_ballot);

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send == if (new_spec.instances[key].accept_ballot.is_some()) {
                    let accept_ballot = Ballot::from_spec(new_spec.instances[key].accept_ballot.unwrap());
                    let accept_value = new_spec.instances[key].accept_value.unwrap() as Value;
                    Some(Message::Promise { key: self.current_instance, sender: c.id, ballot, accepted: Some((accept_ballot, accept_value)), })
                } else {
                    Some(Message::Promise { key: self.current_instance, sender: c.id, ballot, accepted: None, })
                }
            &&& low_promise(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            if let Some(Message::Prepare { key, ballot }) = recv {
                let current_instance = self.get_current_instance();

                let mut updated_instance = current_instance.clone();
                updated_instance.current_ballot = ballot.clone();

                let send_message = if (current_instance.accept_ballot.is_some()) {
                    Some(Message::Promise { key: self.current_instance, sender: c.id, ballot, accepted: Some((current_instance.accept_ballot.as_ref().unwrap().clone(), current_instance.accept_value.unwrap().clone())) })
                } else {
                    Some(Message::Promise { key: self.current_instance, sender: c.id, ballot, accepted: None })
                };

                self.upsert_current_instance(updated_instance);

                send_message
            } else {
                proof! { assert(false); };
                None
            }
        }

        pub exec fn promised(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& recv.is_some()
            &&& recv.unwrap() is Promise
            &&& {
                    let recv = recv.unwrap();
                    let (msg_key, sender, ballot, accepted) = (recv->Promise_key as nat, recv->Promise_sender as nat, recv->Promise_ballot.into_spec(), recv->Promise_accepted);
                    let accepted = if let Some((ballot, value)) = accepted { Some((ballot.into_spec(), value as SpecValue)) } else { None };

                    &&& msg_key == key
                    &&& old_spec.instances.contains_key(key)
                    &&& old_spec.instances[key].promised.contains_key(ballot)
                    &&& !old_spec.instances[key].proposed_value.contains_key(ballot)
                }
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send.is_none()
            &&& low_promised(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            if let Some(Message::Promise { key, sender, ballot, accepted }) = recv {
                let current_instance = self.get_current_instance();

                proof! {
                    axiom_ballot_obeys_hash_table_key_model();
                    broadcast use group_hash_axioms;
                };
                let current_accepted_map = current_instance.promised.get(&ballot).unwrap();
                let mut updated_accepted_map = current_accepted_map.clone();
                updated_accepted_map.insert(sender, accepted);

                proof! {
                    let current_accepted_map_spec = Map::new(
                        |sender: nat| sender <= usize::MAX && current_accepted_map@.contains_key(sender as usize),
                        |sender: nat| if let Some((ballot, value)) = current_accepted_map@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
                    );

                    let updated_accepted_map_spec = Map::new(
                        |sender: nat| sender <= usize::MAX && updated_accepted_map@.contains_key(sender as usize),
                        |sender: nat| if let Some((ballot, value)) = updated_accepted_map@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
                    );

                    assert(updated_accepted_map_spec =~= current_accepted_map_spec.insert(sender as nat, if let Some((ballot, value)) = accepted { Some((ballot.into_spec(), value as SpecValue)) } else { None }));
                };

                let mut updated_instance = current_instance.clone();
                updated_instance.fill_promised(ballot, updated_accepted_map);

                self.upsert_current_instance(updated_instance);
            }

            None
        }

        pub open spec fn max_accepted_value_by_ballot_spec(a: Option<(Ballot, Value)>, b: Option<(Ballot, Value)>) -> Option<(Ballot, Value)> {
            if (a.is_none() && b.is_none()) {
                None
            } else if (a.is_none()) {
                b
            } else if (b.is_none()) {
                a
            } else {
                let (a, b) = (a.unwrap(), b.unwrap());
                if (a.0.into_spec().cmp(&b.0.into_spec()) >= 0) {
                    Some(a)
                } else {
                    Some(b)
                }
            }
        }

        pub exec fn max_accepted_value_by_ballot(a: Option<(Ballot, Value)>, b: Option<(Ballot, Value)>) -> (res: Option<(Ballot, Value)>)
        ensures ({
            let (a_spec, b_spec) = (
                if let Some((ballot, value)) = a { Some((ballot.into_spec(), value as SpecValue)) } else { None },
                if let Some((ballot, value)) = b { Some((ballot.into_spec(), value as SpecValue)) } else { None }
            );

            &&& (if let Some((ballot, value)) = res { Some((ballot.into_spec(), value as SpecValue)) } else { None }) == low_max_accepted_value_by_ballot(a_spec, b_spec)
            &&& res == Variables::max_accepted_value_by_ballot_spec(a, b)
        })
        {
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

        pub exec fn get_max_accepted_value(accepted_map: &HashMap<usize, Option<(Ballot, Value)>>) -> (res: Option<(Ballot, Value)>)
        requires ({
            let accepted_map_spec = Map::new(
                |sender: nat| sender <= usize::MAX && accepted_map@.contains_key(sender as usize),
                |sender: nat| if let Some((ballot, value)) = accepted_map@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
            );

            &&& accepted_map_spec.dom().finite()
        })
        ensures ({
            let accepted_map_spec = Map::new(
                |sender: nat| sender <= usize::MAX && accepted_map@.contains_key(sender as usize),
                |sender: nat| if let Some((ballot, value)) = accepted_map@[sender as usize] { Some((ballot.into_spec(), value as SpecValue)) } else { None },
            );

            &&& if let Some((ballot, value)) = res { Some((ballot.into_spec(), value as SpecValue)) } else { None } == low_get_max_accepted_value(accepted_map_spec)
        })
        {
            // TODO: Don't assume. Add valid proof...
            proof! { assume(false); };
            None // Calculate the correct value before returning...
        }

        pub exec fn send_accept(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& old_spec.instances.contains_key(key)
            &&& old_spec.instances[key].promised.contains_key(old_spec.instances[key].current_ballot)
            &&& old_spec.instances[key].promised[old_spec.instances[key].current_ballot].dom().finite()
            &&& old_spec.instances[key].promised[old_spec.instances[key].current_ballot].len() > c.num_failures
            &&& !old_spec.instances[key].proposed_value.contains_key(old_spec.instances[key].current_ballot)
            &&& recv.is_none()
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send == Some(Message::Accept {
                    key: self.current_instance,
                    ballot: self.instances@[self.current_instance].current_ballot,
                    value: self.instances@[self.current_instance].proposed_value@[self.instances@[self.current_instance].current_ballot]
                })
            &&& low_send_accept(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            let current_instance = self.get_current_instance();
            let ballot = current_instance.current_ballot.clone();

            proof! {
                axiom_ballot_obeys_hash_table_key_model();
                broadcast use group_hash_axioms;
            };
            let accepted_map = current_instance.promised.get(&ballot).unwrap();
            let value_to_propose = if let Some((ballot, value)) = Variables::get_max_accepted_value(accepted_map) { value } else { c.id };

            let mut updated_instance = current_instance.clone();
            updated_instance.fill_proposed_value(ballot.clone(), value_to_propose);

            self.upsert_current_instance(updated_instance);

            Some(Message::Accept { key: self.current_instance, ballot, value: value_to_propose })
        }

        pub exec fn accept(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& recv.is_some()
            &&& recv.unwrap() is Accept
            &&& {
                    let recv = recv.unwrap();
                    let (msg_key, ballot, value) = (recv->Accept_key as nat, recv->Accept_ballot.into_spec(), recv->Accept_value as SpecValue);

                    &&& msg_key == key
                    &&& old_spec.instances.contains_key(key)
                    &&& ballot.cmp(&old_spec.instances[key].current_ballot) >= 0
                }
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
            let key = self.current_instance as nat;
            let ballot = Ballot::from_spec(new_spec.instances[key].current_ballot);

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send == Some(Message::Accepted { key: key as u64, sender: c.id, ballot })
            &&& low_accept(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            if let Some(Message::Accept { key, ballot, value }) = recv {
                let current_instance = self.get_current_instance();

                let mut updated_instance = current_instance.clone();
                updated_instance.current_ballot = ballot.clone();
                updated_instance.accept_ballot = Some(ballot.clone());
                updated_instance.accept_value = Some(value);

                self.upsert_current_instance(updated_instance);

                Some(Message::Accepted { key, sender: c.id, ballot })
            } else {
                proof! { assert(false); };
                None
            }
        }

        pub exec fn accepted(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& recv.is_some()
            &&& recv.unwrap() is Accepted
            &&& {
                    let recv = recv.unwrap();
                    let (msg_key, sender, ballot) = (recv->Accepted_key as nat, recv->Accepted_sender as nat, recv->Accepted_ballot.into_spec());

                    &&& msg_key == key
                    &&& old_spec.instances.contains_key(key)
                    &&& old_spec.instances[key].accepted.contains_key(ballot)
                }
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send.is_none()
            &&& low_accepted(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            if let Some(Message::Accepted { key, sender, ballot }) = recv {
                let current_instance = self.get_current_instance();

                proof! {
                    axiom_ballot_obeys_hash_table_key_model();
                    broadcast use group_hash_axioms;
                };
                let current_acceptor_set = current_instance.accepted.get(&ballot).unwrap();
                let mut updated_acceptor_set = current_acceptor_set.clone();
                updated_acceptor_set.insert(sender);

                proof! {
                    let current_acceptor_set_spec = Set::new(|sender: nat| sender <= usize::MAX && current_acceptor_set@.contains(sender as usize));
                    let updated_acceptor_set_spec = Set::new(|sender: nat| sender <= usize::MAX && updated_acceptor_set@.contains(sender as usize));

                    assert(updated_acceptor_set_spec =~= current_acceptor_set_spec.insert(sender as nat));
                };

                let mut updated_instance = current_instance.clone();
                updated_instance.fill_accepted(ballot, updated_acceptor_set);

                self.upsert_current_instance(updated_instance);
            }

            None
        }

        pub exec fn send_decide(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& old_spec.instances.contains_key(key)
            &&& old_spec.instances[key].proposed_value.contains_key(old_spec.instances[key].current_ballot)
            &&& old_spec.instances[key].accepted.contains_key(old_spec.instances[key].current_ballot)
            &&& old_spec.instances[key].accepted[old_spec.instances[key].current_ballot].len() > c.num_failures
            &&& recv.is_none()
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send == Some(Message::Decide {
                    key: self.current_instance,
                    ballot: self.instances@[self.current_instance].current_ballot,
                    value: self.instances@[self.current_instance].proposed_value@[self.instances@[self.current_instance].current_ballot]
                })
            &&& low_send_decide(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send))
        })
        {
            let current_instance = self.get_current_instance();
            let ballot = current_instance.current_ballot.clone();

            proof! {
                axiom_ballot_obeys_hash_table_key_model();
                broadcast use group_hash_axioms;
            };
            let value_to_decide = current_instance.proposed_value.get(&ballot).unwrap().clone();

            Some(Message::Decide { key: self.current_instance, ballot, value: value_to_decide })
        }

        pub exec fn decide(&mut self, c: &Constants, recv: Option<Message>) -> (send: Option<Message>)
        requires ({
            let old_spec = old(self).into_spec();
            let key = old(self).current_instance as nat;

            &&& old_spec.well_formed(&c.into_spec())
            &&& recv.is_some()
            &&& recv.unwrap() is Decide
            &&& {
                    let recv = recv.unwrap();
                    let (msg_key, ballot, value) = (recv->Decide_key as nat, recv->Decide_ballot.into_spec(), recv->Accept_value as SpecValue);

                    &&& msg_key == key
                    &&& old_spec.instances.contains_key(key)
                    &&& ballot.cmp(&old_spec.instances[key].current_ballot) == 1
                }
        })
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
            let expected_value = recv.unwrap()->Decide_value as SpecValue;

            &&& new_spec.well_formed(&c.into_spec())
            &&& self.current_instance == old(self).current_instance
            &&& send.is_none()
            &&& low_decide(&c.into_spec(), &old_spec, &new_spec, old(self).current_instance as nat, Variables::net_op(recv, send), expected_value)
        })
        {
            if let Some(Message::Decide { key, ballot, value }) = recv {
                let current_instance = self.get_current_instance();

                let mut updated_instance = current_instance.clone();
                updated_instance.current_ballot = ballot.clone();
                updated_instance.decide_value = Some(value);

                self.upsert_current_instance(updated_instance);
            }

            None
        }
    }
}
