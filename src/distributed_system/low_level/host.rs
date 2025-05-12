use super::{Message, NetworkOperation};
use crate::distributed_system::{Event, Value};
use vstd::{calc, prelude::*};

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

    pub struct Instance {
        pub current_ballot: Ballot,
        pub promised: Map<Ballot, Map<nat, Option<(Ballot, Value)>>>,
        pub proposed_value: Map<Ballot, Value>,
        pub accepted: Map<Ballot, Set<nat>>,
        pub accept_ballot: Option<Ballot>,
        pub accept_value: Option<Value>,
        pub decide_value: Option<Value>,
    }

    pub struct Variables {
        pub instances: Map<nat, Instance>,
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
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables, host_id: nat, num_hosts: nat) -> bool {
        &&& u.well_formed(c)
        &&& c.id == host_id
        &&& c.num_hosts == num_hosts
        &&& u.instances.is_empty()
    }

    pub open spec fn init_request(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        &&& !u.instances.contains_key(key)
        &&& net_op.recv.is_none()
        &&& v.instances == u.instances.insert(key, Instance {
            current_ballot: Ballot { num: 0, pid: 0 },
            promised: Map::empty(),
            proposed_value: Map::empty(),
            accepted: Map::empty(),
            accept_ballot: None,
            accept_value: None,
            decide_value: None,
        })
        &&& net_op.send.is_none()
    }

    pub open spec fn send_prepare(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        &&& u.instances.contains_key(key)
        &&& net_op.recv.is_none()
        &&& {
            let new_ballot = Ballot { num: u.instances[key].current_ballot.num + 1, pid: c.id };

            &&& !u.instances[key].promised.contains_key(new_ballot)
            &&& !u.instances[key].proposed_value.contains_key(new_ballot)
            &&& !u.instances[key].accepted.contains_key(new_ballot)
            &&& u.instances[key].decide_value.is_none()
            &&& v.instances == u.instances.insert(key, Instance {
                    current_ballot: u.instances[key].current_ballot,
                    promised: u.instances[key].promised.insert(new_ballot, Map::empty()),
                    proposed_value: u.instances[key].proposed_value,
                    accepted: u.instances[key].accepted.insert(new_ballot, Set::empty()),
                    accept_ballot: u.instances[key].accept_ballot,
                    accept_value: u.instances[key].accept_value,
                    decide_value: u.instances[key].decide_value,
                })
            &&& net_op.send == Some(Message::Prepare { key, ballot: new_ballot })
        }
    }

    pub open spec fn promise(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Prepare { key: instance, ballot }) = net_op.recv {
            &&& instance == key
            &&& u.instances.contains_key(instance)
            &&& ballot.cmp(&u.instances[instance].current_ballot) == 1
            &&& v.instances[instance].current_ballot == ballot
            &&& v.instances == u.instances.insert(instance, Instance {
                    current_ballot: ballot,
                    promised: u.instances[instance].promised,
                    proposed_value: u.instances[instance].proposed_value,
                    accepted: u.instances[instance].accepted,
                    accept_ballot: u.instances[instance].accept_ballot,
                    accept_value: u.instances[instance].accept_value,
                    decide_value: u.instances[instance].decide_value,
                })
            &&& net_op.send == if (u.instances[instance].accept_ballot.is_some()) {
                    Some(Message::Promise { key, sender: c.id, ballot, accepted: Some((u.instances[instance].accept_ballot.unwrap(), u.instances[instance].accept_value.unwrap())) })
                } else {
                    Some(Message::Promise { key, sender: c.id, ballot, accepted: None })
                }
        } else {
            &&& false
        }
    }

    pub open spec fn promised(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Promise { key: instance, sender, ballot, accepted }) = net_op.recv {
            &&& instance == key
            &&& u.instances.contains_key(instance)
            &&& u.instances[instance].promised.contains_key(ballot)
            &&& !u.instances[instance].proposed_value.contains_key(ballot)
            &&& v.instances == u.instances.insert(instance, Instance {
                    current_ballot: u.instances[instance].current_ballot,
                    promised: u.instances[instance].promised.insert(ballot, u.instances[instance].promised[ballot].insert(sender, accepted)),
                    proposed_value: u.instances[instance].proposed_value,
                    accepted: u.instances[instance].accepted,
                    accept_ballot: u.instances[instance].accept_ballot,
                    accept_value: u.instances[instance].accept_value,
                    decide_value: u.instances[instance].decide_value,
                })
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

    pub open spec fn send_accept(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        let instance = key;

        &&& u.instances.contains_key(instance)
        &&& net_op.recv.is_none()
        &&& u.instances[instance].promised.contains_key(u.instances[instance].current_ballot)
        &&& u.instances[instance].promised[u.instances[instance].current_ballot].len() > c.num_failures
        &&& !u.instances[instance].proposed_value.contains_key(u.instances[instance].current_ballot)
        &&& v.instances == u.instances.insert(instance, Instance {
                current_ballot: u.instances[instance].current_ballot,
                promised: u.instances[instance].promised,
                proposed_value: u.instances[instance].proposed_value.insert(
                    u.instances[instance].current_ballot,
                    if let Some((_, value)) = get_max_accepted_value(u.instances[instance].promised[u.instances[instance].current_ballot]) { value } else { c.id as Value }
                ),
                accepted: u.instances[instance].accepted,
                accept_ballot: u.instances[instance].accept_ballot,
                accept_value: u.instances[instance].accept_value,
                decide_value: u.instances[instance].decide_value,
            })
        &&& net_op.send == Some(Message::Accept { key, ballot: v.instances[instance].current_ballot, value: v.instances[instance].proposed_value[v.instances[instance].current_ballot] })
    }

    pub open spec fn accept(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Accept { key: instance, ballot, value }) = net_op.recv {
            &&& instance == key
            &&& u.instances.contains_key(instance)
            &&& ballot.cmp(&u.instances[instance].current_ballot) >= 0
            &&& v.instances == u.instances.insert(instance, Instance {
                    current_ballot: ballot,
                    promised: u.instances[instance].promised,
                    proposed_value: u.instances[instance].proposed_value,
                    accepted: u.instances[instance].accepted,
                    accept_ballot: Some(ballot),
                    accept_value: Some(value),
                    decide_value: u.instances[instance].decide_value,
                })
            &&& net_op.send == Some(Message::Accepted { key, sender: c.id, ballot })
        } else {
            &&& false
        }
    }

    pub open spec fn accepted(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Accepted { key: instance, sender, ballot }) = net_op.recv {
            &&& instance == key
            &&& u.instances.contains_key(instance)
            &&& u.instances[instance].accepted.contains_key(ballot)
            &&& v.instances == u.instances.insert(instance, Instance {
                    current_ballot: u.instances[instance].current_ballot,
                    promised: u.instances[instance].promised,
                    proposed_value: u.instances[instance].proposed_value,
                    accepted: u.instances[instance].accepted.insert(ballot, u.instances[instance].accepted[ballot].insert(sender)),
                    accept_ballot: u.instances[instance].accept_ballot,
                    accept_value: u.instances[instance].accept_value,
                    decide_value: u.instances[instance].decide_value,
                })
            &&& net_op.send.is_none()
        } else {
            &&& false
        }
    }

    pub open spec fn send_decide(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        let instance = key;

        &&& u.instances.contains_key(instance)
        &&& net_op.recv.is_none()
        &&& u.instances[instance].proposed_value.contains_key(u.instances[instance].current_ballot)
        &&& u.instances[instance].accepted.contains_key(u.instances[instance].current_ballot)
        &&& u.instances[instance].accepted[u.instances[instance].current_ballot].len() > c.num_failures
        &&& v == u
        &&& net_op.send == Some(Message::Decide { key, ballot: u.instances[instance].current_ballot, value: u.instances[instance].proposed_value[u.instances[instance].current_ballot] })
    }

    pub open spec fn decide(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation, expected_value: Value) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        if let Some(Message::Decide { key: instance, ballot, value }) = net_op.recv {
            &&& instance == key
            &&& u.instances.contains_key(instance)
            &&& ballot.cmp(&u.instances[instance].current_ballot) == 1
            &&& value == expected_value
            &&& v.instances == u.instances.insert(instance, Instance {
                    current_ballot: ballot,
                    promised: u.instances[instance].promised,
                    proposed_value: u.instances[instance].proposed_value,
                    accepted: u.instances[instance].accepted,
                    accept_ballot: u.instances[instance].accept_ballot,
                    accept_value: u.instances[instance].accept_value,
                    decide_value: Some(value),
                })
            &&& net_op.send.is_none()
        } else {
            &&& false
        }
    }

    pub open spec fn step(c: &Constants, u: &Variables, v: &Variables, key: nat, net_op: NetworkOperation, event: Event) -> bool {
        &&& u.well_formed(c)
        &&& v.well_formed(c)
        &&& match event {
                Event::Decide { key: event_key, value } => {
                    &&& event_key == key
                    &&& decide(c, u, v, key, net_op, value)
                },
                Event::NoOp => {
                    ||| init_request(c, u, v, key, net_op)
                    ||| send_prepare(c, u, v, key, net_op)
                    ||| promise(c, u, v, key, net_op)
                    ||| promised(c, u, v, key, net_op)
                    ||| send_accept(c, u, v, key, net_op)
                    ||| accept(c, u, v, key, net_op)
                    ||| accepted(c, u, v, key, net_op)
                    ||| send_decide(c, u, v, key, net_op)
                },
            }
    }

    pub open spec fn accepted_map_ballots_are_same(b1: Ballot, b2: Ballot) -> bool {
        b1.cmp(&b2) == 0
    }

    pub open spec fn map_has_key_with_some_value<K, V>(accepted_map: Map<K, Option<V>>, sender: K) -> bool {
        accepted_map.contains_key(sender) && accepted_map[sender].is_some()
    }

    pub open spec fn map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map: Map<nat, Option<(Ballot, Value)>>, sender: nat) -> bool {
        map_has_key_with_some_value(accepted_map, sender) && accepted_map[sender] == get_max_accepted_value(accepted_map)
    }

    pub open spec fn same_accepted_ballots_in_accepted_map_have_same_accepted_value(accepted_map: Map<nat, Option<(Ballot, Value)>>) -> bool {
        forall |s1: nat, s2: nat|
            accepted_map.contains_key(s1) &&
            accepted_map.contains_key(s2) &&
            accepted_map[s1].is_some() &&
            accepted_map[s2].is_some() &&
            #[trigger] accepted_map_ballots_are_same(accepted_map[s1].unwrap().0, accepted_map[s2].unwrap().0) ==>
            accepted_map[s1].unwrap().1 == accepted_map[s2].unwrap().1
    }

    pub open spec fn is_largest_accepted_ballot_sender(accepted_map: Map<nat, Option<(Ballot, Value)>>, largest_accepted_ballot_sender: nat) -> bool {
        &&& accepted_map.contains_key(largest_accepted_ballot_sender)
        &&& accepted_map[largest_accepted_ballot_sender].is_some()
        &&& {
                let largest_accepted_ballot = accepted_map[largest_accepted_ballot_sender].unwrap().0;

                forall |sender: nat| #![auto]
                    accepted_map.contains_key(sender) &&
                    accepted_map[sender].is_some() ==>
                    largest_accepted_ballot.cmp(&accepted_map[sender].unwrap().0) >= 0
            }
    }

    pub proof fn if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(accepted_map: Map<nat, Option<(Ballot, Value)>>)
    requires
        accepted_map.dom().finite(),
        exists |sender: nat| #[trigger] map_has_key_with_some_value(accepted_map, sender)
    ensures
        exists |largest_accepted_ballot_sender: nat| #[trigger] is_largest_accepted_ballot_sender(accepted_map, largest_accepted_ballot_sender)
    decreases
        accepted_map.len()
    {
        assert(accepted_map.len() > 0);
        let sender = accepted_map.dom().choose();

        if (accepted_map.dom().is_singleton()) {
            assert(is_largest_accepted_ballot_sender(accepted_map, sender));
        } else {
            let sub_accepted_map = accepted_map.remove(sender);
            assert(sub_accepted_map.len() == accepted_map.len() - 1);

            if (accepted_map[sender].is_none()) {
                assert(accepted_map =~= sub_accepted_map.insert(sender, None));

                let sub_sender = choose |sender: nat| #[trigger] map_has_key_with_some_value(accepted_map, sender);
                assert(map_has_key_with_some_value(sub_accepted_map, sub_sender));

                if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(sub_accepted_map);
                let chosen_sender = choose |chosen_sender: nat| #[trigger] is_largest_accepted_ballot_sender(sub_accepted_map, chosen_sender);
                assert(is_largest_accepted_ballot_sender(accepted_map, chosen_sender));
            } else {
                assert(accepted_map[sender].is_some() && sub_accepted_map.len() > 0);
                let sender_ballot = accepted_map[sender].unwrap().0;

                let other_sender = sub_accepted_map.dom().choose();
                assert(other_sender != sender && sub_accepted_map.contains_key(other_sender));

                if (exists |s: nat| #[trigger] map_has_key_with_some_value(sub_accepted_map, s)) {
                    if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(sub_accepted_map);

                    let sub_largest_sender = choose |sub_largest_sender: nat| #[trigger] is_largest_accepted_ballot_sender(sub_accepted_map, sub_largest_sender);
                    let sub_largest_sender_ballot = sub_accepted_map[sub_largest_sender].unwrap().0;

                    if (sender_ballot.cmp(&sub_largest_sender_ballot) >= 0) {
                        assert(is_largest_accepted_ballot_sender(accepted_map, sender));
                    } else {
                        assert(is_largest_accepted_ballot_sender(accepted_map, sub_largest_sender));
                    }
                } else {
                    assert(forall |s: nat| #![auto] sub_accepted_map.contains_key(s) ==> !map_has_key_with_some_value(sub_accepted_map, s));
                    assert(sub_accepted_map =~= Map::new(
                        |s: nat| sub_accepted_map.contains_key(s),
                        |s: nat| if (map_has_key_with_some_value(sub_accepted_map, s)) { sub_accepted_map[s] } else { None },
                    ));
                    assert(forall |s: nat| #![auto] sub_accepted_map.contains_key(s) ==> sub_accepted_map[s].is_none());
                    assert(is_largest_accepted_ballot_sender(accepted_map, sender));
                    assert(exists |largest_accepted_ballot_sender: nat| #[trigger] is_largest_accepted_ballot_sender(accepted_map, largest_accepted_ballot_sender));
                }
            }
        }
    }

    pub proof fn get_max_accepted_value_is_none_iff_all_accepted_values_are_none(accepted_map: Map<nat, Option<(Ballot, Value)>>)
    requires
        accepted_map.dom().finite(),
    ensures
        get_max_accepted_value(accepted_map).is_none() <==> (forall |sender: nat| #![auto] accepted_map.contains_key(sender) ==> accepted_map[sender].is_none())
    decreases
        accepted_map.len()
    {
        if (accepted_map.dom() =~= Set::empty()) {
        } else {
            get_max_accepted_value_is_none_iff_all_accepted_values_are_none(accepted_map.remove(accepted_map.dom().choose()));
        }
    }

    pub proof fn get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(accepted_map: Map<nat, Option<(Ballot, Value)>>)
    requires
        accepted_map.dom().finite(),
    ensures
        get_max_accepted_value(accepted_map).is_some() ==> (exists |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, s)),
    decreases
        accepted_map.len()
    {
        if (accepted_map.len() == 0) {
            assert(get_max_accepted_value(accepted_map).is_none());
        } else if (accepted_map.len() == 1) {
            let chosen_sender = accepted_map.dom().choose();
            let sub_accepted_map = accepted_map.remove(chosen_sender);
            assert(accepted_map.contains_key(chosen_sender) && sub_accepted_map =~= Map::empty());

            calc! {
                (==)
                get_max_accepted_value(accepted_map); {}
                max_accepted_value_by_ballot(accepted_map[chosen_sender], get_max_accepted_value(sub_accepted_map)); {}
                accepted_map[chosen_sender];
            }

            if (accepted_map[chosen_sender].is_some()) {
                assert(map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, chosen_sender));
                assert(get_max_accepted_value(accepted_map).is_some() ==> (exists |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, s)));
            }
        } else {
            let chosen_sender = accepted_map.dom().choose();
            let sub_accepted_map = accepted_map.remove(chosen_sender);
            assert(accepted_map.contains_key(chosen_sender) && !sub_accepted_map.contains_key(chosen_sender));

            get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(sub_accepted_map);

            if (get_max_accepted_value(sub_accepted_map).is_some()) {
                let sub_chosen_sender = choose |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(sub_accepted_map, s);
                assert(get_max_accepted_value(accepted_map) == max_accepted_value_by_ballot(accepted_map[chosen_sender], accepted_map[sub_chosen_sender]));
                if (get_max_accepted_value(accepted_map).is_some()) {
                    let some_sender = if (get_max_accepted_value(accepted_map) == accepted_map[chosen_sender]) { chosen_sender } else { sub_chosen_sender };
                    assert(map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, some_sender));
                }
                assert(get_max_accepted_value(accepted_map).is_some() ==> (exists |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, s)));
            } else {
                assert(get_max_accepted_value(accepted_map) == accepted_map[chosen_sender]);
                if (accepted_map[chosen_sender].is_some()) {
                    assert(map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, chosen_sender));
                }
                assert(get_max_accepted_value(accepted_map).is_some() ==> (exists |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, s)));
            }
        }
    }

    pub proof fn get_max_accepted_value_is_some_if_accepted_map_has_sender_with_value_as_some_value(accepted_map: Map<nat, Option<(Ballot, Value)>>)
    requires
        accepted_map.dom().finite(),
        exists |sender: nat| #[trigger] map_has_key_with_some_value(accepted_map, sender),
    ensures
        get_max_accepted_value(accepted_map).is_some(),
    decreases
        accepted_map.len()
    {
        assert(accepted_map.len() > 0);
        let satisfying_key = choose |sender: nat| #[trigger] accepted_map.contains_key(sender) && accepted_map[sender].is_some();
        let max_accepted_value = get_max_accepted_value(accepted_map);

        if (accepted_map.dom().is_singleton()) {
            let sub_acepted_map = accepted_map.remove(satisfying_key);
            assert(sub_acepted_map =~= Map::empty());

            let sub_max_accepted_value = get_max_accepted_value(sub_acepted_map);
            assert(sub_max_accepted_value.is_none() && max_accepted_value == accepted_map[satisfying_key] && max_accepted_value.is_some());
        } else {
            let random_key = accepted_map.dom().choose();
            let sub_random_accepted_map = accepted_map.remove(random_key);

            assert(max_accepted_value == max_accepted_value_by_ballot(accepted_map[random_key], get_max_accepted_value(sub_random_accepted_map)));
            if (random_key != satisfying_key) {
                assert(map_has_key_with_some_value(sub_random_accepted_map, satisfying_key));
                get_max_accepted_value_is_some_if_accepted_map_has_sender_with_value_as_some_value(sub_random_accepted_map);
            }
        }
    }

    pub proof fn get_max_accepted_value_is_same_as_sender_value_if_all_other_values_are_none(accepted_map: Map<nat, Option<(Ballot, Value)>>, sender: nat)
    requires
        accepted_map.dom().finite(),
        accepted_map.contains_key(sender),
        forall |s: nat| #![auto] accepted_map.contains_key(s) && s != sender ==> accepted_map[s].is_none(),
    ensures
        get_max_accepted_value(accepted_map) == accepted_map[sender]
    decreases
        accepted_map.len()
    {
        assert(accepted_map.len() == accepted_map.dom().len() > 0);

        if (accepted_map.len() == 1) {
            assert(accepted_map.dom().is_singleton()) by { Set::lemma_is_singleton(accepted_map.dom()); };
            calc! {
                (==)
                get_max_accepted_value(accepted_map); {}
                max_accepted_value_by_ballot(accepted_map[sender], get_max_accepted_value(accepted_map.remove(sender))); {}
                accepted_map[sender];
            };
            assert(get_max_accepted_value(accepted_map) == accepted_map[sender]);
        } else {
            let chosen_sender = accepted_map.dom().choose();
            let sub_accepted_map = accepted_map.remove(chosen_sender);

            if (chosen_sender != sender) {
                assert(accepted_map[chosen_sender].is_none());
                get_max_accepted_value_is_same_as_sender_value_if_all_other_values_are_none(sub_accepted_map, sender);
                assert(get_max_accepted_value(accepted_map) == accepted_map[sender]);
            } else {
                calc! {
                    (==)
                    get_max_accepted_value(accepted_map); {}
                    max_accepted_value_by_ballot(accepted_map[chosen_sender], get_max_accepted_value(sub_accepted_map)); {
                        get_max_accepted_value_is_none_iff_all_accepted_values_are_none(sub_accepted_map);
                    }
                    max_accepted_value_by_ballot(accepted_map[chosen_sender], None);
                };
            }
        }
    }

    pub proof fn get_max_accepted_ballot_corresponds_to_largest_ballot(accepted_map: Map<nat, Option<(Ballot, Value)>>)
    requires
        accepted_map.dom().finite(),
        exists |sender: nat| #[trigger] map_has_key_with_some_value(accepted_map, sender)
    ensures
        ({
            let largest_accepted_ballot_sender = choose |largest_accepted_ballot_sender: nat| #[trigger] is_largest_accepted_ballot_sender(accepted_map, largest_accepted_ballot_sender);

            &&& accepted_map.contains_key(largest_accepted_ballot_sender)
            &&& get_max_accepted_value(accepted_map).is_some()
            &&& get_max_accepted_value(accepted_map).unwrap().0 == accepted_map[largest_accepted_ballot_sender].unwrap().0
        })
    decreases
        accepted_map.len()
    {
        assert(accepted_map.dom().finite() && accepted_map.len() > 0);

        if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(accepted_map);
        let largest_accepted_ballot_sender = choose |largest_accepted_ballot_sender: nat| #[trigger] is_largest_accepted_ballot_sender(accepted_map, largest_accepted_ballot_sender);
        assert(accepted_map.contains_key(largest_accepted_ballot_sender) && accepted_map[largest_accepted_ballot_sender].is_some());
        let largest_accepted_ballot = accepted_map[largest_accepted_ballot_sender].unwrap().0;

        if (accepted_map.len() == 1) {
            calc! {
                (==)
                get_max_accepted_value(accepted_map); {}
                max_accepted_value_by_ballot(accepted_map[largest_accepted_ballot_sender], get_max_accepted_value(accepted_map.remove(largest_accepted_ballot_sender))); {}
                max_accepted_value_by_ballot(accepted_map[largest_accepted_ballot_sender], None); {}
                accepted_map[largest_accepted_ballot_sender];
            };
            assert(get_max_accepted_value(accepted_map) == accepted_map[largest_accepted_ballot_sender]);
        } else {
            let chosen_sender = accepted_map.dom().choose();
            let sub_accepted_map = accepted_map.remove(chosen_sender);
            let sub_response = get_max_accepted_value(sub_accepted_map);

            assert(get_max_accepted_value(accepted_map) == max_accepted_value_by_ballot(accepted_map[chosen_sender], sub_response));

            if (sub_response.is_none()) {
                get_max_accepted_value_is_none_iff_all_accepted_values_are_none(sub_accepted_map);
                assert(chosen_sender == largest_accepted_ballot_sender);
                assert(get_max_accepted_value(accepted_map) == accepted_map[chosen_sender]);
            } else {
                let sub_largest_ballot = sub_response.unwrap().0;
                assert(exists |sub_sender: nat| #![auto] sub_accepted_map.contains_key(sub_sender) && sub_accepted_map[sub_sender] == sub_response)
                by { get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(sub_accepted_map); };
                assert(largest_accepted_ballot.cmp(&sub_largest_ballot) >= 0);

                if (chosen_sender == largest_accepted_ballot_sender) {
                    assert(get_max_accepted_value(accepted_map) == accepted_map[largest_accepted_ballot_sender]);
                } else {
                    assert(sub_accepted_map.contains_key(largest_accepted_ballot_sender));
                    assert(is_largest_accepted_ballot_sender(sub_accepted_map, largest_accepted_ballot_sender));
                    assert(map_has_key_with_some_value(sub_accepted_map, largest_accepted_ballot_sender));
                    get_max_accepted_ballot_corresponds_to_largest_ballot(sub_accepted_map);
                    assert(get_max_accepted_value(accepted_map).unwrap().0 == accepted_map[largest_accepted_ballot_sender].unwrap().0);
                }
            }
        }
    }

    pub proof fn get_max_accepted_value_is_commutative(accepted_map: Map<nat, Option<(Ballot, Value)>>, sender: nat)
    requires
        accepted_map.dom().finite(),
        accepted_map.contains_key(sender),
        same_accepted_ballots_in_accepted_map_have_same_accepted_value(accepted_map),
    ensures
        get_max_accepted_value(accepted_map) == max_accepted_value_by_ballot(accepted_map[sender], get_max_accepted_value(accepted_map.remove(sender)))
    decreases
        accepted_map.len()
    {
        let random_sender = accepted_map.dom().choose();

        let no_sender_map = accepted_map.remove(sender);
        let no_random_map = accepted_map.remove(random_sender);

        let no_sender_result = get_max_accepted_value(no_sender_map);
        let no_random_result = get_max_accepted_value(no_random_map);

        let expected_result = get_max_accepted_value(accepted_map);
        let calculated_result = max_accepted_value_by_ballot(accepted_map[sender], no_sender_result);

        if (random_sender == sender) {
            assert(expected_result == calculated_result);
        } else {
            assert(no_sender_map.contains_key(random_sender) && no_random_map.contains_key(sender));
            get_max_accepted_value_is_commutative(no_random_map, sender);
            assert(no_random_result == max_accepted_value_by_ballot(no_random_map[sender], get_max_accepted_value(no_random_map.remove(sender))));

            if (no_sender_result.is_none()) {
                get_max_accepted_value_is_none_iff_all_accepted_values_are_none(no_sender_map);
                assert(accepted_map[random_sender].is_none() && expected_result == no_random_result);
                assert(calculated_result == accepted_map[sender]);

                if (no_random_result.is_none()) {
                    assert(no_random_result == no_sender_result);

                    get_max_accepted_value_is_none_iff_all_accepted_values_are_none(no_random_map);
                    assert(accepted_map[sender].is_none());
                    assert(no_sender_result == accepted_map[sender]);
                    assert(no_random_result == accepted_map[sender]);
                } else {
                    assert(get_max_accepted_value(no_random_map.remove(sender)).is_none()) by { get_max_accepted_value_is_none_iff_all_accepted_values_are_none(no_random_map.remove(sender)); };
                    assert(no_random_result == no_random_map[sender]);
                    assert(no_random_result == accepted_map[sender]);
                }

                assert(expected_result == calculated_result);
            } else {
                get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(no_sender_map);
                if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(no_sender_map);
                let largest_non_sender_sender = choose |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(no_sender_map, s);
                let (lnss_ballot, lnss_value) = accepted_map[largest_non_sender_sender].unwrap();

                get_max_accepted_ballot_corresponds_to_largest_ballot(no_sender_map);
                assert(no_sender_result.unwrap().0 == no_sender_map[largest_non_sender_sender].unwrap().0);
                assert(no_sender_result == no_sender_map[largest_non_sender_sender]);
                assert(largest_non_sender_sender != sender);

                if (no_random_result.is_none()) {
                    assert(expected_result == accepted_map[random_sender]);

                    get_max_accepted_value_is_none_iff_all_accepted_values_are_none(no_random_map);
                    assert(no_random_map[sender].is_none() && calculated_result == no_sender_result);
                    assert(largest_non_sender_sender == random_sender);
                    assert(no_sender_result == accepted_map[random_sender]);
                    assert(expected_result == calculated_result);
                } else {
                    assert(expected_result.is_some());
                    get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(accepted_map);
                    if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(accepted_map);
                    let largest_sender = choose |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(accepted_map, s);
                    let (ls_ballot, ls_value) = accepted_map[largest_sender].unwrap();

                    get_max_accepted_ballot_corresponds_to_largest_ballot(accepted_map);
                    assert(expected_result.unwrap().0 == accepted_map[largest_sender].unwrap().0);
                    assert(expected_result == accepted_map[largest_sender]);

                    get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(no_random_map);
                    if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(no_random_map);
                    let largest_non_random_sender = choose |s: nat| #[trigger] map_has_key_with_some_value_same_as_get_max_accepted_value(no_random_map, s);
                    let (lnrs_ballot, lnrs_value) = accepted_map[largest_non_random_sender].unwrap();

                    get_max_accepted_ballot_corresponds_to_largest_ballot(no_random_map);
                    assert(no_random_result.unwrap().0 == no_random_map[largest_non_random_sender].unwrap().0);
                    assert(no_random_result == no_random_map[largest_non_random_sender]);
                    assert(largest_non_random_sender != random_sender);

                    assert(expected_result == max_accepted_value_by_ballot(accepted_map[random_sender], accepted_map[largest_non_random_sender]));
                    assert(calculated_result == max_accepted_value_by_ballot(accepted_map[sender], accepted_map[largest_non_sender_sender]));

                    if (accepted_map[sender].is_none() && accepted_map[random_sender].is_none()) {
                        assert(expected_result == accepted_map[largest_non_random_sender] && calculated_result == accepted_map[largest_non_sender_sender]);
                        assert(largest_non_random_sender != sender && largest_non_sender_sender != random_sender);

                        assert(is_largest_accepted_ballot_sender(accepted_map, largest_non_random_sender));
                        assert(is_largest_accepted_ballot_sender(accepted_map, largest_non_sender_sender));
                        assert(accepted_map_ballots_are_same(lnrs_ballot, lnss_ballot));
                        assert(accepted_map[largest_non_random_sender] == accepted_map[largest_non_sender_sender]);
                    } else if (accepted_map[sender].is_none()) {
                        assert(calculated_result == accepted_map[largest_non_sender_sender]);
                        assert(largest_non_random_sender != sender && random_sender != sender);

                        assert(accepted_map_ballots_are_same(ls_ballot, lnss_ballot));
                        assert(accepted_map[largest_non_sender_sender] == accepted_map[largest_sender]);
                        assert(expected_result == calculated_result);
                    } else {
                        let (s_ballot, s_value) = accepted_map[sender].unwrap();
                        let (other_largest_sender, other_largest_ballot) = if (s_ballot.cmp(&lnss_ballot) >= 0) { (sender, s_ballot) } else { (largest_non_sender_sender, lnss_ballot) };

                        assert(calculated_result == accepted_map[other_largest_sender]);
                        assert(accepted_map_ballots_are_same(ls_ballot, other_largest_ballot));
                        assert(accepted_map[other_largest_sender] == accepted_map[largest_sender]);
                        assert(expected_result == calculated_result);
                    }
                }
            }
        }
    }
}
