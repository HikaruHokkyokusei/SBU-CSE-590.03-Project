use super::{Event, Value};
use vstd::{prelude::*, set_lib::*};

verus! {
    pub mod host;
    pub mod network;

    pub enum Message {
        Prepare { key: nat, ballot: host::Ballot },
        Promise { key: nat, sender: nat, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)> },
        Accept { key: nat, ballot: host::Ballot, value: Value },
        Accepted { key: nat, sender: nat, ballot: host::Ballot },
        Decide { key: nat, ballot: host::Ballot, value: Value },
    }

    pub struct NetworkOperation {
        pub send: Option<Message>,
        pub recv: Option<Message>,
    }

    pub struct Constants {
        pub num_failures: nat,
        pub num_hosts: nat,
        pub hosts: Seq<host::Constants>,
        pub network: network::Constants,
    }

    pub struct Variables {
        pub hosts: Seq<host::Variables>,
        pub network: network::Variables,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.num_hosts > 0
            &&& self.num_failures > 0
            &&& self.num_hosts == ((2 * self.num_failures) + 1)
            &&& self.hosts.len() == self.num_hosts
            &&& forall |i: nat| #![auto]
                    0 <= i < self.num_hosts ==>
                    self.hosts[i as int].id == i &&
                    self.hosts[i as int].num_failures == self.num_failures
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.hosts.len() == c.hosts.len()
            &&& forall |idx: nat| #![auto] 0 <= idx < self.hosts.len() ==> self.hosts[idx as int].well_formed(&c.hosts[idx as int])
            &&& self.network.well_formed(&c.network)
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |idx: nat| #![auto]
                0 <= idx < u.hosts.len() ==>
                host::init(&c.hosts[idx as int], &u.hosts[idx as int], idx, u.hosts.len())
        &&& network::init(&c.network, &u.network)
    }

    pub enum Transition {
        HostStep { host_id: int, instance: nat, net_op: NetworkOperation }
    }

    pub open spec fn host_step(c: &Constants, u: &Variables, v: &Variables, host_id: int, instance: nat, net_op: NetworkOperation, event: Event) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        &&& {
            &&& 0 <= host_id < u.hosts.len()
            &&& host::step(&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id], instance, net_op, event)
            &&& forall |i: int| 0 <= i < v.hosts.len() && i != host_id ==> u.hosts[i] == v.hosts[i]
        }
        &&& network::step(&c.network, &u.network, &v.network, net_op)
    }

    pub open spec fn is_valid_transition(c: &Constants, u: &Variables, v: &Variables, transition: Transition, event: Event) -> bool {
        &&& u.well_formed(c)
        &&& v.well_formed(c)
        &&& match transition {
            Transition::HostStep { host_id, instance, net_op } => host_step(c, u, v, host_id, instance, net_op, event)
        }
    }

    pub open spec fn next(c: &Constants, u: &Variables, v: &Variables, event: Event) -> bool {
        exists |transition: Transition| is_valid_transition(c, u, v, transition, event)
    }

    pub open spec fn safety(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |i: int, j: int| #![auto]
                0 <= i < j < u.hosts.len() &&
                u.hosts[i].decide_value.is_some() &&
                u.hosts[j].decide_value.is_some() ==>
                u.hosts[i].decide_value == u.hosts[j].decide_value
    }

    impl Variables {
        pub open spec fn all_maps_and_sets_are_finite(&self, c: &Constants) -> bool {
            &&& forall |i: int| #![auto] 0 <= i < self.hosts.len() ==> self.hosts[i].instances.dom().finite()
            &&& forall |i: int, instance: nat| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) ==>
                    self.hosts[i].instances[instance].promised.dom().finite() &&
                    self.hosts[i].instances[instance].proposed_value.dom().finite() &&
                    self.hosts[i].instances[instance].accepted.dom().finite()
            &&& forall |i: int, instance: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].promised.contains_key(ballot) ==>
                    self.hosts[i].instances[instance].promised[ballot].dom().finite()
            &&& forall |i: int, instance: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].accepted.contains_key(ballot) ==>
                    self.hosts[i].instances[instance].accepted[ballot].finite()
        }

        pub open spec fn all_map_keys_and_set_values_are_valid(&self, c: &Constants) -> bool {
            &&& forall |i: int, instance: nat, ballot: host::Ballot, sender: nat| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].promised.contains_key(ballot) &&
                    self.hosts[i].instances[instance].promised[ballot].contains_key(sender) ==>
                    0 <= sender < c.num_hosts
            &&& forall |i: int, instance: nat, ballot: host::Ballot, sender: nat| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].accepted.contains_key(ballot) &&
                    self.hosts[i].instances[instance].accepted[ballot].contains(sender) ==>
                    0 <= sender < c.num_hosts
        }

        pub open spec fn all_map_and_set_sizes_are_bounded(&self, c: &Constants) -> bool {
            &&& forall |i: int, instance: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].promised.contains_key(ballot) ==>
                    0 <= self.hosts[i].instances[instance].promised[ballot].len() <= c.num_hosts
            &&& forall |i: int, instance: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].accepted.contains_key(ballot) ==>
                    0 <= self.hosts[i].instances[instance].accepted[ballot].len() <= c.num_hosts
        }

        pub open spec fn all_ballot_pids_in_all_maps_correspond_to_respective_host_id(&self, c: &Constants) -> bool {
            &&& forall |i: int, instance: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].promised.contains_key(ballot) ==>
                    ballot.pid == c.hosts[i].id
            &&& forall |i: int, instance: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].proposed_value.contains_key(ballot) ==>
                    ballot.pid == c.hosts[i].id
            &&& forall |i: int, instance: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(instance) &&
                    self.hosts[i].instances[instance].accepted.contains_key(ballot) ==>
                    ballot.pid == c.hosts[i].id
        }

        pub proof fn all_map_and_set_sizes_are_bounded_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.all_map_and_set_sizes_are_bounded(c),
        {
            assert(u.all_maps_and_sets_are_finite(c));
            assert(self.network.in_flight_messages.finite());

            let Transition::HostStep { host_id, instance, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |i: int, key: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(key) &&
                    self.hosts[i].instances[key].promised.contains_key(ballot) implies
                    0 <= self.hosts[i].instances[key].promised[ballot].len() <= c.num_hosts
            by {
                assert(forall |sender: nat| #[trigger] self.hosts[i].instances[key].promised[ballot].contains_key(sender) ==> 0 <= sender < c.num_hosts);
                let full_set = Set::new(|x: nat| 0 <= x < c.num_hosts);
                assert(full_set.finite() && full_set.len() == c.num_hosts) by { full_set_size(full_set, c.num_hosts); };
                assert(self.hosts[i].instances[key].promised[ballot].len() <= c.num_hosts) by { lemma_len_subset(self.hosts[i].instances[key].promised[ballot].dom(), full_set); };
            };

            assert forall |i: int, key: nat, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].instances.contains_key(key) &&
                    self.hosts[i].instances[key].accepted.contains_key(ballot) implies
                    0 <= self.hosts[i].instances[key].accepted[ballot].len() <= c.num_hosts
            by {
                assert(forall |sender: nat| #[trigger] self.hosts[i].instances[key].accepted[ballot].contains(sender) ==> 0 <= sender < c.num_hosts);
                let full_set = Set::new(|x: nat| 0 <= x < c.num_hosts);
                assert(full_set.finite() && full_set.len() == c.num_hosts) by { full_set_size(full_set, c.num_hosts); };
                assert(self.hosts[i].instances[key].accepted[ballot].len() <= c.num_hosts) by { lemma_len_subset(self.hosts[i].instances[key].accepted[ballot], full_set); };
            };
        }
    }

    pub open spec fn host_map_properties(c: &Constants, u: &Variables) -> bool {
        &&& u.all_maps_and_sets_are_finite(c)
        &&& u.all_map_keys_and_set_values_are_valid(c)
        &&& u.all_map_and_set_sizes_are_bounded(c)
        &&& u.all_ballot_pids_in_all_maps_correspond_to_respective_host_id(c)
    }

    impl Variables {
        pub open spec fn prepare_msg_in_network_implies_sender_map_has_ballot_key(&self, c: &Constants) -> bool {
            forall |key: nat, ballot: host::Ballot| #![auto]
                self.network.in_flight_messages.contains(Message::Prepare { key, ballot }) ==>
                {
                    let leader = ballot.pid as int;

                    &&& 0 <= leader < self.hosts.len()
                    &&& self.hosts[leader].instances.contains_key(key)
                    &&& self.hosts[leader].instances[key].promised.contains_key(ballot)
                    &&& self.hosts[leader].instances[key].accepted.contains_key(ballot)
                }
        }

        pub open spec fn promise_msg_in_network_implies_sender_has_promised(&self, c: &Constants) -> bool {
            forall |key: nat, sender: nat, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
                self.network.in_flight_messages.contains(Message::Promise { key, sender, ballot, accepted }) ==>
                self.hosts[sender as int].instances.contains_key(key) &&
                self.hosts[sender as int].instances[key].current_ballot.cmp(&ballot) >= 0
        }

        pub open spec fn accept_msg_in_network_implies_quorum_promised_and_value_proposed_by_sender(&self, c: &Constants) -> bool {
            forall |key: nat, ballot: host::Ballot, value: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Accept { key, ballot, value }) ==>
                {
                    let leader = ballot.pid as int;

                    &&& 0 <= leader < self.hosts.len()
                    &&& self.hosts[leader].instances.contains_key(key)
                    &&& self.hosts[leader].instances[key].promised.contains_key(ballot)
                    &&& self.hosts[leader].instances[key].promised[ballot].len() > c.num_failures
                    &&& self.hosts[leader].instances[key].proposed_value.contains_key(ballot)
                    &&& self.hosts[leader].instances[key].proposed_value[ballot] == value
                }
        }

        pub open spec fn accepted_msg_in_network_implies_sender_has_accepted_some_value(&self, c: &Constants) -> bool {
            forall |key: nat, sender: nat, ballot: host::Ballot| #![auto]
                self.network.in_flight_messages.contains(Message::Accepted { key, sender, ballot }) ==>
                self.hosts[sender as int].instances.contains_key(key) &&
                self.hosts[sender as int].instances[key].current_ballot.cmp(&ballot) >= 0 &&
                self.hosts[sender as int].instances[key].accept_ballot.is_some() &&
                self.hosts[sender as int].instances[key].accept_ballot.unwrap().cmp(&ballot) >= 0 &&
                self.hosts[sender as int].instances[key].accept_value.is_some()
        }

        pub open spec fn decide_msg_in_network_implies_quorum_has_accepted_some_value(&self, c: &Constants) -> bool {
            forall |key: nat, ballot: host::Ballot, value: Value|
                #[trigger] self.network.in_flight_messages.contains(Message::Decide { key, ballot, value }) ==>
                {
                    let leader = ballot.pid as int;

                    &&& 0 <= leader < self.hosts.len()
                    &&& self.hosts[leader].instances.contains_key(key)
                    &&& self.hosts[leader].instances[key].accepted.contains_key(ballot)
                    &&& self.hosts[leader].instances[key].accepted[ballot].len() > c.num_failures
                    &&& self.hosts[leader].instances[key].proposed_value.contains_key(ballot)
                    &&& value == self.hosts[leader].instances[key].proposed_value[ballot]
                }
        }
    }

    pub open spec fn messages_in_network_implies_first_degree_properties(c: &Constants, u: &Variables) -> bool {
        &&& u.prepare_msg_in_network_implies_sender_map_has_ballot_key(c)
        &&& u.promise_msg_in_network_implies_sender_has_promised(c)
        &&& u.accept_msg_in_network_implies_quorum_promised_and_value_proposed_by_sender(c)
        &&& u.accepted_msg_in_network_implies_sender_has_accepted_some_value(c)
        &&& u.decide_msg_in_network_implies_quorum_has_accepted_some_value(c)
    }

    impl Variables {
        pub open spec fn promised_state_implies_network_has_prepare_msg(&self, c: &Constants) -> bool {
            forall |i: int, instance: nat| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances.contains_key(instance) &&
                self.hosts[i].instances[instance].current_ballot.num > 0 ==>
                self.network.in_flight_messages.contains(Message::Prepare { key: instance, ballot: self.hosts[i].instances[instance].current_ballot })
        }

        pub open spec fn someone_promised_implies_network_has_their_promise_msg(&self, c: &Constants) -> bool {
            forall |i: int, instance: nat, ballot: host::Ballot, sender: nat| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances.contains_key(instance) &&
                self.hosts[i].instances[instance].promised.dom().contains(ballot) &&
                self.hosts[i].instances[instance].promised[ballot].dom().contains(sender) ==>
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot, accepted: self.hosts[i].instances[instance].promised[ballot][sender] })
        }

        pub open spec fn either_of_accept_ballot_or_value_is_some(&self, i: int, instance: nat) -> bool {
            ||| self.hosts[i].instances[instance].accept_ballot.is_some()
            ||| self.hosts[i].instances[instance].accept_value.is_some()
        }

        pub open spec fn if_accept_ballot_is_some_then_accept_value_is_some(&self, c: &Constants) -> bool {
            forall |i: int, instance: nat| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances.contains_key(instance) ==>
                self.hosts[i].instances[instance].accept_ballot.is_some() == self.hosts[i].instances[instance].accept_value.is_some()
        }

        pub open spec fn accepted_state_implies_network_has_accept_message(&self, c: &Constants) -> bool {
            forall |i: int, instance: nat|
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances.contains_key(instance) &&
                #[trigger] self.either_of_accept_ballot_or_value_is_some(i, instance) ==>
                self.hosts[i].instances[instance].accept_ballot.is_some() &&
                self.hosts[i].instances[instance].accept_value.is_some() &&
                self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot: self.hosts[i].instances[instance].accept_ballot.unwrap(), value: self.hosts[i].instances[instance].accept_value.unwrap() })
        }

        pub open spec fn accepted_state_implies_network_has_accepted_message(&self, c: &Constants) -> bool {
            forall |sender: nat, instance: nat, ballot: host::Ballot| #![auto]
                0 <= sender < self.hosts.len() &&
                self.hosts[sender as int].instances.contains_key(instance) &&
                self.hosts[sender as int].instances[instance].accept_ballot == Some(ballot) ==>
                self.network.in_flight_messages.contains(Message::Accepted { key: instance, sender , ballot })
        }

        pub open spec fn someone_accepted_implies_network_has_their_accepted_msg(&self, c: &Constants) -> bool {
            forall |i: int, instance: nat, ballot: host::Ballot, sender: nat| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances[instance].accepted.contains_key(ballot) &&
                self.hosts[i].instances[instance].accepted[ballot].contains(sender) ==>
                self.network.in_flight_messages.contains(Message::Accepted { key: instance, sender, ballot })
        }

        pub open spec fn decided_state_implies_network_has_decide_message(&self, c: &Constants) -> bool {
            forall |i: int, instance: nat| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances.contains_key(instance) &&
                self.hosts[i].instances[instance].decide_value.is_some() ==>
                exists |ballot: host::Ballot| #![auto] self.network.in_flight_messages.contains(Message::Decide { key: instance, ballot, value: self.hosts[i].instances[instance].decide_value.unwrap() })
        }

        pub proof fn accepted_state_implies_network_has_accept_message_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.accepted_state_implies_network_has_accept_message(c),
        {
            assert(self.all_maps_and_sets_are_finite(c));

            assert forall |i: int, instance: nat|
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances.contains_key(instance) &&
                #[trigger] self.either_of_accept_ballot_or_value_is_some(i, instance) implies
                self.hosts[i].instances[instance].accept_ballot.is_some() &&
                self.hosts[i].instances[instance].accept_value.is_some() &&
                self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot: self.hosts[i].instances[instance].accept_ballot.unwrap(), value: self.hosts[i].instances[instance].accept_value.unwrap() })
            by {
                if (self.hosts[i].instances[instance].accept_ballot == u.hosts[i].instances[instance].accept_ballot) { assert(u.either_of_accept_ballot_or_value_is_some(i, instance)); }
            };
        }

        pub proof fn decided_state_implies_network_has_decide_message_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.decided_state_implies_network_has_decide_message(c),
        {
            assert(self.all_maps_and_sets_are_finite(c));

            let Transition::HostStep { host_id, instance: step_key, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |i: int, instance: nat| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].instances.contains_key(instance) &&
                self.hosts[i].instances[instance].decide_value.is_some() implies
                exists |ballot: host::Ballot| #![auto] self.network.in_flight_messages.contains(Message::Decide { key: instance, ballot, value: self.hosts[i].instances[instance].decide_value.unwrap() })
            by {
                match ((event, net_op.recv)) {
                    (Event::Decide { key: decide_key, value }, Some(Message::Decide { key: instance, ballot: recv_bal, value: recv_val }))
                    if (i == host_id) => {
                        assert(decide_key == step_key);
                        assert(host::decide(lc, lu, lv, step_key, net_op, value));
                        assert(step_key == instance);
                        assert(recv_val == self.hosts[i].instances[instance].decide_value.unwrap());
                        assert(self.network.in_flight_messages.contains(Message::Decide { key: instance, ballot: recv_bal, value: recv_val }));
                        assert(exists |ballot: host::Ballot| #![auto] self.network.in_flight_messages.contains(Message::Decide { key: instance, ballot, value: self.hosts[i].instances[instance].decide_value.unwrap() }));
                    },
                    _ => { }
                }
            };
        }
    }

    pub open spec fn properties_imply_first_degree_messages_in_network(c: &Constants, u: &Variables) -> bool {
        &&& u.promised_state_implies_network_has_prepare_msg(c)
        &&& u.someone_promised_implies_network_has_their_promise_msg(c)
        &&& u.if_accept_ballot_is_some_then_accept_value_is_some(c)
        &&& u.accepted_state_implies_network_has_accept_message(c)
        &&& u.accepted_state_implies_network_has_accepted_message(c)
        &&& u.someone_accepted_implies_network_has_their_accepted_msg(c)
        &&& u.decided_state_implies_network_has_decide_message(c)
    }

    impl Variables {
        pub open spec fn network_msgs_have_valid_sender_and_ballot_pid(&self, c: &Constants) -> bool {
            &&& forall |key: nat, ballot: host::Ballot| #![auto]
                    self.network.in_flight_messages.contains(Message::Prepare { key, ballot }) ==>
                    ballot.num > 0 && 0 <= ballot.pid < self.hosts.len()
            &&& forall |key:nat, sender: nat, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
                    self.network.in_flight_messages.contains(Message::Promise { key, sender, ballot, accepted }) ==>
                    ballot.num > 0 && 0 <= sender < self.hosts.len() && ballot.num > 0 && 0 <= ballot.pid < self.hosts.len()
            &&& forall |key:nat, sender: nat, ballot: host::Ballot, accepted_ballot: host::Ballot, accepted_value: Value| #![auto]
                    self.network.in_flight_messages.contains(Message::Promise { key, sender, ballot, accepted: Some((accepted_ballot, accepted_value)) }) ==>
                    ballot.num > 0 && 0 <= accepted_ballot.pid < self.hosts.len()
            &&& forall |key:nat, ballot: host::Ballot, value: Value| #![auto]
                    self.network.in_flight_messages.contains(Message::Accept { key, ballot, value }) ==>
                    ballot.num > 0 && 0 <= ballot.pid < self.hosts.len()
            &&& forall |key:nat, sender: nat, ballot: host::Ballot| #![auto]
                    self.network.in_flight_messages.contains(Message::Accepted { key, sender, ballot }) ==>
                    ballot.num > 0 && 0 <= sender < self.hosts.len() && ballot.num > 0 && 0 <= ballot.pid < self.hosts.len()
            &&& forall |key:nat, ballot: host::Ballot, value: Value| #![auto]
                    ballot.num > 0 && self.network.in_flight_messages.contains(Message::Decide { key, ballot, value }) ==>
                    0 <= ballot.pid < self.hosts.len()
        }

        pub open spec fn promise_msgs_from_same_sender_for_same_ballot_have_same_accepted(&self, c: &Constants) -> bool {
            forall |sender: nat, instance: nat, b1: host::Ballot, a1: Option<(host::Ballot, Value)>, b2: host::Ballot, a2: Option<(host::Ballot, Value)>| #![auto]
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot: b1, accepted: a1 }) &&
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot: b2, accepted: a2 }) &&
                b1 == b2 ==>
                a1 == a2
        }

        pub open spec fn ballot_in_accepted_is_smaller_than_promise_message_ballot(&self, c: &Constants) -> bool {
            forall |sender: nat, instance: nat, promise_ballot: host::Ballot, accepted_ballot: host::Ballot, accepted_value: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot: promise_ballot, accepted: Some((accepted_ballot, accepted_value)) }) ==>
                accepted_ballot.cmp(&promise_ballot) < 0
        }

        pub open spec fn value_in_accepted_of_promise_is_same_as_proposed_value_for_corresponding_ballot(&self, c: &Constants) -> bool {
            forall |sender: nat, instance: nat, ballot: host::Ballot, accepted_ballot: host::Ballot, accepted_value: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot, accepted: Some((accepted_ballot, accepted_value)) }) ==>
                {
                    let leader = accepted_ballot.pid as int;

                    &&& 0 <= leader < self.hosts.len()
                    &&& self.hosts[leader].instances.contains_key(instance)
                    &&& self.hosts[leader].instances[instance].proposed_value.contains_key(accepted_ballot)
                    &&& accepted_value == self.hosts[leader].instances[instance].proposed_value[accepted_ballot]
                }
        }

        pub open spec fn if_accepted_is_some_in_promise_message_then_network_has_corresponding_old_accepted_message(&self, c: &Constants) -> bool {
            forall |sender: nat, instance: nat, ballot: host::Ballot, accepted_ballot: host::Ballot, accepted_value: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot, accepted: Some((accepted_ballot, accepted_value)) }) ==>
                self.network.in_flight_messages.contains(Message::Accepted { key: instance, sender, ballot: accepted_ballot })
        }

        pub open spec fn network_has_at_most_one_accept_message_for_any_ballot(&self, c: &Constants) -> bool {
            forall |instance: nat, ballot: host::Ballot, v1: Value, v2: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value: v1 }) &&
                self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value: v2 }) ==>
                v1 == v2
        }

        pub open spec fn accepted_msg_in_network_implies_future_promises_of_same_sender_have_some_accepted(&self, c: &Constants) -> bool {
            forall |sender: nat, instance: nat, accepted_ballot: host::Ballot, future_ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
                self.network.in_flight_messages.contains(Message::Accepted { key: instance, sender, ballot: accepted_ballot }) &&
                future_ballot.cmp(&accepted_ballot) > 0 &&
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot: future_ballot, accepted }) ==>
                {
                    &&& accepted.is_some()
                    &&& accepted.unwrap().0.cmp(&accepted_ballot) >= 0
                }
        }

        pub open spec fn accepted_msg_in_network_implies_network_has_corresponding_accept_msg(&self, c: &Constants) -> bool {
            forall |sender: nat, instance: nat, ballot: host::Ballot| #![auto]
                self.network.in_flight_messages.contains(Message::Accepted { key: instance, sender, ballot }) ==>
                (exists |value: Value| #![auto] self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value }))
        }

        pub open spec fn all_decide_messages_hold_same_value(&self, c: &Constants) -> bool {
            forall |b1:host::Ballot, v1: Value, b2: host::Ballot, v2: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Decide { ballot: b1, value: v1 }) &&
                self.network.in_flight_messages.contains(Message::Decide { ballot: b2, value: v2 }) ==>
                v1 == v2
        }

        pub proof fn value_in_accepted_of_promise_is_same_as_proposed_value_for_corresponding_ballot_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.value_in_accepted_of_promise_is_same_as_proposed_value_for_corresponding_ballot(c),
        {
            assert(host_map_properties(c, self)) by { self.all_map_and_set_sizes_are_bounded_is_inductive(c, u, event); };
            assert(self.if_accepted_is_some_in_promise_message_then_network_has_corresponding_old_accepted_message(c));

            let Transition::HostStep { host_id, instance: step_key, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |sender: nat, instance: nat, ballot: host::Ballot, accepted_ballot: host::Ballot, accepted_value: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Promise { key: instance, sender, ballot, accepted: Some((accepted_ballot, accepted_value)) }) implies
                {
                    let leader = accepted_ballot.pid as int;

                    &&& 0 <= leader < self.hosts.len()
                    &&& self.hosts[leader].instances.contains_key(instance)
                    &&& self.hosts[leader].instances[instance].proposed_value.contains_key(accepted_ballot)
                    &&& accepted_value == self.hosts[leader].instances[instance].proposed_value[accepted_ballot]
                }
            by {
                if (instance == step_key) {
                    let leader = accepted_ballot.pid as int;
                    assert(0 <= leader < self.hosts.len());
                    assert(self.hosts[leader].instances[instance].proposed_value.contains_key(accepted_ballot));

                    match ((event, net_op.recv, net_op.send)) {
                        (Event::NoOp, Some(Message::Prepare { key: recv_instance, ballot: prepare_ballot }), Some(Message::Promise { key: send_instance, sender, ballot: promise_ballot, accepted }))
                        if (host::promise(lc, lu, lv, step_key, net_op) && (sender == host_id) && (promise_ballot == prepare_ballot) && accepted.is_some() && (accepted == Some((accepted_ballot, accepted_value)))) => {
                            assert(recv_instance == send_instance);
                            assert(self.either_of_accept_ballot_or_value_is_some(sender as int, instance));
                            assert(self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot: lv.instances[instance].accept_ballot.unwrap(), value: lv.instances[instance].accept_value.unwrap() })) by {
                                self.accepted_state_implies_network_has_accept_message_is_inductive(c, u, event);
                            };
                            assert(accepted_value == self.hosts[leader].instances[instance].proposed_value[accepted_ballot]);
                        },
                        _ => {},
                    }
                }
            };
        }

        pub proof fn accepted_msg_in_network_implies_network_has_corresponding_accept_msg_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.accepted_msg_in_network_implies_network_has_corresponding_accept_msg(c),
        {
            assert(host_map_properties(c, self)) by { self.all_map_and_set_sizes_are_bounded_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, instance: step_key, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |sender: nat, instance: nat, ballot: host::Ballot| #![auto]
                self.network.in_flight_messages.contains(Message::Accepted { key: instance, sender, ballot }) implies
                exists |value: Value| #![auto] self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value })
            by {
                match (event) {
                    Event::NoOp => {
                        let condition = host::send_prepare(lc, lu, lv, step_key, net_op) ||
                            host::send_decide(lc, lu, lv, step_key, net_op) ||
                            host::promise(lc, lu, lv, step_key, net_op) ||
                            host::accept(lc, lu, lv, step_key, net_op) ||
                            host::send_accept(lc, lu, lv, step_key, net_op);

                        if (condition) {
                            assert(exists |value: Value| #![auto] self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value })) by {
                                assert(exists |value: Value| #![auto] u.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value }));
                                let existing_value = choose |value: Value| #![auto] u.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value });
                                assert(self.network.in_flight_messages.contains(Message::Accept { key: instance, ballot, value: existing_value }));
                            };
                        }
                    },
                    _ => {}
                }
            };
        }

        pub proof fn all_decide_messages_hold_same_value_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.all_decide_messages_hold_same_value(c)
        {
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, event); };
            assert(self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some(c)) by { self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |b1:host::Ballot, v1: Value, b2: host::Ballot, v2: Value| #![auto]
                self.network.in_flight_messages.contains(Message::Decide { ballot: b1, value: v1 }) &&
                self.network.in_flight_messages.contains(Message::Decide { ballot: b2, value: v2 }) implies
                v1 == v2
            by {
                let (h1, h2) = (b1.pid as int, b2.pid as int);
                assert(0 <= h1 < self.hosts.len() && 0 <= h2 < self.hosts.len());
                assert(map_contains_key_with_min_len(self.hosts[h1].accepted, b1, c.num_failures));
                assert(map_contains_key_with_min_len(self.hosts[h2].accepted, b2, c.num_failures));

                assert(self.hosts[h1].proposed_value.contains_key(b1) && self.hosts[h2].proposed_value.contains_key(b2));
                assert(v1 == self.hosts[h1].proposed_value[b1] && v2 == self.hosts[h2].proposed_value[b2]);

                if (b1 != b2) {
                    let (future_leader, future_ballot, future_value) = if (b1.cmp(&b2) > 0) {
                        (h1, b1, v1)
                    } else {
                        (h2, b2, v2)
                    };
                    let (past_leader, past_ballot, past_value) = if (b1.cmp(&b2) > 0) {
                        (h2, b2, v2)
                    } else {
                        (h1, b1, v1)
                    };

                    assert(future_ballot.cmp(&past_ballot) > 0);
                    self.accepted_system_always_proposes_same_value_in_future_is_inductive(c, u, event);
                    assert(map_contains_key_with_min_len_and_map_contains_key(self.hosts[past_leader].accepted, self.hosts[future_leader].proposed_value, past_ballot, future_ballot, c.num_failures));
                }

                assert (v1 == v2);
            };
        }
    }

    pub open spec fn properties_of_valid_messages_in_network(c: &Constants, u: &Variables) -> bool {
        &&& u.network_msgs_have_valid_sender_and_ballot_pid(c)
        &&& u.promise_msgs_from_same_sender_for_same_ballot_have_same_accepted(c)
        &&& u.ballot_in_accepted_is_smaller_than_promise_message_ballot(c)
        &&& u.value_in_accepted_of_promise_is_same_as_proposed_value_for_corresponding_ballot(c)
        &&& u.if_accepted_is_some_in_promise_message_then_network_has_corresponding_old_accepted_message(c)
        &&& u.network_has_at_most_one_accept_message_for_any_ballot(c)
        &&& u.accepted_msg_in_network_implies_future_promises_of_same_sender_have_some_accepted(c)
        &&& u.accepted_msg_in_network_implies_network_has_corresponding_accept_msg(c)
        &&& u.all_decide_messages_hold_same_value(c)
    }

    impl Variables {
        pub open spec fn if_host_maps_have_ballot_then_network_has_prepare_msg_with_same_ballot(&self, c: &Constants) -> bool {
            &&& forall |i: int, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].promised.contains_key(ballot) ==>
                    self.network.in_flight_messages.contains(Message::Prepare { ballot })
            &&& forall |i: int, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].proposed_value.contains_key(ballot) ==>
                    self.network.in_flight_messages.contains(Message::Prepare { ballot })
            &&& forall |i: int, ballot: host::Ballot| #![auto]
                    0 <= i < self.hosts.len() &&
                    self.hosts[i].accepted.contains_key(ballot) ==>
                    self.network.in_flight_messages.contains(Message::Prepare { ballot })
        }

        pub open spec fn proposed_some_value_and_get_max_accepted_value_is_some(&self, i: int, ballot: host::Ballot) -> bool {
            &&& self.hosts[i].proposed_value.contains_key(ballot)
            &&& host::get_max_accepted_value(self.hosts[i].promised[ballot]).is_some()
        }

        pub open spec fn if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some(&self, c: &Constants) -> bool {
            forall |i: int, ballot: host::Ballot|
                0 <= i < self.hosts.len() &&
                #[trigger] self.proposed_some_value_and_get_max_accepted_value_is_some(i, ballot) ==>
                self.hosts[i].proposed_value[ballot] == host::get_max_accepted_value(self.hosts[i].promised[ballot]).unwrap().1
        }

        pub open spec fn host_accept_ballot_is_none_or_leq_to_current_ballot(&self, c: &Constants) -> bool {
            forall |i: int| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].accept_ballot.is_some() ==>
                self.hosts[i].accept_ballot.unwrap().cmp(&self.hosts[i].current_ballot) <= 0
        }

        pub open spec fn hosts_have_same_some_accept_ballot(&self, h1: int, h2: int) -> bool {
            &&& self.hosts[h1].accept_ballot.is_some()
            &&& self.hosts[h1].accept_ballot == self.hosts[h2].accept_ballot
        }

        pub open spec fn hosts_have_same_some_accept_value(&self, h1: int, h2: int) -> bool {
            &&& self.hosts[h1].accept_value.is_some()
            &&& self.hosts[h1].accept_value == self.hosts[h2].accept_value
        }

        pub open spec fn any_two_hosts_with_some_same_accept_ballot_have_some_same_accept_value(&self, c: &Constants) -> bool {
            forall |h1: int, h2: int|
                0 <= h1 < self.hosts.len() &&
                0 <= h2 < self.hosts.len() &&
                #[trigger] self.hosts_have_same_some_accept_ballot(h1, h2) ==>
                self.hosts_have_same_some_accept_value(h1, h2)
        }

        pub open spec fn if_someone_has_accepted_then_someone_has_proposed(&self, c: &Constants) -> bool {
            forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < self.hosts.len() &&
                self.hosts[i].accepted.contains_key(ballot) &&
                self.hosts[i].accepted[ballot].len() > 0 ==>
                self.hosts[i].proposed_value.contains_key(ballot)
        }

        pub open spec fn same_accepted_ballots_have_same_value_in_accepted_map_in_promised_of_all_hosts(&self, c: &Constants) -> bool {
            forall |i: int, ballot: host::Ballot|
                0 <= i < self.hosts.len() &&
                self.hosts[i].promised.contains_key(ballot) ==>
                #[trigger] host::same_accepted_ballots_in_accepted_map_have_same_accepted_value(self.hosts[i].promised[ballot])
        }

        pub proof fn if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some(c),
        {
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |i: int, ballot: host::Ballot|
            0 <= i < self.hosts.len() &&
            #[trigger] self.proposed_some_value_and_get_max_accepted_value_is_some(i, ballot) implies
            self.hosts[i].proposed_value[ballot] == host::get_max_accepted_value(self.hosts[i].promised[ballot]).unwrap().1
            by {
                if ((i != host_id) || u.hosts[i].proposed_value.contains_key(ballot)) {
                    assert(u.proposed_some_value_and_get_max_accepted_value_is_some(i, ballot));
                }
            };
        }

        pub proof fn any_two_hosts_with_some_same_accept_ballot_have_some_same_accept_value_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.any_two_hosts_with_some_same_accept_ballot_have_some_same_accept_value(c),
        {
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |h1: int, h2: int|
                0 <= h1 < self.hosts.len() &&
                0 <= h2 < self.hosts.len() &&
                #[trigger] self.hosts_have_same_some_accept_ballot(h1, h2) implies
                self.hosts_have_same_some_accept_value(h1, h2)
            by {
                assert(self.hosts[h1].accept_ballot.is_some() && self.hosts[h2].accept_ballot.is_some());
                assert(self.hosts[h1].accept_ballot == self.hosts[h2].accept_ballot);

                self.accepted_state_implies_network_has_accept_message_is_inductive(c, u, event);

                assert(self.either_of_accept_ballot_or_value_is_some(h1));
                assert(self.network.in_flight_messages.contains(Message::Accept { ballot: self.hosts[h1].accept_ballot.unwrap(), value: self.hosts[h1].accept_value.unwrap() }));
                assert(self.either_of_accept_ballot_or_value_is_some(h2));
                assert(self.network.in_flight_messages.contains(Message::Accept { ballot: self.hosts[h2].accept_ballot.unwrap(), value: self.hosts[h2].accept_value.unwrap() }));
            };
        }
    }

    pub open spec fn properties_of_valid_host_states(c: &Constants, u: &Variables) -> bool {
        &&& u.if_host_maps_have_ballot_then_network_has_prepare_msg_with_same_ballot(c)
        &&& u.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some(c)
        &&& u.host_accept_ballot_is_none_or_leq_to_current_ballot(c)
        &&& u.any_two_hosts_with_some_same_accept_ballot_have_some_same_accept_value(c)
        &&& u.if_someone_has_accepted_then_someone_has_proposed(c)
        &&& u.same_accepted_ballots_have_same_value_in_accepted_map_in_promised_of_all_hosts(c)
    }

    pub trait HasLen {
        spec fn get_len(&self) -> nat;
    }

    impl<K, V> HasLen for Map<K, V> {
        open spec fn get_len(&self) -> nat {
            self.len()
        }
    }

    impl<V> HasLen for Set<V> {
        open spec fn get_len(&self) -> nat {
            self.len()
        }
    }

    pub open spec fn map_contains_key_with_min_len<K, V: HasLen>(map: Map<K, V>, key: K, min_val: nat) -> bool {
        &&& map.contains_key(key)
        &&& map[key].get_len() > min_val
    }

    pub open spec fn map_contains_key_with_min_len_and_map_contains_key<K1, V1: HasLen, K2, V2>(map1: Map<K1, V1>, map2: Map<K2, V2>, key1: K1, key2: K2, min_val: nat) -> bool {
        &&& map_contains_key_with_min_len(map1, key1, min_val)
        &&& map2.contains_key(key2)
    }

    pub open spec fn two_maps_contain_values_with_min_len<K1, V1: HasLen, K2, V2: HasLen>(map1: Map<K1, V1>, map2: Map<K2, V2>, key1: K1, key2: K2, min_val: nat) -> bool {
        &&& map_contains_key_with_min_len(map1, key1, min_val)
        &&& map_contains_key_with_min_len(map2, key2, min_val)
    }

    impl Variables {
        pub open spec fn if_host_proposed_then_quorum_has_promised(&self, c: &Constants) -> bool {
            forall |i: int, ballot: host::Ballot|
                0 <= i < self.hosts.len() &&
                self.hosts[i].proposed_value.contains_key(ballot) ==>
                #[trigger] map_contains_key_with_min_len(self.hosts[i].promised, ballot, c.num_failures)
        }

        pub open spec fn if_system_accepted_exists_some_accept_value_in_future_promise_quorum(&self, c: &Constants) -> bool {
            forall |h1: int, h2: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot|
                0 <= h1 < self.hosts.len() &&
                0 <= h2 < self.hosts.len() &&
                #[trigger] two_maps_contain_values_with_min_len(self.hosts[h1].accepted, self.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures) &&
                future_ballot.cmp(&accepted_ballot) > 0 ==>
                exists |sender: nat| #[trigger] host::map_has_key_with_some_value(self.hosts[h2].promised[future_ballot], sender) && self.hosts[h1].accepted[accepted_ballot].contains(sender)
        }

        pub open spec fn accepted_system_calculates_same_proposed_value_in_future(self, c: &Constants) -> bool {
            forall |h1: int, h2: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot|
                0 <= h1 < self.hosts.len() &&
                0 <= h2 < self.hosts.len() &&
                #[trigger] two_maps_contain_values_with_min_len(self.hosts[h1].accepted, self.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures) &&
                future_ballot.cmp(&accepted_ballot) > 0 ==>
                {
                    let old_accepted_value = self.hosts[h1].proposed_value[accepted_ballot];
                    let calculated_new_proposed = host::get_max_accepted_value(self.hosts[h2].promised[future_ballot]);

                    &&& calculated_new_proposed.is_some()
                    &&& calculated_new_proposed.unwrap().1 == old_accepted_value
                }
        }

        pub open spec fn accepted_system_always_proposes_same_value_in_future(&self, c: &Constants) -> bool {
            forall |i: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot|
                0 <= i < self.hosts.len() &&
                0 <= future_ballot.pid < self.hosts.len() &&
                #[trigger] map_contains_key_with_min_len_and_map_contains_key(self.hosts[i].accepted, self.hosts[future_ballot.pid as int].proposed_value, accepted_ballot, future_ballot, c.num_failures) &&
                future_ballot.cmp(&accepted_ballot) >= 0 ==>
                self.hosts[future_ballot.pid as int].proposed_value[future_ballot] == self.hosts[i].proposed_value[accepted_ballot]
        }

        pub proof fn if_host_proposed_then_quorum_has_promised_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.if_host_proposed_then_quorum_has_promised(c),
        {
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |i: int, ballot: host::Ballot|
                0 <= i < self.hosts.len() &&
                self.hosts[i].proposed_value.contains_key(ballot) implies
                #[trigger] map_contains_key_with_min_len(self.hosts[i].promised, ballot, c.num_failures)
            by {
                if (u.hosts[i].proposed_value.contains_key(ballot)) {
                    assert(self.hosts[i].proposed_value[ballot] == u.hosts[i].proposed_value[ballot]);
                    assert(map_contains_key_with_min_len(u.hosts[i].promised, ballot, c.num_failures));
                    assert(map_contains_key_with_min_len(self.hosts[i].promised, ballot, c.num_failures));
                }
            }
        }

        pub proof fn if_system_accepted_exists_some_accept_value_in_future_promise_quorum_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c),
        {
            assert(u.network.in_flight_messages.finite());
            assert(self.network.in_flight_messages.finite());
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |h1: int, h2: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot|
                0 <= h1 < self.hosts.len() &&
                0 <= h2 < self.hosts.len() &&
                #[trigger] two_maps_contain_values_with_min_len(self.hosts[h1].accepted, self.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures) &&
                future_ballot.cmp(&accepted_ballot) > 0 implies
                exists |sender: nat| #[trigger] host::map_has_key_with_some_value(self.hosts[h2].promised[future_ballot], sender) && self.hosts[h1].accepted[accepted_ballot].contains(sender)
            by {
                assert(self.hosts.len() == c.num_hosts);
                assert(c.num_hosts == ((2 * c.num_failures) + 1));
                assert(forall |x: nat| #![auto] self.hosts[h1].accepted[accepted_ballot].contains(x) ==> 0 <= x < c.num_hosts);
                assert(forall |x: nat| #![auto] self.hosts[h2].promised[future_ballot].contains_key(x) ==> 0 <= x < c.num_hosts);
                assert(exists |sender: nat| #![auto] self.hosts[h1].accepted[accepted_ballot].contains(sender) && self.hosts[h2].promised[future_ballot].contains_key(sender)) by {
                    overlapping_sets_have_common_element(self.hosts[h1].accepted[accepted_ballot], self.hosts[h2].promised[future_ballot].dom(), c.num_failures, c.num_hosts);
                };

                let common_sender = choose |sender: nat| #![auto] self.hosts[h1].accepted[accepted_ballot].contains(sender) && self.hosts[h2].promised[future_ballot].contains_key(sender);
                assert(self.hosts[h1].accepted[accepted_ballot].contains(common_sender) && self.hosts[h2].promised[future_ballot].contains_key(common_sender));
                assert(self.hosts[common_sender as int].accept_value.is_some());
                assert(
                    forall |ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
                        self.network.in_flight_messages.contains(Message::Promise { sender: common_sender, ballot, accepted }) &&
                        ballot.cmp(&accepted_ballot) > 0 ==>
                        accepted.is_some()
                );
                assert(host::map_has_key_with_some_value(self.hosts[h2].promised[future_ballot], common_sender));
            }
        }

        pub proof fn accepted_system_calculates_same_proposed_value_in_future_is_inductive_for_accepted_host_step(&self, c: &Constants, u: &Variables, h1: int, sender: nat, accepted_ballot: host::Ballot, future_ballot: host::Ballot)
        requires
            inductive(c, u),
            next(c, u, self, Event::NoOp),
            host_step(c, u, self, h1, NetworkOperation { recv: Some(Message::Accepted { sender, ballot: accepted_ballot }), send: None }, Event::NoOp),
            host::accepted(
                &c.hosts[h1],
                &u.hosts[h1],
                &self.hosts[h1],
                NetworkOperation { recv: Some(Message::Accepted { sender, ballot: accepted_ballot }), send: None }
            ),
            network::step(&c.network, &u.network, &self.network, NetworkOperation { recv: Some(Message::Accepted { sender, ballot: accepted_ballot }), send: None }),
            0 <= future_ballot.pid < u.hosts.len(),
            future_ballot.cmp(&accepted_ballot) > 0,
            u.hosts[future_ballot.pid as int].promised.contains_key(future_ballot),
            u.hosts[future_ballot.pid as int].promised[future_ballot].len() > c.num_failures,
            self.hosts[h1].proposed_value.contains_key(accepted_ballot),
            self.hosts[h1].accepted.contains_key(accepted_ballot),
            self.hosts[h1].accepted[accepted_ballot].len() > c.num_failures,
        ensures
            ({
                let calculated_result = host::get_max_accepted_value(u.hosts[future_ballot.pid as int].promised[future_ballot]);

                &&& calculated_result.is_some()
                &&& calculated_result.unwrap().1 == self.hosts[h1].proposed_value[accepted_ballot]
            })
        decreases
            future_ballot.num, future_ballot.pid
        {
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, Event::NoOp); };

            assert(host::accepted(
                &c.hosts[h1],
                &u.hosts[h1],
                &self.hosts[h1],
                NetworkOperation { recv: Some(Message::Accepted { sender, ballot: accepted_ballot }), send: None }
            ));

            let h2 = future_ballot.pid as int;
            let accepted_map = u.hosts[h2].promised[future_ballot];

            assert(self.if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c)) by {
                self.if_system_accepted_exists_some_accept_value_in_future_promise_quorum_is_inductive(c, u, Event::NoOp);
            };
            assert(two_maps_contain_values_with_min_len(self.hosts[h1].accepted, self.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures));
            let common_sender = choose |s: nat| #[trigger] host::map_has_key_with_some_value(accepted_map, s) && self.hosts[h1].accepted[accepted_ballot].contains(s);
            let (common_sender_ballot, common_sender_value) = accepted_map[common_sender].unwrap();
            assert(common_sender_ballot.cmp(&accepted_ballot) >= 0);

            host::get_max_accepted_value_is_some_if_accepted_map_has_sender_with_value_as_some_value(accepted_map);
            let calculated_result = host::get_max_accepted_value(accepted_map);
            assert(calculated_result.is_some());
            let (calculated_ballot, calculated_value) = calculated_result.unwrap();

            host::if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(accepted_map);
            let largest_sender = choose |largest_sender: nat| #[trigger] host::is_largest_accepted_ballot_sender(accepted_map, largest_sender);
            let (largest_sender_ballot, largest_sender_value) = accepted_map[largest_sender].unwrap();

            host::get_max_accepted_ballot_corresponds_to_largest_ballot(accepted_map);
            assert(calculated_ballot == largest_sender_ballot);
            host::get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(accepted_map);
            assert(calculated_value == largest_sender_value);

            assert(largest_sender_ballot.cmp(&accepted_ballot) >= 0);

            if (largest_sender_ballot == accepted_ballot) {
                assert(calculated_value == self.hosts[h1].proposed_value[accepted_ballot]);
            } else {
                assert(self.network.in_flight_messages.contains(Message::Promise { sender: largest_sender, ballot: future_ballot, accepted: Some((largest_sender_ballot, largest_sender_value)) }));
                assert(largest_sender_value == self.hosts[largest_sender_ballot.pid as int].proposed_value[largest_sender_ballot]);

                assert(decreases_to!(future_ballot.num, future_ballot.pid => largest_sender_ballot.num, largest_sender_ballot.pid));
                self.accepted_system_calculates_same_proposed_value_in_future_is_inductive_for_accepted_host_step(c, u, h1, sender, accepted_ballot, largest_sender_ballot);
                let old_calculated_result = host::get_max_accepted_value(u.hosts[largest_sender_ballot.pid as int].promised[largest_sender_ballot]);
                assert(old_calculated_result.is_some());
                let (old_result_ballot, old_result_value) = old_calculated_result.unwrap();
                assert(old_result_value == self.hosts[h1].proposed_value[accepted_ballot]);

                self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(c, u, Event::NoOp);
                assert(self.proposed_some_value_and_get_max_accepted_value_is_some(largest_sender_ballot.pid as int, largest_sender_ballot));
                assert(self.hosts[largest_sender_ballot.pid as int].proposed_value[largest_sender_ballot] == old_result_value);

                assert(largest_sender_value == old_result_value);
            }
        }

        pub proof fn accepted_system_calculates_same_proposed_value_in_future_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.accepted_system_calculates_same_proposed_value_in_future(c),
        {
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, event); };
            assert(self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some(c)) by { self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |h1: int, h2: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot|
                0 <= h1 < self.hosts.len() &&
                0 <= h2 < self.hosts.len() &&
                #[trigger] two_maps_contain_values_with_min_len(self.hosts[h1].accepted, self.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures) &&
                future_ballot.cmp(&accepted_ballot) > 0 implies
                {
                    let old_accepted_value = self.hosts[h1].proposed_value[accepted_ballot];
                    let calculated_new_proposed = host::get_max_accepted_value(self.hosts[h2].promised[future_ballot]);

                    &&& calculated_new_proposed.is_some()
                    &&& calculated_new_proposed.unwrap().1 == old_accepted_value
                }
            by {
                let old_accepted_value = self.hosts[h1].proposed_value[accepted_ballot];
                assert(old_accepted_value == u.hosts[h1].proposed_value[accepted_ballot]);
                let calculated_new_proposed = host::get_max_accepted_value(self.hosts[h2].promised[future_ballot]);

                self.if_system_accepted_exists_some_accept_value_in_future_promise_quorum_is_inductive(c, u, event);
                let common_sender = choose |s: nat| #[trigger] host::map_has_key_with_some_value(self.hosts[h2].promised[future_ballot], s) && self.hosts[h1].accepted[accepted_ballot].contains(s);
                let (common_sender_ballot, common_sender_value) = self.hosts[h2].promised[future_ballot][common_sender].unwrap();
                assert(common_sender_ballot.cmp(&accepted_ballot) >= 0);

                host::get_max_accepted_value_is_some_if_accepted_map_has_sender_with_value_as_some_value(self.hosts[h2].promised[future_ballot]);
                assert(calculated_new_proposed.is_some());
                let (calculated_ballot, calculated_value) = calculated_new_proposed.unwrap();

                match ((event, net_op.recv, net_op.send)) {
                    (Event::NoOp, _, Some(Message::Prepare { ballot })) if (host::send_prepare(lc, lu, lv, net_op)) => {
                        assert(ballot != accepted_ballot);
                        assert(two_maps_contain_values_with_min_len(u.hosts[h1].accepted, u.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures));
                        assert(calculated_value == old_accepted_value);
                    },
                    (Event::NoOp, Some(Message::Promise { sender, ballot, accepted }), _) if (host::promised(lc, lu, lv, net_op) && (h2 == host_id)) => {
                        if (ballot == future_ballot) {
                            let old_accepted_map = lu.promised[future_ballot];
                            let new_accepted_map = lu.promised[future_ballot].insert(sender, accepted);
                            assert(lv.promised[future_ballot] == new_accepted_map);
                            assert(old_accepted_map.len() >= c.num_failures);

                            assert(host::same_accepted_ballots_in_accepted_map_have_same_accepted_value(new_accepted_map));

                            if (old_accepted_map.contains_key(sender)) {
                                assert(new_accepted_map == old_accepted_map);
                                assert(two_maps_contain_values_with_min_len(self.hosts[h1].accepted, u.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures));
                                assert(calculated_value == old_accepted_value);
                            } else {
                                host::if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(new_accepted_map);
                                let largest_sender = choose |largest_sender: nat| #[trigger] host::is_largest_accepted_ballot_sender(new_accepted_map, largest_sender);
                                let (largest_sender_ballot, largest_sender_value) = new_accepted_map[largest_sender].unwrap();
                                assert(largest_sender_ballot != ballot);

                                host::get_max_accepted_ballot_corresponds_to_largest_ballot(new_accepted_map);
                                assert(calculated_ballot == largest_sender_ballot);
                                host::get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(new_accepted_map);
                                assert(calculated_value == largest_sender_value);
                                assert(largest_sender_ballot.cmp(&accepted_ballot) >= 0);

                                let largest_sender_ballot_leader = largest_sender_ballot.pid as int;
                                assert(largest_sender_value == self.hosts[largest_sender_ballot_leader].proposed_value[largest_sender_ballot]);

                                if (largest_sender_ballot == accepted_ballot) {
                                    assert(calculated_value == old_accepted_value);
                                } else {
                                    assert(largest_sender_ballot.cmp(&accepted_ballot) > 0);
                                    assert(two_maps_contain_values_with_min_len(u.hosts[h1].accepted, u.hosts[largest_sender_ballot_leader].promised, accepted_ballot, largest_sender_ballot, c.num_failures));
                                    assert(host::get_max_accepted_value(u.hosts[largest_sender_ballot_leader].promised[largest_sender_ballot]).unwrap().1 == old_accepted_value);
                                    assert(u.proposed_some_value_and_get_max_accepted_value_is_some(largest_sender_ballot_leader, largest_sender_ballot));
                                    assert(u.hosts[largest_sender_ballot_leader].proposed_value[largest_sender_ballot] == old_accepted_value);
                                    assert(calculated_value == old_accepted_value);
                                }
                            }
                        } else {
                            assert(two_maps_contain_values_with_min_len(u.hosts[h1].accepted, u.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures));
                            assert(calculated_value == old_accepted_value);
                        }
                    },
                    (Event::NoOp, Some(Message::Accepted { sender, ballot }), None) if (host::accepted(lc, lu, lv, net_op) && (h1 == host_id)) => {
                        assert(self.hosts[h1].proposed_value == u.hosts[h1].proposed_value && self.hosts[h2].proposed_value == u.hosts[h2].proposed_value);
                        assert(self.hosts[h1].promised == u.hosts[h1].promised && self.hosts[h2].promised == u.hosts[h2].promised);

                        if ((ballot == accepted_ballot) && (lu.accepted[ballot].len() == c.num_failures)) {
                            assert(ballot != future_ballot);

                            let old_accepted_hosts = lu.accepted[ballot];
                            let new_accepted_hosts = lu.accepted[ballot].insert(sender);
                            assert(lv.accepted[ballot] == new_accepted_hosts);

                            let accepted_map = self.hosts[h2].promised[future_ballot];

                            assert(host::same_accepted_ballots_in_accepted_map_have_same_accepted_value(accepted_map));
                            host::if_accepted_map_has_sender_with_value_as_some_then_larget_accepted_ballot_sender_exists(accepted_map);
                            let largest_sender = choose |largest_sender: nat| #[trigger] host::is_largest_accepted_ballot_sender(accepted_map, largest_sender);
                            let (largest_sender_ballot, largest_sender_value) = accepted_map[largest_sender].unwrap();

                            host::get_max_accepted_ballot_corresponds_to_largest_ballot(accepted_map);
                            assert(calculated_ballot == largest_sender_ballot);
                            host::get_max_accepted_value_is_some_implies_accepted_map_has_corresponding_sender(accepted_map);
                            assert(calculated_value == largest_sender_value);

                            self.accepted_system_calculates_same_proposed_value_in_future_is_inductive_for_accepted_host_step(c, u, h1, sender, accepted_ballot, future_ballot);
                            assert(largest_sender_value == old_accepted_value);
                        } else {
                            assert(two_maps_contain_values_with_min_len(lu.accepted, u.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures));
                            assert(calculated_value == old_accepted_value);
                        }
                    },
                    _ => { },
                }
            };
        }

        pub proof fn accepted_system_always_proposes_same_value_in_future_is_inductive(&self, c: &Constants, u: &Variables, event: Event)
        requires
            inductive(c, u),
            next(c, u, self, event),
        ensures
            self.accepted_system_always_proposes_same_value_in_future(c),
        {
            assert(host_map_properties(c, self)) by { self.all_maps_and_sets_are_finite_is_inductive(c, u, event); };
            assert(self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some(c)) by { self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(c, u, event); };

            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, self, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &self.hosts[host_id]);

            assert forall |i: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot|
                0 <= i < self.hosts.len() &&
                0 <= future_ballot.pid < self.hosts.len() &&
                #[trigger] map_contains_key_with_min_len_and_map_contains_key(self.hosts[i].accepted, self.hosts[future_ballot.pid as int].proposed_value, accepted_ballot, future_ballot, c.num_failures) &&
                future_ballot.cmp(&accepted_ballot) >= 0 implies
                self.hosts[future_ballot.pid as int].proposed_value[future_ballot] == self.hosts[i].proposed_value[accepted_ballot]
            by {
                if (future_ballot.cmp(&accepted_ballot) > 0) {
                    let h2 = future_ballot.pid as int;
                    self.if_host_proposed_then_quorum_has_promised_is_inductive(c, u, event);
                    assert(two_maps_contain_values_with_min_len(self.hosts[i].accepted, self.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures));
                    let calculated_result = host::get_max_accepted_value(self.hosts[h2].promised[future_ballot]);
                    self.if_system_accepted_exists_some_accept_value_in_future_promise_quorum_is_inductive(c, u, event);
                    host::get_max_accepted_value_is_some_if_accepted_map_has_sender_with_value_as_some_value(self.hosts[h2].promised[future_ballot]);
                    assert(calculated_result.is_some());
                    let (calculated_ballot, calculated_value) = calculated_result.unwrap();


                    self.accepted_system_calculates_same_proposed_value_in_future_is_inductive(c, u, event);
                    assert(two_maps_contain_values_with_min_len(self.hosts[i].accepted, self.hosts[h2].promised, accepted_ballot, future_ballot, c.num_failures));
                    assert(calculated_value == self.hosts[i].proposed_value[accepted_ballot]);

                    self.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(c, u, event);
                    assert(self.proposed_some_value_and_get_max_accepted_value_is_some(h2, future_ballot));
                    assert(self.hosts[h2].proposed_value[future_ballot] == calculated_value);
                }
            };
        }
    }

    pub open spec fn system_quorum_properties(c: &Constants, u: &Variables) -> bool {
        &&& u.if_host_proposed_then_quorum_has_promised(c)
        &&& u.if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c)
        &&& u.accepted_system_calculates_same_proposed_value_in_future(c)
        &&& u.accepted_system_always_proposes_same_value_in_future(c)
    }

    pub open spec fn inductive(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& u.network.in_flight_messages.finite()
        &&& host_map_properties(c, u)
        &&& messages_in_network_implies_first_degree_properties(c, u)
        &&& properties_imply_first_degree_messages_in_network(c, u)
        &&& properties_of_valid_messages_in_network(c, u)
        &&& properties_of_valid_host_states(c, u)
        &&& system_quorum_properties(c, u)
    }

/*  Redundant with `set_lib::lemma_set_disjoint_lens`
    pub proof fn union_of_disjoint_sets_implies_sum_of_lengths<T>(set1: Set<T>, set2: Set<T>)
    requires
        set1.finite(),
        set2.finite(),
        set1 * set2 =~= Set::<T>::empty()
    ensures
        (set1 + set2).len() == set1.len() + set2.len()
    decreases
        set1.len() + set2.len()
    {
        let sum_of_lengths = set1.len() + set2.len();

        if (sum_of_lengths == 0) {
            assert(set1 =~= Set::<T>::empty() && set2 =~= Set::<T>::empty());
            assert(set1 + set2 =~= Set::<T>::empty());
            assert((set1 + set2).len() == sum_of_lengths);
        } else {
            if (set1.len() > 0) {
                let x = set1.choose();

                let (left, mid) = (set1.remove(x), set![x]);
                assert(left.finite() && mid.finite() && mid.len() == 1);

                let mid_value = mid.choose();
                assert(mid.contains(mid_value) && mid_value == x);

                assert(set1.len() == left.len() + 1);
                union_of_disjoint_sets_implies_sum_of_lengths(left, set2);

                let left_right = left + set2;
                assert(left_right.len() == sum_of_lengths - 1);
                assert(set1 + set2 =~= left_right + mid);

                let complete = left_right.insert(mid_value);
                assert(complete.len() == left_right.len() + 1);
                assert(left_right + mid =~= complete);

                assert((set1 + set2).len() == set1.len() + set2.len());
            } else if (set2.len() > 0) {
                let x = set2.choose();

                let (mid, right) = (set![x], set2.remove(x));
                assert(mid.finite() && right.finite() && mid.len() == 1);

                let mid_value = mid.choose();
                assert(mid.contains(mid_value) && mid_value == x);

                assert(set2.len() == right.len() + 1);
                union_of_disjoint_sets_implies_sum_of_lengths(set1, right);

                let left_right = set1 + right;
                assert(left_right.len() == sum_of_lengths - 1);
                assert(set1 + set2 =~= left_right + mid);

                let complete = left_right.insert(mid_value);
                assert(complete.len() == left_right.len() + 1);
                assert(left_right + mid =~= complete);

                assert((set1 + set2).len() == set1.len() + set2.len());
            } else {
                assert(false);
            }
        }
    }
    */

    pub proof fn subset_intersection_size_is_same_as_subset_size<T>(small_set: Set<T>, big_set: Set<T>)
    requires
        small_set.len() >= 0,
        big_set.finite(),
        small_set.subset_of(big_set),
    ensures
        small_set.finite(),
        big_set * small_set =~= small_set,
        (big_set * small_set).len() == small_set.len(),
    decreases
        small_set.len()
    {
        let intersection = big_set * small_set;

        if (small_set =~= Set::<T>::empty()) {
            assert(intersection =~= Set::<T>::empty());
            assert(intersection.len() == small_set.len());
        } else {
            let x = small_set.choose();
            let (sub_small_set, sub_big_set) = (small_set.remove(x), big_set.remove(x));
            assert(sub_small_set.finite() && sub_big_set.finite());
            subset_intersection_size_is_same_as_subset_size(sub_small_set, sub_big_set);

            let non_existent_element_set = set![small_set.choose()];
            assert(non_existent_element_set.is_singleton());

            let sub_intersection = sub_big_set * sub_small_set;
            assert(sub_intersection.finite() && sub_intersection.intersect(non_existent_element_set) =~= Set::empty());

            assert(intersection =~= sub_intersection + non_existent_element_set);
            assert(sub_intersection.len() == sub_small_set.len());

            assert((sub_intersection + non_existent_element_set).len() == sub_intersection.len() + non_existent_element_set.len()) by {
                lemma_set_disjoint_lens(sub_intersection, non_existent_element_set);
            };
        }
    }

    pub proof fn different_sized_sets_have_non_common_element<T>(set1: Set<T>, set2: Set<T>)
    requires
        set1.finite(),
        set2.finite(),
        set1.len() < set2.len(),
    ensures
        exists |x: T| #[trigger] set2.contains(x) && !set1.contains(x)
    decreases
        set1.len()
    {
        if set1 =~= Set::<T>::empty() {
            let x = set2.choose();
            assert(set2.contains(x) && !set1.contains(x));
            assert(exists |x: T| #[trigger] set2.contains(x) && !set1.contains(x));
        } else {
            let x = set1.choose();
            different_sized_sets_have_non_common_element(set1.remove(x), set2.remove(x));
        }
    }

    pub proof fn removing_common_element_reduces_intersection_size_by_1<T>(small_set: Set<T>, big_set: Set<T>, common_element: T)
    requires
        small_set.finite(),
        big_set.finite(),
        (big_set * small_set).contains(common_element),
    ensures
        (big_set.remove(common_element) * small_set.remove(common_element)).len() == (big_set * small_set).len() - 1,
    {
        assert(small_set.contains(common_element) && big_set.contains(common_element));

        let intersection = big_set * small_set;

        let (sub_small_set, sub_big_set) = (small_set.remove(common_element), big_set.remove(common_element));
        let sub_intersection = sub_big_set * sub_small_set;

        let bridge = set![common_element];
        assert(bridge.is_singleton());

        assert(intersection =~= sub_intersection + bridge);
        assert(intersection.len() == sub_intersection.len() + bridge.len()) by {
            assert(sub_intersection * bridge =~= Set::<T>::empty());
            lemma_set_disjoint_lens(sub_intersection, bridge);
        };
    }

    pub proof fn full_set_size(full_set: Set<nat>, max_val: nat)
    requires
        max_val > 0,
        full_set =~= Set::new(|x: nat| 0 <= x < max_val),
    ensures
        full_set.finite(),
        full_set.len() == max_val,
    decreases
        max_val
    {
        if (max_val == 1) {
            assert(full_set =~= set![0]);
            assert(full_set.finite());
        } else {
            let largest_val = (max_val - 1) as nat;
            let sub_full_set = full_set.remove(largest_val);
            full_set_size(sub_full_set, largest_val);
        }
    }

    pub proof fn continuous_set_size_bounds(s: Set<nat>, max_val: nat)
    requires
        s.finite(),
        forall |x: nat| #[trigger] s.contains(x) ==> 0 <= x < max_val,
    ensures
        0 <= s.len() <= max_val
    decreases
        max_val
    {
        if (max_val == 0) {
            assert(forall |x: nat| s.contains(x) ==> 0 <= x < 0);
            assert(s =~= Set::empty());
        } else {
            assert(max_val > 0);
            let largest_value = (max_val - 1) as nat;

            let ss = if (s.contains(largest_value)) {
                s.remove(largest_value)
            } else {
                s
            };

            assert(forall |x: nat| #[trigger] ss.contains(x) ==> 0 <= x < largest_value);
            continuous_set_size_bounds(ss, largest_value);
        }
    }

    pub proof fn overlapping_sets_have_common_element(set1: Set<nat>, set2: Set<nat>, floor_half_size: nat, full_size: nat)
    requires
        set1.finite(),
        set2.finite(),
        floor_half_size > 0,
        full_size == ((2 * floor_half_size) + 1),
        forall |x: nat| #![auto] set1.contains(x) ==> 0 <= x < full_size,
        forall |x: nat| #![auto] set2.contains(x) ==> 0 <= x < full_size,
        set1.len() > floor_half_size,
        set2.len() > floor_half_size,
    ensures
        exists |x: nat| #![auto] set1.contains(x) && set2.contains(x)
    {
        assert(set1.len() + set2.len() > full_size);
        assert(set1.union(set2).len() <= full_size) by { continuous_set_size_bounds(set1.union(set2), full_size); };

        let (set1_size, set2_size) = (set1.len(), set2.len());
        let (union, intersection) = (set1 + set2, set1 * set2);
        let (union_size, intersection_size) = (union.len(), intersection.len());

        assert(set1_size + set2_size == union_size + intersection_size) by { lemma_set_intersect_union_lens(set1, set2); };

        let common_len = (set1.len() + set2.len() - (set1 + set2).len()) as nat;
        assert(common_len >= 1);
        assert(common_len == intersection_size);

        assert(intersection.len() > 0);
        let common_val = intersection.choose();
        assert(intersection.contains(common_val));
        assert(set1.contains(common_val) && set2.contains(common_val));
    }
}
