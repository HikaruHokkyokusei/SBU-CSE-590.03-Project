use high_level::{
    init as high_init, next as high_next, Constants as HighConstants, Variables as HighVariables,
};
use low_level::{
    init as low_init, next as low_next, Constants as LowConstants, Variables as LowVariables, *,
};
use vstd::prelude::*;

verus! {
    pub mod high_level;
    pub mod low_level;

    pub type Value = int;

    pub enum Event {
        Decide { key: nat, value: Value },
        NoOp,
    }

    pub open spec fn constants_abstraction(lc: &LowConstants) -> HighConstants
    recommends
        lc.well_formed()
    {
        HighConstants { }
    }

    pub open spec fn variables_abstraction(lc: &LowConstants, lv: &LowVariables) -> HighVariables
    recommends
        lv.well_formed(lc)
    {
        HighVariables {
            decided_value: Map::new(
                |key: nat| (exists |i: int| #![auto] 0 <= i < lv.hosts.len() && lv.hosts[i].instances.contains_key(key) && lv.hosts[i].instances[key].decide_value.is_some()),
                |key: nat| {
                    let host = choose |i: int| #![auto] 0 <= i < lv.hosts.len() && lv.hosts[i].instances.contains_key(key) && lv.hosts[i].instances[key].decide_value.is_some();
                    lv.hosts[host].instances[key].decide_value.unwrap()
                },
            )
        }
    }

    // Corresponds to `init(c, u) ==> inductive(c, u)`
    proof fn refinement_init(c: &LowConstants, u: &LowVariables)
    requires
        low_init(c, u),
    ensures
        inductive(c, u),
        high_init(&constants_abstraction(c), &variables_abstraction(c, u)),
    { }

    // Corresponds to `inductive(c, u) && next(c, u, v) ==> inductive(c, v)`
    proof fn refinement_next(c: &LowConstants, u: &LowVariables, v: &LowVariables, event: Event)
    requires
        inductive(c, u),
        low_next(c, u, v, event),
    ensures
        inductive(c, v),
        high_next(&constants_abstraction(c), &variables_abstraction(c, u), &variables_abstraction(c, v), event),
    {
        assert(inductive(c, v)) by {
            assert(v.network.in_flight_messages.finite());
            assert(host_map_properties(c, v)) by { v.all_map_and_set_sizes_are_bounded_is_inductive(c, u, event); };
            assert(messages_in_network_implies_first_degree_properties(c, v));
            assert(properties_imply_first_degree_messages_in_network(c, v)) by {
                v.if_accept_ballot_is_some_then_accept_value_is_some_is_inductive(c, u, event);
                v.accepted_state_implies_network_has_accept_message_is_inductive(c, u, event);
                v.decided_state_implies_network_has_decide_message_is_inductive(c, u, event);
            };
            assert(properties_of_valid_messages_in_network(c, v)) by {
                v.network_msgs_have_valid_sender_and_ballot_pid_is_inductive(c, u, event);
                v.value_in_accepted_of_promise_is_same_as_proposed_value_for_corresponding_ballot_is_inductive(c, u, event);
                v.accepted_msg_in_network_implies_network_has_corresponding_accept_msg_is_inductive(c, u, event);
                v.all_decide_messages_hold_same_value_is_inductive(c, u, event);
            };
            assert(properties_of_valid_host_states(c, v)) by {
                v.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(c, u, event);
                v.any_two_hosts_with_some_same_accept_ballot_have_some_same_accept_value_is_inductive(c, u, event);
                v.same_accepted_ballots_have_same_value_in_accepted_map_in_promised_of_all_hosts_is_inductive(c, u, event);
            };
            assert(system_quorum_properties(c, v)) by {
                v.if_host_proposed_then_quorum_has_promised_is_inductive(c, u, event);
                v.if_system_accepted_exists_some_accept_value_in_future_promise_quorum_is_inductive(c, u, event);
                v.accepted_system_calculates_same_proposed_value_in_future_is_inductive(c, u, event);
                v.accepted_system_always_proposes_same_value_in_future_is_inductive(c, u, event);
            };
        };

        assert(high_next(&constants_abstraction(c), &variables_abstraction(c, u), &variables_abstraction(c, v), event)) by {
            assert(host_map_properties(c, v));
            inductive_is_safe(c, v);

            let Transition::HostStep { host_id, instance: step_key, net_op } = choose |transition: Transition| is_valid_transition(c, u, v, transition, event);
            let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id]);

            match (event) {
                Event::Decide { key, value } => {
                    assert(forall |i: int| #![auto] 0 <= i < u.hosts.len() ==> v.hosts[i].instances.dom() == u.hosts[i].instances.dom());

                    let old_calculated_map = Map::new(
                        |key: nat| (exists |i: int| #![auto] 0 <= i < u.hosts.len() && u.hosts[i].instances.contains_key(key) && u.hosts[i].instances[key].decide_value.is_some()),
                        |key: nat| {
                            let host = choose |i: int| #![auto] 0 <= i < u.hosts.len() && u.hosts[i].instances.contains_key(key) && u.hosts[i].instances[key].decide_value.is_some();
                            u.hosts[host].instances[key].decide_value.unwrap()
                        },
                    );

                    let new_calculated_map = Map::new(
                        |key: nat| (exists |i: int| #![auto] 0 <= i < v.hosts.len() && v.hosts[i].instances.contains_key(key) && v.hosts[i].instances[key].decide_value.is_some()),
                        |key: nat| {
                            let host = choose |i: int| #![auto] 0 <= i < v.hosts.len() && v.hosts[i].instances.contains_key(key) && v.hosts[i].instances[key].decide_value.is_some();
                            v.hosts[host].instances[key].decide_value.unwrap()
                        },
                    );

                    assert(new_calculated_map.dom() =~= old_calculated_map.dom().insert(key));

                    if (old_calculated_map.contains_key(key)) {
                        assert(new_calculated_map[key] == old_calculated_map[key]);
                    }

                    assert(new_calculated_map =~= old_calculated_map.insert(key, value));
                    assert(high_next(&constants_abstraction(c), &variables_abstraction(c, u), &variables_abstraction(c, v), event));
                },
                Event::NoOp => {
                    if (host::init_request(lc, lu, lv, step_key, net_op)) {
                        assert(forall |i: int| #![auto] 0 <= i < u.hosts.len() && i != host_id ==> v.hosts[i].instances.dom() == u.hosts[i].instances.dom());
                    } else {
                        assert(forall |i: int| #![auto] 0 <= i < u.hosts.len() ==> v.hosts[i].instances.dom() == u.hosts[i].instances.dom());
                    }

                    assert(forall |i: int, key: nat| #![auto]
                        0 <= i < u.hosts.len() &&
                        u.hosts[i].instances.contains_key(key) ==>
                        v.hosts[i].instances[key].decide_value == u.hosts[i].instances[key].decide_value);

                    let old_calculated_map = Map::new(
                        |key: nat| (exists |i: int| #![auto] 0 <= i < u.hosts.len() && u.hosts[i].instances.contains_key(key) && u.hosts[i].instances[key].decide_value.is_some()),
                        |key: nat| {
                            let host = choose |i: int| #![auto] 0 <= i < u.hosts.len() && u.hosts[i].instances.contains_key(key) && u.hosts[i].instances[key].decide_value.is_some();
                            u.hosts[host].instances[key].decide_value.unwrap()
                        },
                    );

                    let new_calculated_map = Map::new(
                        |key: nat| (exists |i: int| #![auto] 0 <= i < v.hosts.len() && v.hosts[i].instances.contains_key(key) && v.hosts[i].instances[key].decide_value.is_some()),
                        |key: nat| {
                            let host = choose |i: int| #![auto] 0 <= i < v.hosts.len() && v.hosts[i].instances.contains_key(key) && v.hosts[i].instances[key].decide_value.is_some();
                            v.hosts[host].instances[key].decide_value.unwrap()
                        },
                    );

                    assert(variables_abstraction(c, u).decided_value =~= old_calculated_map);
                    assert(variables_abstraction(c, v).decided_value =~= new_calculated_map);

                    assert(new_calculated_map =~= old_calculated_map);
                    assert(high_next(&constants_abstraction(c), &variables_abstraction(c, u), &variables_abstraction(c, v), event));
                },
            };
        };
    }

    // Corresponds to `inductive(c, u) ==> safety(c, u)`
    proof fn inductive_is_safe(c: &LowConstants, u: &LowVariables)
    requires
        inductive(c, u)
    ensures
        safety(c, u)
    { }
}
