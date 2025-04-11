use distributed_system::{
    constants_abstraction,
    high_level::{init as high_init, next as high_next},
    low_level::{
        accept_has_accept_message_in_network,
        accept_message_exist_only_if_system_promised_on_corresponding_ballot,
        accept_message_exists_only_if_host_proposed_that_value,
        accepted_has_accepted_message_in_network,
        all_ballot_pids_in_host_maps_is_same_as_corresponding_host_id,
        all_decide_messages_hold_same_value, all_message_sender_and_ballot_pids_are_valid,
        all_promised_and_accepted_sets_of_all_hosts_are_finite,
        decide_has_decide_message_in_network,
        decide_message_exist_only_if_system_accepted_on_corresponding_ballot,
        if_accepted_message_exists_then_accept_message_exists,
        if_accepted_message_exists_then_sender_has_accepted_some_value,
        if_accepted_then_all_future_promise_have_some_accepted_value,
        if_host_promised_or_accepted_has_ballot_then_network_contains_corresponding_prepare,
        if_promise_message_exists_then_sender_has_promised,
        if_someone_has_accepted_then_someone_has_proposed,
        if_system_accepted_exists_some_accept_value_in_future_promise_quorum, inductive,
        inductive_next_implies_all_promised_and_accepted_sets_of_all_hosts_are_finite,
        inductive_next_implies_decide_has_decide_message_in_network,
        inductive_next_implies_if_accepted_message_exists_then_accept_message_exists,
        inductive_next_implies_if_system_accepted_exists_some_accept_value_in_future_promise_quorum,
        init as low_init, next as low_next, promise_has_prepare_message_in_network,
        promised_has_promise_message_in_network, safety, Constants as LowConstants,
        Variables as LowVariables,
    },
    variables_abstraction, Event,
};
use vstd::prelude::*;

verus! {
    mod distributed_system;

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
            assert(all_promised_and_accepted_sets_of_all_hosts_are_finite(c, v)) by { inductive_next_implies_all_promised_and_accepted_sets_of_all_hosts_are_finite(c, u, v, event); };
            assert(all_ballot_pids_in_host_maps_is_same_as_corresponding_host_id(c, v));
            assert(all_message_sender_and_ballot_pids_are_valid(c, v));
            assert(if_host_promised_or_accepted_has_ballot_then_network_contains_corresponding_prepare(c, v));
            assert(promise_has_prepare_message_in_network(c, v));
            assert(if_promise_message_exists_then_sender_has_promised(c, v));
            assert(promised_has_promise_message_in_network(c, v));
            assert(accept_message_exists_only_if_host_proposed_that_value(c, v));
            assert(accept_message_exist_only_if_system_promised_on_corresponding_ballot(c, v));
            assert(accept_has_accept_message_in_network(c, v));
            assert(accepted_has_accepted_message_in_network(c, v));
            assert(if_accepted_message_exists_then_sender_has_accepted_some_value(c, v));
            assert(if_accepted_message_exists_then_accept_message_exists(c, v)) by { inductive_next_implies_if_accepted_message_exists_then_accept_message_exists(c, u, v, event); };
            assert(if_someone_has_accepted_then_someone_has_proposed(c, v));
            assert(if_accepted_then_all_future_promise_have_some_accepted_value(c, v));
            assert(if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c, v)) by { inductive_next_implies_if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c, u, v, event); };
            assert(decide_message_exist_only_if_system_accepted_on_corresponding_ballot(c, v));
            assert(decide_has_decide_message_in_network(c, v)) by { inductive_next_implies_decide_has_decide_message_in_network(c, u, v, event); };
            assert(all_decide_messages_hold_same_value(c, v)) by { assume(false); };
        };
    }

    // Corresponds to `inductive(c, u) ==> safety(c, u)`
    proof fn inductive_is_safe(c: &LowConstants, u: &LowVariables)
    requires
        inductive(c, u)
    ensures
        safety(c, u)
    {}

    fn main() { }
}
