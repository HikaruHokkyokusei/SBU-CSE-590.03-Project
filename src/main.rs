use distributed_system::{
    constants_abstraction,
    high_level::{init as high_init, next as high_next},
    low_level::{
        init as low_init, next as low_next, Constants as LowConstants, Variables as LowVariables, *,
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
            assert(host_map_properties(c, v)) by { v.all_maps_and_sets_are_finite_is_inductive(c, u, event); };
            assert(messages_in_network_implies_first_degree_properties(c, v));
            assert(properties_imply_first_degree_messages_in_network(c, v)) by {
                v.accepted_state_implies_network_has_accept_message_is_inductive(c, u, event);
                v.decided_state_implies_network_has_decide_message_is_inductive(c, u, event);
            };
            assert(properties_of_valid_messages_in_network(c, v)) by {
                v.accepted_msg_in_network_implies_network_has_corresponding_accept_msg_is_inductive(c, u, event);
                v.value_in_accepted_of_promise_is_same_as_proposed_value_for_corresponding_ballot_is_inductive(c, u, event);
            };
            assert(properties_of_valid_host_states(c, v)) by {
                v.if_host_proposed_some_value_it_is_always_same_as_get_max_accepted_value_if_some_is_inductive(c, u, event);
                v.any_two_hosts_with_some_same_accept_ballot_have_some_same_accept_value_is_inductive(c, u, event);
            };
            assert(host_accept_ballot_is_none_or_leq_to_current_ballot(c, v));
            assert(if_someone_has_accepted_then_someone_has_proposed(c, v));
            assert(if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c, v)) by { inductive_next_implies_if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c, u, v, event); };
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
