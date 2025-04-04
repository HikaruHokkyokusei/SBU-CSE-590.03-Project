use distributed_system::{
    constants_abstraction,
    high_level::{init as high_init, next as high_next},
    low_level::{
        accept_has_accept_message_in_network, accepted_has_accepted_message_in_network,
        all_decide_messages_hold_same_value, decide_has_decide_message_in_network, inductive,
        inductive_next_implies_decide_has_decide_message_in_network, init as low_init,
        next as low_next, promised_has_promise_message_in_network, safety,
        Constants as LowConstants, Variables as LowVariables,
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
            assert(promised_has_promise_message_in_network(c, v));
            assert(accept_has_accept_message_in_network(c, v));
            assert(accepted_has_accepted_message_in_network(c, v));
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
