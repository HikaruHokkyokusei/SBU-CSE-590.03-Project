mod distributed_system;

use distributed_system::{
    all_hosts_zero_counter_sum_is_zero, constants_abstraction,
    high_level::init as high_init,
    low_level::{
        inductive, init as low_init, Constants as LowConstants, Message, Variables as LowVariables,
    },
    variables_abstraction,
};
use vstd::prelude::*;

verus! {
    // Corresponds to `init(c, u) ==> inductive(c, u)`
    proof fn refinement_init(c: &LowConstants, u: &LowVariables)
    requires
        low_init(c, u),
    ensures
        inductive(c, u),
        high_init(&constants_abstraction(c), &variables_abstraction(c, u)),
    {
        assert((forall |i: int| #![auto] 0 <= i < u.hosts.len() ==> !u.hosts[i].holds_counter) ==> (exists |m: Message| u.network.in_flight_messages =~= set![m])) by {
            assert(u.hosts[0].holds_counter);
            assert(exists |i: int| #![auto] 0 <= i < u.hosts.len() ==> u.hosts[i].holds_counter);
        };

        let high_constants = constants_abstraction(c);
        let high_variables = variables_abstraction(c, u);
        all_hosts_zero_counter_sum_is_zero(u.hosts);
        assert(high_init(&high_constants, &high_variables));
    }

    fn main() { }
}
