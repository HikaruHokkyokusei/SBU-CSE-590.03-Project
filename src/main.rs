use distributed_system::{
    constants_abstraction,
    high_level::init as high_init,
    low_level::{
        inductive, init as low_init, Constants as LowConstants, Variables as LowVariables,
    },
    variables_abstraction,
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

    fn main() { }
}
