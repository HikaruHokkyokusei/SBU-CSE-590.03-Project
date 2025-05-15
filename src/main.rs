use crate::distributed_system::{
    inductive_is_safe,
    low_level::{inductive as low_inductive, init as low_init, safety as low_safety},
    refinement_init,
};
use implementation::{constants_abstraction, variables_abstraction, Constants, Variables};
use std::collections::{HashMap, HashSet};
use vstd::{prelude::*, std_specs::hash::obeys_key_model};

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

    pub proof fn axiom_message_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<implementation::Message>(),
    { admit(); }

    pub proof fn axiom_ballot_obeys_hash_table_key_model()
    ensures
        #[trigger] obeys_key_model::<implementation::host::Ballot>(),
    { admit(); }
}

verus! {
    mod distributed_system;
    mod implementation;

    exec fn driver(c: &Constants, v: &mut Variables)
    requires
        old(v).well_formed(c),
        forall |i: int| #![auto] 0 <= i < old(v).hosts@.len() ==> old(v).hosts@[i].current_instance == 0,
        low_init(&constants_abstraction(&c), &variables_abstraction(&c, &old(v))),
    ensures
        v.well_formed(c),
        low_safety(&constants_abstraction(&c), &variables_abstraction(&c, v)),
    {
        let ghost low_constants = constants_abstraction(&c);
        let ghost mut low_variables = variables_abstraction(&c, v);

        proof! {
            refinement_init(&low_constants, &low_variables);
            assert(low_inductive(&low_constants, &low_variables));
        };

        let mut current_instance: u64 = 0;
        proof! {
            assert(forall |i: int| #![auto] 0 <= i < v.hosts@.len() ==> v.hosts@[i].current_instance == current_instance);
            assert(forall |i: int, instance: nat| #![auto] 0 <= i < v.hosts@.len() && 0 <= instance <= u64::MAX ==> !v.into_spec().hosts[i].instances.contains_key(instance));
            assert(forall |i: int, instance: nat| #![auto] 0 <= i < low_variables.hosts.len() && 0 <= instance <= u64::MAX ==> !low_variables.hosts[i].instances.contains_key(instance));
        };

        while current_instance < u64::MAX
        invariant
            v.well_formed(c),
            v.into_spec().well_formed(&c.into_spec()),
            low_variables == variables_abstraction(c, v),
            forall |i: int| #![auto] 0 <= i < v.hosts@.len() ==> v.hosts@[i].current_instance == current_instance,
            forall |i: int, instance: nat| #![auto] 0 <= i < v.hosts@.len() && current_instance < instance <= u64::MAX ==> !v.into_spec().hosts[i].instances.contains_key(instance),
            forall |i: int, instance: nat| #![auto] 0 <= i < low_variables.hosts.len() && current_instance < instance <= u64::MAX ==> !low_variables.hosts[i].instances.contains_key(instance),
            low_inductive(&low_constants, &low_variables),
        decreases
            u64::MAX - current_instance,
        {
            v.all_host_next_intance(&c);
            current_instance += 1;

            proof! {
                low_variables = variables_abstraction(c, v);
                assert(forall |i: int| #![auto] 0 <= i < v.hosts@.len() ==> v.hosts@[i].current_instance == current_instance);
                assert(forall |i: int| #![auto] 0 <= i < low_variables.hosts.len() ==> !low_variables.hosts[i].instances.contains_key(v.hosts@[i].current_instance as nat));
            };

            v.all_host_init_request(&c);
            proof! { low_variables = variables_abstraction(c, v); };
        };

        proof! {
            inductive_is_safe(&low_constants, &low_variables);
            assert(low_safety(&low_constants, &low_variables));
        };
    }

    exec fn main() {
        let c = Constants::new(3);
        let mut v = Variables::new(&c);

        driver(&c, &mut v);
    }
}
