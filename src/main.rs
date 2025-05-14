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

    fn main() { }
}
