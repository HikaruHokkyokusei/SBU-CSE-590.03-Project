use super::Message;
use crate::distributed_system::low_level::network::{
    Constants as LowConstants, Variables as LowVariables,
};
use std::collections::HashSet;

use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        in_flight_messages: HashSet<Message>,
    }

    impl Constants {
        pub closed spec fn into_spec(&self) -> LowConstants {
            LowConstants { }
        }
    }

    impl Variables {
        pub closed spec fn into_spec(&self) -> LowVariables {
            LowVariables {
                in_flight_messages: self.in_flight_messages@.map(|val: Message| val.into_spec()),
            }
        }
    }
}
