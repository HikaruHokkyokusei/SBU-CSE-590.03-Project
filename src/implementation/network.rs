use super::Message;
use crate::distributed_system::low_level::{
    network::{Constants as LowConstants, Variables as LowVariables},
    Message as LowMessage,
};
use std::collections::HashSet;

use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub in_flight_messages: HashSet<Message>,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            true
        }

        pub open spec fn into_spec(&self) -> LowConstants {
            LowConstants { }
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
        }

        pub open spec fn into_spec(&self) -> LowVariables {
            LowVariables {
                in_flight_messages: Set::new(|message: LowMessage| self.in_flight_messages@.contains(Message::from_spec(message))),
            }
        }
    }

    impl Constants {
        pub exec fn new() -> Self {
            Self { }
        }
    }

    impl Variables {
        pub exec fn new() -> (res: Self)
        ensures
            res.in_flight_messages@.is_empty(),
        {
            Self {
                in_flight_messages: HashSet::new(),
            }
        }
    }
}
