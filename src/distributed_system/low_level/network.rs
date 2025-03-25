use super::Message;
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    #[verifier::ext_equal]
    pub struct Variables {
        pub in_flight_messages: Set<Message>,
    }
}
