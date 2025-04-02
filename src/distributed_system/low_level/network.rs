use super::Message;
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    #[verifier::ext_equal]
    pub struct Variables {
        pub in_flight_messages: Set<Message>,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& true
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& u.in_flight_messages.is_empty()
    }
}
