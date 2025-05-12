use super::{Message, NetworkOperation};
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

    pub open spec fn step(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation) -> bool {
        &&& u.well_formed(c)
        &&& v.well_formed(c)
        &&& if let Some(message) = net_op.recv { u.in_flight_messages.contains(message) } else { true }
        &&& if let Some(message) = net_op.send { v.in_flight_messages =~= u.in_flight_messages.insert(message) } else { v =~= u }
    }
}
