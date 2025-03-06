use super::Message;
use vstd::prelude::*;

verus! {
    pub(crate) struct Constants {}

    pub(crate) struct Variables {
        pub(crate) sent_messages: Set<Message>
    }

    impl Constants {
        pub(crate) open spec fn well_formed(&self) -> bool {
            true
        }
    }

    impl Variables {
        pub(crate) open spec fn well_formed(&self, c: &Constants) -> bool {
            c.well_formed()
        }
    }

    pub(crate) open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& u.sent_messages.is_empty()
    }
}
