use super::Message;
use vstd::prelude::*;

verus! {
    pub(crate) struct Constants {}

    pub(crate) struct Variables {
        pub(crate) sent_messages: Set<Message>
    }
}
