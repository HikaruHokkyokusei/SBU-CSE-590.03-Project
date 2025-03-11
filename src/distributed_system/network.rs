use super::{Message, MessageOps};
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

    pub(crate) open spec fn step(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c)
        &&& v.well_formed(c)
        // Only allow receipt of messages that have been sent
        &&& if let Some(message) = message_ops.recv { u.sent_messages.contains(message) } else { true }
        // Update sent messages with any new message
        &&& if let Some(message) = message_ops.send { v.sent_messages == u.sent_messages.insert(message) } else { true }
    }
}
