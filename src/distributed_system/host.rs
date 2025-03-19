use super::{Decision, MessageOps, Message};
use vstd::prelude::*;

verus! {
    pub enum Vote {
        Yes,
        No
    }

    pub struct Constants {
        pub id: int,
        pub vote: Vote
    }

    pub struct Variables {
        pub decision: Option<Decision>
    }

    impl Constants {
        pub open spec fn well_formed(&self, id: int) -> bool {
            &&& id >= 0
            &&& self.id == id
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants, id: int) -> bool {
            &&& c.well_formed(id)
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables, host_id: int) -> bool {
        &&& u.well_formed(c, host_id)
        &&& u.decision.is_none()
    }

    pub open spec fn vote(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c, c.id)
        &&& message_ops.recv == Some(Message::VoteRequest)
        &&& v.decision == if (c.vote == Vote::No) { Some(Decision::Abort) } else { u.decision }
        &&& message_ops.send == Some(Message::Vote { sender: c.id, vote: c.vote })
        &&& v.well_formed(c, c.id)
    }

    pub open spec fn learn_decision(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c, c.id)
        &&& if let Some(Message::Decision { decision }) = message_ops.recv { v.decision == Some(decision) } else { false }
        &&& message_ops.send.is_none()
        &&& v.well_formed(c, c.id)
    }

    pub open spec fn step(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        ||| vote(c, u, v, message_ops)
        ||| learn_decision(c, u, v, message_ops)
    }
}
