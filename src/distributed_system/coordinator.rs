use super::{host, Decision, Message, MessageOps};
use vstd::prelude::*;

verus! {
    pub struct Constants {
        pub num_hosts: int,
    }

    pub struct Variables {
        pub decision: Option<Decision>,
        pub votes: Seq<Option<host::Vote>>,
    }

    impl Constants {
        pub open spec fn well_formed(&self, num_hosts: int) -> bool {
            self.num_hosts == num_hosts
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants, num_hosts: int) -> bool {
            &&& c.well_formed(num_hosts)
            &&& self.votes.len() == num_hosts
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables, num_hosts: int) -> bool {
        &&& u.well_formed(c, num_hosts)
        &&& u.decision.is_none()
        &&& forall |i: int| 0 <= i < u.votes.len() ==> u.votes[i].is_none()
    }

    pub open spec fn all_votes_collected(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c, c.num_hosts)
        &&& forall |i: int| 0 <= i < u.votes.len() ==> u.votes[i].is_some()
    }

    pub open spec fn send_vote_request(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c, c.num_hosts)
        &&& message_ops.recv.is_none()
        &&& message_ops.send == Some(Message::VoteRequest)
        &&& v == u
        &&& v.well_formed(c, c.num_hosts)
    }

    pub open spec fn learn_vote(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c, c.num_hosts)
        &&& if let Some(Message::Vote { sender, vote }) = message_ops.recv {
            &&& 0 <= sender < c.num_hosts
            &&& v.votes[sender] == Some(vote)
            &&& forall |i: int| 0 <= i < v.votes.len() && i != sender ==> v.votes[i] == u.votes[i]
            &&& v.decision == u.decision
        } else {
            false
        }
        &&& message_ops.send.is_none()
        &&& v.well_formed(c, c.num_hosts)
    }

    pub open spec fn decide(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c, c.num_hosts)
        &&& v.well_formed(c, c.num_hosts)
        &&& all_votes_collected(c, u)
        &&& message_ops.recv.is_none()
        &&& {
            let decision = if (forall |i: int| 0 <= i < u.votes.len() ==> u.votes[i] == Some(host::Vote::Yes)) {
                Decision::Commit
            } else {
                Decision::Abort
            };

            &&& v.votes == u.votes
            &&& v.decision == Some(decision)
            &&& message_ops.send == Some(Message::Decision { decision })
        }
    }

    pub open spec fn step(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        ||| send_vote_request(c, u, v, message_ops)
        ||| learn_vote(c, u, v, message_ops)
        ||| decide(c, u, v, message_ops)
    }
}
