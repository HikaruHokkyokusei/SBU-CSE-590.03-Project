mod distributed_system;

use distributed_system::{
    decision_message_agrees_with_decision, host, inductive, init, is_valid_transition, next,
    safety, vote_has_vote_message, vote_message_agrees_with_vote, Constants, Decision, Transition,
    Variables,
};
use vstd::prelude::*;

verus! {
    pub proof fn ensures_safety(c: &Constants, u: &Variables, v: &Variables)
    ensures
        init(c, u) ==> inductive(c, u),
        inductive(c, u) && next(c, u, v) ==> inductive(c, v),
        inductive(c, u) ==> safety(c, u)
    {
        assert(inductive(c, u) && next(c, u, v) ==> inductive(c, v)) by {
            assume(inductive(c, u));
            assume(next(c, u, v));
            assert(u.well_formed(c));

            assert(v.well_formed(c));
            assert(vote_message_agrees_with_vote(c, u));
            assert(decision_message_agrees_with_decision(c, u));
            assert(vote_has_vote_message(c, u));

            assert(
                (u.coordinator.decision == Some(Decision::Commit)) ==>
                (forall |i: int| 0 <= i < v.coordinator.votes.len() ==> v.coordinator.votes[i] == Some(host::Vote::Yes))
            ) by {
                assume(u.coordinator.decision == Some(Decision::Commit));

                assert forall |i: int| #![auto]
                    0 <= i < v.coordinator.votes.len() implies
                    v.coordinator.votes[i] == Some(host::Vote::Yes)
                by {
                    let transition = choose |transition: Transition| is_valid_transition(c, u, v, transition);
                    match transition {
                        Transition::CoordinatorStep { message_ops } => {},
                        Transition::HostStep { host_id, message_ops } => {},
                    }
                };
            };

            assert(forall |i: int| #![auto] 0 <= i < v.hosts.len() && v.hosts[i].decision.is_some() ==> v.hosts[i].decision == v.coordinator.decision);
        }
    }

    fn main() { }
}
