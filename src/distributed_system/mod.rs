pub mod coordinator;
pub mod host;
pub mod network;

use vstd::prelude::*;

verus! {
    pub enum Decision {
        Commit,
        Abort,
    }

    pub enum Message {
        VoteRequest,
        Vote { sender: int, vote: host::Vote },
        Decision { decision: Decision },
    }

    pub struct MessageOps {
        pub send: Option<Message>,
        pub recv: Option<Message>,
    }

    pub struct Constants {
        pub num_hosts: int,
        pub coordinator: coordinator::Constants,
        pub hosts: Seq<host::Constants>,
        pub network: network::Constants,
    }

    pub struct Variables {
        pub coordinator: coordinator::Variables,
        pub hosts: Seq<host::Variables>,
        pub network: network::Variables,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.num_hosts > 0
            &&& self.hosts.len() == self.num_hosts
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.hosts.len() == c.hosts.len()
            &&& self.coordinator.well_formed(&c.coordinator, c.num_hosts)
            &&& forall |idx: int| #![auto] 0 <= idx < self.hosts.len() ==> self.hosts[idx].well_formed(&c.hosts[idx], idx)
            &&& self.network.well_formed(&c.network)
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& coordinator::init(&c.coordinator, &u.coordinator, c.num_hosts)
        &&& forall |idx: int| #![auto] 0 <= idx < u.hosts.len() ==> host::init(&c.hosts[idx], &u.hosts[idx], idx)
        &&& network::init(&c.network, &u.network)
    }

    pub enum Transition {
        CoordinatorStep { message_ops: MessageOps },
        HostStep { host_id: int, message_ops: MessageOps }
    }

    pub open spec fn coordinator_step(c: &Constants, u: &Variables, v: &Variables, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c)
        &&& coordinator::step(&c.coordinator, &u.coordinator, &v.coordinator, message_ops)
        &&& v.hosts == u.hosts
        &&& network::step(&c.network, &u.network, &v.network, message_ops)
        &&& v.well_formed(c)
    }

    pub open spec fn host_step(c: &Constants, u: &Variables, v: &Variables, host_id: int, message_ops: MessageOps) -> bool {
        &&& u.well_formed(c)
        &&& v.coordinator == u.coordinator
        &&& {
            &&& 0 <= host_id < u.hosts.len()
            &&& host::step(&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id], message_ops)
            &&& forall |i: int| 0 <= i < v.hosts.len() && i != host_id ==> u.hosts[i] == v.hosts[i]
        }
        &&& network::step(&c.network, &u.network, &v.network, message_ops)
        &&& v.well_formed(c)
    }

    pub open spec fn is_valid_transition(c: &Constants, u: &Variables, v: &Variables, transition: Transition) -> bool {
        match transition {
            Transition::CoordinatorStep { message_ops } => coordinator_step(c, u, v, message_ops),
            Transition::HostStep { host_id, message_ops } => host_step(c, u, v, host_id, message_ops)
        }
    }

    pub open spec fn next(c: &Constants, u: &Variables, v: &Variables) -> bool {
        exists |transition: Transition| is_valid_transition(c, u, v, transition)
    }

    pub open spec fn safety(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& (u.coordinator.decision == Some(Decision::Commit)) ==> (forall |i: int| 0 <= i < u.coordinator.votes.len() ==> u.coordinator.votes[i] == Some(host::Vote::Yes))
        &&& forall |i: int| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].decision.is_some() ==>
                u.hosts[i].decision == u.coordinator.decision
    }

    pub open spec fn vote_message_agrees_with_vote(c: &Constants, u: &Variables) -> bool {
        forall |message: Message| #![auto]
            u.network.sent_messages.contains(message) ==>
            if let Message::Vote { sender, vote } = message {
                &&& 0 <= sender < c.hosts.len()
                &&& vote == c.hosts[sender].vote
            } else {
                true
            }
    }

    pub open spec fn decision_message_agrees_with_decision(c: &Constants, u: &Variables) -> bool {
        forall |message: Message| #![auto]
            u.network.sent_messages.contains(message) ==>
            if let Message::Decision { decision } = message {
                &&& u.coordinator.decision == Some(decision)
            } else {
                true
            }
    }

    pub open spec fn vote_has_vote_message(c: &Constants, u: &Variables) -> bool {
        forall |i: int| #![auto]
            0 <= i < u.coordinator.votes.len() &&
            u.coordinator.votes[i].is_some() ==>
            u.network.sent_messages.contains(Message::Vote { sender: i, vote: u.coordinator.votes[i].unwrap() })
    }

    pub open spec fn inductive(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& vote_message_agrees_with_vote(c, u)
        &&& decision_message_agrees_with_decision(c, u)
        &&& vote_has_vote_message(c, u)
        &&& (u.coordinator.decision == Some(Decision::Commit)) ==> (forall |i: int| 0 <= i < u.coordinator.votes.len() ==> u.coordinator.votes[i] == Some(host::Vote::Yes))
        &&& forall |i: int| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].decision.is_some() ==>
                u.hosts[i].decision == u.coordinator.decision
    }
}
