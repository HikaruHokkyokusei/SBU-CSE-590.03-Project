pub(crate) mod coordinator;
pub(crate) mod host;
pub(crate) mod network;

use vstd::prelude::*;

verus! {
    pub(crate) enum Decision {
        Commit,
        Abort
    }

    pub(crate) enum Message {
        VoteRequest,
        Vote{ sender: int, vote: host::Vote },
        Decision{ decision: Decision }
    }

    pub(crate) struct Constants {
        pub(crate) num_hosts: int,
        pub(crate) coordinator: coordinator::Constants,
        pub(crate) hosts: Seq<host::Constants>,
        pub(crate) network: network::Constants,
    }

    pub(crate) struct Variables {
        pub(crate) coordinator: coordinator::Variables,
        pub(crate) hosts: Seq<host::Variables>,
        pub(crate) network: network::Variables,
    }
}
