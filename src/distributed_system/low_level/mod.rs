use super::Value;
use vstd::prelude::*;

verus! {
    pub mod host;
    pub mod network;

    pub enum Message {
        Prepare { ballot: host::Ballot },
        Promise { sender: nat, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)> },
        Accept { ballot: host::Ballot, value: Value },
        Accepted { sender: nat, ballot: host::Ballot },
        Decide { ballot: host::Ballot, value: Value },
    }

    pub struct NetworkOperation {
        pub send: Option<Message>,
        pub recv: Option<Message>,
    }

    pub struct Constants {
        pub num_failures: nat,
        pub num_hosts: nat,
        pub hosts: Seq<host::Constants>,
        pub network: network::Constants,
    }

    pub struct Variables {
        pub hosts: Seq<host::Variables>,
        pub network: network::Variables,
    }
}
