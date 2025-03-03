pub(crate) mod host;
pub(crate) mod network;
pub(crate) mod time;

use vstd::prelude::*;

verus! {
    pub(crate) enum Decision {
        Commit,
        Abort
    }

    pub(crate) struct Constants {
        hosts: Vec<host::Constants>,
        network: network::Constants,
        time: time::Constants,
    }

    pub(crate) struct Variables {
        hosts: Vec<host::Variables>,
        network: network::Variables,
        time: time::Variables,
    }
}
