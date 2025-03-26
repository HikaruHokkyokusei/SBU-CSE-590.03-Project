pub mod high_level;
pub mod low_level;

use high_level::{Constants as HighConstants, Variables as HighVariables};
use low_level::{Constants as LowConstants, Variables as LowVariables};
use vstd::prelude::*;

verus! {
    pub enum Event {
        Increment,
        NoOp,
    }

    pub open spec fn conditional_host_counter_sum(hosts: Seq<low_level::host::Variables>) -> int
    decreases
        hosts.len()
    {
        if (hosts.len() > 0) {
            let last_element = hosts.last();
            conditional_host_counter_sum(hosts.drop_last()) + if (last_element.holds_counter) { last_element.counter } else { 0 }
        } else {
            0
        }
    }

    pub open spec fn get_counter_in_network_messages(in_flight_messages: Set<low_level::Message>) -> int {
        if (in_flight_messages.len() == 1) {
            let low_level::Message::Transfer { counter } = in_flight_messages.choose();
            counter
        } else {
            0
        }
    }

    pub open spec fn constants_abstraction(lc: &LowConstants) -> HighConstants
    recommends
        lc.well_formed()
    {
        HighConstants { }
    }

    pub open spec fn variables_abstraction(lc: &LowConstants, lv: &LowVariables) -> HighVariables
    recommends
        lv.well_formed(lc)
    {
        HighVariables {
            counter: conditional_host_counter_sum(lv.hosts) + get_counter_in_network_messages(lv.network.in_flight_messages)
        }
    }
}
