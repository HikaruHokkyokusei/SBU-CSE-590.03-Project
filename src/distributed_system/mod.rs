use high_level::{Constants as HighConstants, Variables as HighVariables};
use low_level::{Constants as LowConstants, Variables as LowVariables};
use vstd::prelude::*;

verus! {
    pub mod high_level;
    pub mod low_level;

    pub type Value = int;

    pub enum Event {
        Decide { value: Value },
        NoOp,
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
            decided_value: if (exists |i: int| #![auto] 0 <= i < lv.hosts.len() && lv.hosts[i].decide_value.is_some()) {
                let i = choose |i: int| #![auto] 0 <= i < lv.hosts.len() && lv.hosts[i].decide_value.is_some();
                lv.hosts[i].decide_value
            } else {
                None
            }
        }
    }
}
