pub mod high_level;
pub mod low_level;

use vstd::prelude::*;

verus! {
    pub enum Event {
        Increment,
        NoOp,
    }
}
