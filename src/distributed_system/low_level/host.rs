use vstd::prelude::*;

verus! {
    pub struct Constants {
        pub id: int,
    }

    pub struct Variables {
        pub holds_counter: bool,
        pub counter: int,
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
        &&& u.counter == 0
    }
}
