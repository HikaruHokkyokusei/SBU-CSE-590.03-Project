use vstd::prelude::*;

verus! {
    pub(crate) struct Constants {
        pub(crate) ids: Vec<i64>
    }

    pub(crate) struct Variables {
        pub(crate) max_received_ids: Vec<i64>
    }

    pub(crate) open spec fn unique_values(arr: &Vec<i64>) -> bool {
        forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j]
    }

    impl Constants {
        pub(crate) open spec fn well_formed(&self) -> bool {
            self.ids.len() > 0 && unique_values(&self.ids)
        }
    }

    impl Variables {
        pub(crate) open spec fn well_formed(&self, c: &Constants) -> bool {
            c.well_formed() && self.max_received_ids.len() == c.ids.len()
        }
    }

    pub(crate) open spec fn valid_index(arr: &Vec<i64>, idx: int) -> bool {
        0 <= idx < arr.len()
    }

    pub(crate) open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |idx: int| #![auto] valid_index(&u.max_received_ids, idx) ==> (c.ids[idx] >= 0) && (u.max_received_ids[idx] == -1)
    }
}
