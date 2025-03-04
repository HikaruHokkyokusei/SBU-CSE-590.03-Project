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

    pub(crate) enum Transition {
        MessageExchange { src: int }
    }

    pub(crate) open spec fn next_index(arr: &Vec<i64>, src: int) -> int {
        if src + 1 == arr.len() { 0 } else { src + 1 }
    }

    pub(crate) open spec fn message_exchange(c: &Constants, u: &Variables, v: &Variables, src: int) -> bool {
        &&& valid_index(&c.ids, src)
        &&& {
            let dest = next_index(&c.ids, src);
            let msg = if c.ids[src] > u.max_received_ids[src] { c.ids[src] } else { u.max_received_ids[src] };
            let new_val = if u.max_received_ids[dest] > msg { u.max_received_ids[dest] } else { msg };
            v.max_received_ids@ == u.max_received_ids@.update(dest, new_val)
        }
    }

    pub(crate) open spec fn is_valid_transition(c: &Constants, u: &Variables, v: &Variables, transition: Transition) -> bool {
        match transition {
            Transition::MessageExchange { src } => message_exchange(c, u, v, src)
        }
    }

    pub(crate) open spec fn next(c: &Constants, u: &Variables, v: &Variables) -> bool {
        exists |transition: Transition| is_valid_transition(c, u, v, transition)
    }

    pub(crate) open spec fn safety(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |i: int, j: int| #![auto]
            valid_index(&c.ids, i) &&
            valid_index(&c.ids, j) &&
            c.ids[i] == u.max_received_ids[i] &&
            c.ids[j] == u.max_received_ids[j] ==>
            i == j
    }

    pub(crate) open spec fn is_index_in_between(start: int, mid: int, end: int) -> bool {
        if end > start {
            start <= mid < end
        } else {
            (start <= mid) || (mid < end)
        }
    }

    pub(crate) open spec fn inductive(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |i: int, mid: int, j: int| #![auto]
            valid_index(&c.ids, i) &&
            valid_index(&c.ids, mid) &&
            valid_index(&c.ids, j) &&
            is_index_in_between(i, mid, j) &&
            u.max_received_ids[j] == c.ids[i] ==>
            c.ids[mid] <= c.ids[i]
    }

    pub(crate) proof fn ensures_safety(c: &Constants, u: &Variables, v: &Variables)
    ensures
        init(c, u) ==> inductive(c, u),
        inductive(c, u) && next(c, u, v) ==> inductive(c, v),
        inductive(c, u) ==> safety(c, u)
    {
        assert(init(c, u) ==> inductive(c, u)) by {
            assume(init(c, u));

            assert forall |i: int, j: int| #![auto]
                valid_index(&c.ids, i) &&
                valid_index(&c.ids, j) implies
                u.max_received_ids[j] != c.ids[i]
            by {
                assert(valid_index(&u.max_received_ids, i));
                assert(valid_index(&u.max_received_ids, j));
            };
        };

        assert(inductive(c, u) && next(c, u, v) ==> inductive(c, v)) by {
            assume(inductive(c, u));
            assume(next(c, u, v));

            assert forall |i: int, mid: int, j: int|
                valid_index(&c.ids, i) &&
                valid_index(&c.ids, mid) &&
                valid_index(&c.ids, j) &&
                is_index_in_between(i, mid, j) &&
                v.max_received_ids[j] == c.ids[i] implies
                c.ids[mid] <= c.ids[i]
            by {
                assume(u.max_received_ids[j] == c.ids[i]);
            }
        };

        assert(inductive(c, u) ==> safety(c, u)) by {
            assume(inductive(c, u));

            assert forall |i: int, j: int| #![auto]
                valid_index(&c.ids, i) &&
                valid_index(&c.ids, j) &&
                c.ids[i] == u.max_received_ids[i] &&
                c.ids[j] == u.max_received_ids[j] implies
                i == j
            by {
                assert(is_index_in_between(i, j, i));
                assert(is_index_in_between(j, i, j));
            };
        }
    }
}
