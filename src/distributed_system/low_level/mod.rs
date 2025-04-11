use super::{Event, Value};
use vstd::{prelude::*, set_lib::*};

verus! {
    broadcast use vstd::set_lib::group_set_properties;

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

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            &&& self.num_hosts > 0
            &&& self.num_failures > 0
            &&& self.num_hosts == ((2 * self.num_failures) + 1)
            &&& self.hosts.len() == self.num_hosts
            &&& forall |i: nat| #![auto]
                    0 <= i < self.num_hosts ==>
                    self.hosts[i as int].id == i &&
                    self.hosts[i as int].num_failures == self.num_failures
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
            &&& self.hosts.len() == c.hosts.len()
            &&& forall |idx: nat| #![auto] 0 <= idx < self.hosts.len() ==> self.hosts[idx as int].well_formed(&c.hosts[idx as int])
            &&& self.network.well_formed(&c.network)
        }
    }

    pub open spec fn init(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |idx: nat| #![auto]
                0 <= idx < u.hosts.len() ==>
                host::init(&c.hosts[idx as int], &u.hosts[idx as int], idx, u.hosts.len())
        &&& network::init(&c.network, &u.network)
    }

    pub enum Transition {
        HostStep { host_id: int, net_op: NetworkOperation }
    }

    pub open spec fn host_step(c: &Constants, u: &Variables, v: &Variables, host_id: int, net_op: NetworkOperation, event: Event) -> bool
    recommends
        u.well_formed(c),
        v.well_formed(c),
    {
        &&& {
            &&& 0 <= host_id < u.hosts.len()
            &&& host::step(&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id], net_op, event)
            &&& forall |i: int| 0 <= i < v.hosts.len() && i != host_id ==> u.hosts[i] == v.hosts[i]
        }
        &&& network::step(&c.network, &u.network, &v.network, net_op)
    }

    pub open spec fn is_valid_transition(c: &Constants, u: &Variables, v: &Variables, transition: Transition, event: Event) -> bool {
        &&& u.well_formed(c)
        &&& v.well_formed(c)
        &&& match transition {
            Transition::HostStep { host_id, net_op } => host_step(c, u, v, host_id, net_op, event)
        }
    }

    pub open spec fn next(c: &Constants, u: &Variables, v: &Variables, event: Event) -> bool {
        exists |transition: Transition| is_valid_transition(c, u, v, transition, event)
    }

    pub open spec fn safety(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& forall |i: int, j: int| #![auto]
                0 <= i < j < u.hosts.len() &&
                u.hosts[i].decide_value.is_some() &&
                u.hosts[j].decide_value.is_some() ==>
                u.hosts[i].decide_value == u.hosts[j].decide_value
    }

    pub open spec fn all_promised_and_accepted_sets_of_all_hosts_are_finite(c: &Constants, u: &Variables) -> bool {
        &&& forall |i: int| #![auto]
                0 <= i < u.hosts.len() ==>
                u.hosts[i].promised.dom().finite() &&
                u.hosts[i].proposed_value.dom().finite() &&
                u.hosts[i].accepted.dom().finite()
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].promised.contains_key(ballot) ==>
                u.hosts[i].promised[ballot].dom().finite() &&
                0 <= u.hosts[i].promised[ballot].len() <= c.num_hosts
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].accepted.contains_key(ballot) ==>
                u.hosts[i].accepted[ballot].finite() &&
                0 <= u.hosts[i].accepted[ballot].len() <= c.num_hosts
    }

    pub open spec fn all_ballot_pids_in_host_maps_is_same_as_corresponding_host_id(c: &Constants, u: &Variables) -> bool {
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].promised.contains_key(ballot) ==>
                ballot.pid == c.hosts[i].id
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].proposed_value.contains_key(ballot) ==>
                ballot.pid == c.hosts[i].id
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].accepted.contains_key(ballot) ==>
                ballot.pid == c.hosts[i].id
    }

    pub open spec fn all_message_sender_and_ballot_pids_are_valid(c: &Constants, u: &Variables) -> bool {
        &&& forall |ballot: host::Ballot| #![auto]
                u.network.in_flight_messages.contains(Message::Prepare { ballot }) ==>
                0 <= ballot.pid < u.hosts.len()
        &&& forall |sender: nat, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
                u.network.in_flight_messages.contains(Message::Promise { sender, ballot, accepted }) ==>
                0 <= sender < u.hosts.len() &&
                0 <= ballot.pid < u.hosts.len()
        &&& forall |ballot: host::Ballot, value: Value| #![auto]
                u.network.in_flight_messages.contains(Message::Accept { ballot, value }) ==>
                0 <= ballot.pid < u.hosts.len()
        &&& forall |sender: nat, ballot: host::Ballot| #![auto]
                u.network.in_flight_messages.contains(Message::Accepted { sender, ballot }) ==>
                0 <= sender < u.hosts.len() &&
                0 <= ballot.pid < u.hosts.len()
        &&& forall |ballot: host::Ballot, value: Value| #![auto]
                u.network.in_flight_messages.contains(Message::Decide { ballot, value }) ==>
                0 <= ballot.pid < u.hosts.len()
    }

    pub open spec fn if_host_promised_or_accepted_has_ballot_then_network_contains_corresponding_prepare(c: &Constants, u: &Variables) -> bool {
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].promised.contains_key(ballot) ==>
                u.network.in_flight_messages.contains(Message::Prepare { ballot })
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].proposed_value.contains_key(ballot) ==>
                u.network.in_flight_messages.contains(Message::Prepare { ballot })
        &&& forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].accepted.contains_key(ballot) ==>
                u.network.in_flight_messages.contains(Message::Prepare { ballot })
    }

    pub open spec fn promise_has_prepare_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int| #![auto]
            0 <= i < u.hosts.len() &&
            u.hosts[i].current_ballot.num > 0 ==>
            u.network.in_flight_messages.contains(Message::Prepare { ballot: u.hosts[i].current_ballot })
    }

    pub open spec fn if_promise_message_exists_then_sender_has_promised(c: &Constants, u: &Variables) -> bool {
        forall |sender: nat, ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
            u.network.in_flight_messages.contains(Message::Promise { sender, ballot, accepted }) ==>
            u.hosts[sender as int].current_ballot.cmp(&ballot) >= 0
    }

    pub open spec fn promised_has_promise_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int, ballot: host::Ballot, sender: nat| #![auto]
            0 <= i < u.hosts.len() &&
            u.hosts[i].promised.dom().contains(ballot) &&
            u.hosts[i].promised[ballot].dom().contains(sender) ==>
            u.network.in_flight_messages.contains(Message::Promise { sender, ballot, accepted: u.hosts[i].promised[ballot][sender] })
    }

    pub open spec fn accept_message_exists_only_if_host_proposed_that_value(c: &Constants, u: &Variables) -> bool {
        forall |msg: Message| #![auto]
            u.network.in_flight_messages.contains(msg) ==>
            if let Message::Accept { ballot, value } = msg {
                let leader = ballot.pid as int;

                &&& 0 <= leader < u.hosts.len()
                &&& u.hosts[leader].proposed_value.contains_key(ballot)
                &&& u.hosts[leader].proposed_value[ballot] == value
            } else {
                true
            }
    }

    pub open spec fn accept_message_exist_only_if_system_promised_on_corresponding_ballot(c: &Constants, u: &Variables) -> bool {
        forall |msg: Message| #![auto]
            u.network.in_flight_messages.contains(msg) ==>
            if let Message::Accept { ballot, .. } = msg {
                let leader = ballot.pid as int;

                &&& 0 <= leader < u.hosts.len()
                &&& u.hosts[leader].promised.contains_key(ballot)
                &&& u.hosts[leader].promised[ballot].len() > c.num_failures
            } else {
                true
            }
    }

    pub open spec fn accept_has_accept_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int| #![auto]
            0 <= i < u.hosts.len() &&
            (u.hosts[i].accept_ballot.is_some() || u.hosts[i].accept_value.is_some()) ==>
            u.hosts[i].accept_ballot.is_some() &&
            u.hosts[i].accept_value.is_some() &&
            u.network.in_flight_messages.contains(Message::Accept { ballot: u.hosts[i].accept_ballot.unwrap(), value: u.hosts[i].accept_value.unwrap() })
    }

    pub open spec fn accepted_has_accepted_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int, ballot: host::Ballot, sender: nat| #![auto]
            0 <= i < u.hosts.len() &&
            u.hosts[i].accepted.dom().contains(ballot) &&
            u.hosts[i].accepted[ballot].contains(sender) ==>
            u.network.in_flight_messages.contains(Message::Accepted { sender, ballot })
    }

    pub open spec fn if_accepted_message_exists_then_sender_has_accepted_some_value(c: &Constants, u: &Variables) -> bool {
        forall |sender: nat, ballot: host::Ballot| #![auto]
            u.network.in_flight_messages.contains(Message::Accepted { sender, ballot }) ==>
            u.hosts[sender as int].current_ballot.cmp(&ballot) >= 0 &&
            u.hosts[sender as int].accept_ballot.is_some() &&
            u.hosts[sender as int].accept_ballot.unwrap().cmp(&ballot) >= 0 &&
            u.hosts[sender as int].accept_value.is_some()
    }

    pub open spec fn if_accepted_message_exists_then_accept_message_exists(c: &Constants, u: &Variables) -> bool {
        forall |sender: nat, ballot: host::Ballot| #![auto]
            u.network.in_flight_messages.contains(Message::Accepted { sender, ballot }) ==>
            (exists |value: Value| #![auto] u.network.in_flight_messages.contains(Message::Accept { ballot, value }))
    }

    pub open spec fn if_someone_has_accepted_then_someone_has_proposed(c: &Constants, u: &Variables) -> bool {
        forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < u.hosts.len() &&
                u.hosts[i].accepted.contains_key(ballot) &&
                u.hosts[i].accepted[ballot].len() > 0 ==>
                u.hosts[i].proposed_value.contains_key(ballot)
    }

    pub open spec fn if_accepted_then_all_future_promise_have_some_accepted_value(c: &Constants, u: &Variables) -> bool {
        forall |sender: nat, accepted_ballot: host::Ballot, future_ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
            u.network.in_flight_messages.contains(Message::Accepted { sender, ballot: accepted_ballot }) &&
            future_ballot.cmp(&accepted_ballot) > 0 &&
            u.network.in_flight_messages.contains(Message::Promise { sender, ballot: future_ballot, accepted }) ==>
            accepted.is_some()
    }

    pub open spec fn if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c: &Constants, u: &Variables) -> bool {
        forall |h1: int, h2: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot| #![auto]
            0 <= h1 < u.hosts.len() &&
            0 <= h2 < u.hosts.len() &&
            u.hosts[h1].accepted.contains_key(accepted_ballot) &&
            u.hosts[h1].accepted[accepted_ballot].len() > c.num_failures &&
            future_ballot.cmp(&accepted_ballot) > 0 &&
            u.hosts[h2].promised.contains_key(future_ballot) &&
            u.hosts[h2].promised[future_ballot].len() > c.num_failures ==>
            exists |sender: nat| #![auto] u.hosts[h2].promised[future_ballot].contains_key(sender) && u.hosts[h2].promised[future_ballot][sender].is_some()
    }

    pub open spec fn decide_message_exist_only_if_system_accepted_on_corresponding_ballot(c: &Constants, u: &Variables) -> bool {
        forall |msg: Message| #![auto]
            u.network.in_flight_messages.contains(msg) ==>
            if let Message::Decide { ballot, .. } = msg {
                let leader = ballot.pid as int;

                &&& 0 <= leader < u.hosts.len()
                &&& u.hosts[leader].accepted.contains_key(ballot)
                &&& u.hosts[leader].accepted[ballot].len() > c.num_failures
            } else {
                true
            }
    }

    pub open spec fn decide_has_decide_message_in_network(c: &Constants, u: &Variables) -> bool {
        forall |i: int| #![auto]
            0 <= i < u.hosts.len() &&
            u.hosts[i].decide_value.is_some() ==>
            exists |ballot: host::Ballot| #![auto] u.network.in_flight_messages.contains(Message::Decide { ballot, value: u.hosts[i].decide_value.unwrap() })
    }

    pub open spec fn all_decide_messages_hold_same_value(c: &Constants, u: &Variables) -> bool {
        forall |msg1: Message, msg2: Message| #![auto]
            u.network.in_flight_messages.contains(msg1) &&
            u.network.in_flight_messages.contains(msg2) ==>
            match (msg1, msg2) {
                (Message::Decide { value: value1, .. }, Message::Decide { value: value2, .. }) => { value1 == value2 },
                _ => { true }
            }
    }

    pub open spec fn inductive(c: &Constants, u: &Variables) -> bool {
        &&& u.well_formed(c)
        &&& u.network.in_flight_messages.finite()
        &&& all_promised_and_accepted_sets_of_all_hosts_are_finite(c, u)
        &&& all_ballot_pids_in_host_maps_is_same_as_corresponding_host_id(c, u)
        &&& all_message_sender_and_ballot_pids_are_valid(c, u)
        &&& if_host_promised_or_accepted_has_ballot_then_network_contains_corresponding_prepare(c, u)
        &&& promise_has_prepare_message_in_network(c, u)
        &&& if_promise_message_exists_then_sender_has_promised(c, u)
        &&& promised_has_promise_message_in_network(c, u)
        &&& accept_message_exists_only_if_host_proposed_that_value(c, u)
        &&& accept_message_exist_only_if_system_promised_on_corresponding_ballot(c, u)
        &&& accept_has_accept_message_in_network(c, u)
        &&& accepted_has_accepted_message_in_network(c, u)
        &&& if_accepted_message_exists_then_sender_has_accepted_some_value(c, u)
        &&& if_accepted_message_exists_then_accept_message_exists(c, u)
        &&& if_someone_has_accepted_then_someone_has_proposed(c, u)
        &&& if_accepted_then_all_future_promise_have_some_accepted_value(c, u)
        &&& if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c, u)
        &&& decide_message_exist_only_if_system_accepted_on_corresponding_ballot(c, u)
        &&& decide_has_decide_message_in_network(c, u)
        &&& all_decide_messages_hold_same_value(c, u)
    }

/*  Redundant with `set_lib::lemma_set_disjoint_lens`
    pub proof fn union_of_disjoint_sets_implies_sum_of_lengths<T>(set1: Set<T>, set2: Set<T>)
    requires
        set1.finite(),
        set2.finite(),
        set1 * set2 =~= Set::<T>::empty()
    ensures
        (set1 + set2).len() == set1.len() + set2.len()
    decreases
        set1.len() + set2.len()
    {
        let sum_of_lengths = set1.len() + set2.len();

        if (sum_of_lengths == 0) {
            assert(set1 =~= Set::<T>::empty() && set2 =~= Set::<T>::empty());
            assert(set1 + set2 =~= Set::<T>::empty());
            assert((set1 + set2).len() == sum_of_lengths);
        } else {
            if (set1.len() > 0) {
                let x = set1.choose();

                let (left, mid) = (set1.remove(x), set![x]);
                assert(left.finite() && mid.finite() && mid.len() == 1);

                let mid_value = mid.choose();
                assert(mid.contains(mid_value) && mid_value == x);

                assert(set1.len() == left.len() + 1);
                union_of_disjoint_sets_implies_sum_of_lengths(left, set2);

                let left_right = left + set2;
                assert(left_right.len() == sum_of_lengths - 1);
                assert(set1 + set2 =~= left_right + mid);

                let complete = left_right.insert(mid_value);
                assert(complete.len() == left_right.len() + 1);
                assert(left_right + mid =~= complete);

                assert((set1 + set2).len() == set1.len() + set2.len());
            } else if (set2.len() > 0) {
                let x = set2.choose();

                let (mid, right) = (set![x], set2.remove(x));
                assert(mid.finite() && right.finite() && mid.len() == 1);

                let mid_value = mid.choose();
                assert(mid.contains(mid_value) && mid_value == x);

                assert(set2.len() == right.len() + 1);
                union_of_disjoint_sets_implies_sum_of_lengths(set1, right);

                let left_right = set1 + right;
                assert(left_right.len() == sum_of_lengths - 1);
                assert(set1 + set2 =~= left_right + mid);

                let complete = left_right.insert(mid_value);
                assert(complete.len() == left_right.len() + 1);
                assert(left_right + mid =~= complete);

                assert((set1 + set2).len() == set1.len() + set2.len());
            } else {
                assert(false);
            }
        }
    }
    */

    pub proof fn subset_intersection_size_is_same_as_subset_size<T>(small_set: Set<T>, big_set: Set<T>)
    requires
        small_set.len() >= 0,
        big_set.finite(),
        small_set.subset_of(big_set),
    ensures
        small_set.finite(),
        big_set * small_set =~= small_set,
        (big_set * small_set).len() == small_set.len(),
    decreases
        small_set.len()
    {
        let intersection = big_set * small_set;

        if (small_set =~= Set::<T>::empty()) {
            assert(intersection =~= Set::<T>::empty());
            assert(intersection.len() == small_set.len());
        } else {
            let x = small_set.choose();
            let (sub_small_set, sub_big_set) = (small_set.remove(x), big_set.remove(x));
            assert(sub_small_set.finite() && sub_big_set.finite());
            subset_intersection_size_is_same_as_subset_size(sub_small_set, sub_big_set);

            let non_existent_element_set = set![small_set.choose()];
            assert(non_existent_element_set.is_singleton());

            let sub_intersection = sub_big_set * sub_small_set;
            assert(sub_intersection.finite() && sub_intersection.intersect(non_existent_element_set) =~= Set::empty());

            assert(intersection =~= sub_intersection + non_existent_element_set);
            assert(sub_intersection.len() == sub_small_set.len());

            assert((sub_intersection + non_existent_element_set).len() == sub_intersection.len() + non_existent_element_set.len()) by {
                lemma_set_disjoint_lens(sub_intersection, non_existent_element_set);
            };
        }
    }

    pub proof fn different_sized_sets_have_non_common_element<T>(set1: Set<T>, set2: Set<T>)
    requires
        set1.finite(),
        set2.finite(),
        set1.len() < set2.len(),
    ensures
        exists |x: T| #[trigger] set2.contains(x) && !set1.contains(x)
    decreases
        set1.len()
    {
        if set1 =~= Set::<T>::empty() {
            let x = set2.choose();
            assert(set2.contains(x) && !set1.contains(x));
            assert(exists |x: T| #[trigger] set2.contains(x) && !set1.contains(x));
        } else {
            let x = set1.choose();
            different_sized_sets_have_non_common_element(set1.remove(x), set2.remove(x));
        }
    }

    pub proof fn removing_common_element_reduces_intersection_size_by_1<T>(small_set: Set<T>, big_set: Set<T>, common_element: T)
    requires
        small_set.finite(),
        big_set.finite(),
        (big_set * small_set).contains(common_element),
    ensures
        (big_set.remove(common_element) * small_set.remove(common_element)).len() == (big_set * small_set).len() - 1,
    {
        assert(small_set.contains(common_element) && big_set.contains(common_element));

        let intersection = big_set * small_set;

        let (sub_small_set, sub_big_set) = (small_set.remove(common_element), big_set.remove(common_element));
        let sub_intersection = sub_big_set * sub_small_set;

        let bridge = set![common_element];
        assert(bridge.is_singleton());

        assert(intersection =~= sub_intersection + bridge);
        assert(intersection.len() == sub_intersection.len() + bridge.len()) by {
            assert(sub_intersection * bridge =~= Set::<T>::empty());
            lemma_set_disjoint_lens(sub_intersection, bridge);
        };
    }

    pub proof fn full_set_size(full_set: Set<nat>, max_val: nat)
    requires
        max_val > 0,
        full_set =~= Set::new(|x: nat| 0 <= x < max_val),
    ensures
        full_set.finite(),
        full_set.len() == max_val,
    decreases
        max_val
    {
        if (max_val == 1) {
            assert(full_set =~= set![0]);
            assert(full_set.finite());
        } else {
            let largest_val = (max_val - 1) as nat;
            let sub_full_set = full_set.remove(largest_val);
            full_set_size(sub_full_set, largest_val);
        }
    }

    pub proof fn continuous_set_size_bounds(s: Set<nat>, max_val: nat)
    requires
        s.finite(),
        forall |x: nat| #[trigger] s.contains(x) ==> 0 <= x < max_val,
    ensures
        0 <= s.len() <= max_val
    decreases
        max_val
    {
        if (max_val == 0) {
            assert(forall |x: nat| s.contains(x) ==> 0 <= x < 0);
            assert(s =~= Set::empty());
        } else {
            assert(max_val > 0);
            let largest_value = (max_val - 1) as nat;

            let ss = if (s.contains(largest_value)) {
                s.remove(largest_value)
            } else {
                s
            };

            assert(forall |x: nat| #[trigger] ss.contains(x) ==> 0 <= x < largest_value);
            continuous_set_size_bounds(ss, largest_value);
        }
    }

    pub proof fn overlapping_sets_have_common_element(set1: Set<nat>, set2: Set<nat>, floor_half_size: nat, full_size: nat)
    requires
        set1.finite(),
        set2.finite(),
        floor_half_size > 0,
        full_size == ((2 * floor_half_size) + 1),
        forall |x: nat| #![auto] set1.contains(x) ==> 0 <= x < full_size,
        forall |x: nat| #![auto] set2.contains(x) ==> 0 <= x < full_size,
        set1.len() > floor_half_size,
        set2.len() > floor_half_size,
    ensures
        exists |x: nat| #![auto] set1.contains(x) && set2.contains(x)
    {
        assert(set1.len() + set2.len() > full_size);
        assert(set1.union(set2).len() <= full_size) by { continuous_set_size_bounds(set1.union(set2), full_size); };

        let (set1_size, set2_size) = (set1.len(), set2.len());
        let (union, intersection) = (set1 + set2, set1 * set2);
        let (union_size, intersection_size) = (union.len(), intersection.len());

        assert(set1_size + set2_size == union_size + intersection_size) by { lemma_set_intersect_union_lens(set1, set2); };

        let common_len = (set1.len() + set2.len() - (set1 + set2).len()) as nat;
        assert(common_len >= 1);
        assert(common_len == intersection_size);

        assert(intersection.len() > 0);
        let common_val = intersection.choose();
        assert(intersection.contains(common_val));
        assert(set1.contains(common_val) && set2.contains(common_val));
    }

    pub proof fn inductive_next_implies_all_promised_and_accepted_sets_of_all_hosts_are_finite(c: &Constants, u: &Variables, v: &Variables, event: Event)
    requires
        inductive(c, u),
        next(c, u, v, event),
    ensures
        all_promised_and_accepted_sets_of_all_hosts_are_finite(c, v),
    {
        assert(u.network.in_flight_messages.finite());
        assert(v.network.in_flight_messages.finite());

        let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, v, transition, event);
        let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id]);

        assert forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < v.hosts.len() &&
                v.hosts[i].promised.contains_key(ballot) implies
                0 <= v.hosts[i].promised[ballot].len() <= c.num_hosts
        by {
            assert(forall |sender: nat| #![auto] v.hosts[i].promised[ballot].contains_key(sender) ==> 0 <= sender < c.num_hosts);

            let full_set = Set::new(|x: nat| 0 <= x < c.num_hosts);
            assert(full_set.finite() && full_set.len() == c.num_hosts) by { full_set_size(full_set, c.num_hosts); };
            assert(v.hosts[i].promised[ballot].len() <= c.num_hosts) by { lemma_len_subset(v.hosts[i].promised[ballot].dom(), full_set); };
        };

        assert forall |i: int, ballot: host::Ballot| #![auto]
                0 <= i < v.hosts.len() &&
                v.hosts[i].accepted.contains_key(ballot) implies
                0 <= v.hosts[i].accepted[ballot].len() <= c.num_hosts
        by {
            assert(forall |sender: nat| #![auto] v.hosts[i].accepted[ballot].contains(sender) ==> 0 <= sender < c.num_hosts);

            let full_set = Set::new(|x: nat| 0 <= x < c.num_hosts);
            assert(full_set.finite() && full_set.len() == c.num_hosts) by { full_set_size(full_set, c.num_hosts); };
            assert(v.hosts[i].accepted[ballot].len() <= c.num_hosts) by { lemma_len_subset(v.hosts[i].accepted[ballot], full_set); };
        };
    }

    pub proof fn inductive_next_implies_if_accepted_message_exists_then_accept_message_exists(c: &Constants, u: &Variables, v: &Variables, event: Event)
    requires
        inductive(c, u),
        next(c, u, v, event),
    ensures
        if_accepted_message_exists_then_accept_message_exists(c, v),
    {
        let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, v, transition, event);
        let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id]);

        assert forall |sender: nat, ballot: host::Ballot| #![auto]
            v.network.in_flight_messages.contains(Message::Accepted { sender, ballot }) implies
            exists |value: Value| #![auto] v.network.in_flight_messages.contains(Message::Accept { ballot, value })
        by {
            match (event) {
                Event::NoOp => {
                    let condition = host::send_prepare(lc, lu, lv, net_op) ||
                        host::send_decide(lc, lu, lv, net_op) ||
                        host::promise(lc, lu, lv, net_op) ||
                        host::accept(lc, lu, lv, net_op) ||
                        host::send_accept(lc, lu, lv, net_op);

                    if (condition) {
                        assert(exists |value: Value| #![auto] v.network.in_flight_messages.contains(Message::Accept { ballot, value })) by {
                            assert(exists |value: Value| #![auto] u.network.in_flight_messages.contains(Message::Accept { ballot, value }));
                            let existing_value = choose |value: Value| #![auto] u.network.in_flight_messages.contains(Message::Accept { ballot, value });
                            assert(v.network.in_flight_messages.contains(Message::Accept { ballot, value: existing_value }));
                        };
                    }
                },
                _ => {}
            }
        };
    }

    pub proof fn inductive_next_implies_if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c: &Constants, u: &Variables, v: &Variables, event: Event)
    requires
        inductive(c, u),
        next(c, u, v, event),
    ensures
        if_system_accepted_exists_some_accept_value_in_future_promise_quorum(c, v),
    {
        assert(u.network.in_flight_messages.finite());
        assert(v.network.in_flight_messages.finite());
        assert(all_promised_and_accepted_sets_of_all_hosts_are_finite(c, v)) by { inductive_next_implies_all_promised_and_accepted_sets_of_all_hosts_are_finite(c, u, v, event); };

        let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, v, transition, event);
        let (lc, lu, lv) = (&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id]);

        assert forall |h1: int, h2: int, accepted_ballot: host::Ballot, future_ballot: host::Ballot| #![auto]
            0 <= h1 < v.hosts.len() &&
            0 <= h2 < v.hosts.len() &&
            v.hosts[h1].accepted.contains_key(accepted_ballot) &&
            v.hosts[h1].accepted[accepted_ballot].len() > c.num_failures &&
            future_ballot.cmp(&accepted_ballot) > 0 &&
            v.hosts[h2].promised.contains_key(future_ballot) &&
            v.hosts[h2].promised[future_ballot].len() > c.num_failures implies
            exists |sender: nat| #![auto] v.hosts[h2].promised[future_ballot].contains_key(sender) && v.hosts[h2].promised[future_ballot][sender].is_some()
        by {
            assert(v.hosts.len() == c.num_hosts);
            assert(c.num_hosts == ((2 * c.num_failures) + 1));
            assert(forall |x: nat| #[trigger] v.hosts[h1].accepted[accepted_ballot].contains(x) ==> 0 <= x < c.num_hosts);
            assert(forall |x: nat| #[trigger] v.hosts[h2].promised[future_ballot].contains_key(x) ==> 0 <= x < c.num_hosts);
            assert(exists |sender: nat| #[trigger] v.hosts[h1].accepted[accepted_ballot].contains(sender) && #[trigger] v.hosts[h2].promised[future_ballot].contains_key(sender)) by {
                overlapping_sets_have_common_element(v.hosts[h1].accepted[accepted_ballot], v.hosts[h2].promised[future_ballot].dom(), c.num_failures, c.num_hosts);
            };

            let common_sender = choose |sender: nat| #[trigger] v.hosts[h1].accepted[accepted_ballot].contains(sender) && #[trigger] v.hosts[h2].promised[future_ballot].contains_key(sender);
            assert(v.hosts[h1].accepted[accepted_ballot].contains(common_sender) && v.hosts[h2].promised[future_ballot].contains_key(common_sender));
            assert(v.hosts[common_sender as int].accept_value.is_some());
            assert(
                forall |ballot: host::Ballot, accepted: Option<(host::Ballot, Value)>| #![auto]
                    v.network.in_flight_messages.contains(Message::Promise { sender: common_sender, ballot, accepted }) &&
                    ballot.cmp(&accepted_ballot) > 0 ==> accepted.is_some()
            );
            assert(exists |sender: nat| #![auto] v.hosts[h2].promised[future_ballot].contains_key(sender) && v.hosts[h2].promised[future_ballot][sender].is_some());
        }
    }

    pub proof fn inductive_next_implies_decide_has_decide_message_in_network(c: &Constants, u: &Variables, v: &Variables, event: Event)
    requires
        inductive(c, u),
        next(c, u, v, event),
    ensures
        decide_has_decide_message_in_network(c, v),
    {
        assert(u.network.in_flight_messages.finite());
        assert(v.network.in_flight_messages.finite());

        let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, v, transition, event);
        let (host_c, host_u, host_v) = (&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id]);

        assert forall |i: int| #![auto]
            0 <= i < v.hosts.len() &&
            v.hosts[i].decide_value.is_some() implies
            exists |ballot: host::Ballot| #![auto] v.network.in_flight_messages.contains(Message::Decide { ballot, value: v.hosts[i].decide_value.unwrap() })
        by {
            match ((event, net_op.recv)) {
                (Event::Decide { value }, Some(Message::Decide { ballot: recv_bal, value: recv_val }))
                if (i == host_id) => {
                    assert(host::decide(host_c, host_u, host_v, net_op, value));
                    assert(recv_val == v.hosts[i].decide_value.unwrap());
                    assert(v.network.in_flight_messages.contains(Message::Decide { ballot: recv_bal, value: recv_val }));
                    assert(exists |ballot: host::Ballot| #![auto] v.network.in_flight_messages.contains(Message::Decide { ballot, value: v.hosts[i].decide_value.unwrap() }));
                },
                _ => { }
            }
        };
    }
}
