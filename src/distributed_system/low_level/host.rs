use super::{Message, NetworkOperation};
use crate::distributed_system::Event;
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

    pub open spec fn increment_counter(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation, event: Event) -> bool {
        &&& u.well_formed(c, c.id)
        &&& net_op.recv.is_none()
        &&& u.holds_counter
        &&& v.holds_counter
        &&& v.counter == u.counter + 1
        &&& net_op.send.is_none()
        &&& v.well_formed(c, c.id)
    }

    pub open spec fn send_counter(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation, event: Event) -> bool {
        &&& u.well_formed(c, c.id)
        &&& net_op.recv.is_none()
        &&& u.holds_counter == true
        &&& v.holds_counter == false
        &&& v.counter == u.counter
        &&& net_op.send == Some(Message::Transfer { counter: u.counter })
        &&& v.well_formed(c, c.id)
    }

    pub open spec fn receive_counter(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation, event: Event) -> bool {
        &&& u.well_formed(c, c.id)
        &&& v.holds_counter == true
        &&& if let Some(Message::Transfer { counter }) = net_op.recv { v.counter == counter } else { false }
        &&& net_op.send.is_none()
        &&& v.well_formed(c, c.id)
    }

    pub open spec fn step(c: &Constants, u: &Variables, v: &Variables, net_op: NetworkOperation, event: Event) -> bool {
        match event {
            Event::Increment => increment_counter(c, u, v, net_op, event),
            Event::NoOp => send_counter(c, u, v, net_op, event) || receive_counter(c, u, v, net_op, event),
        }
    }
}
