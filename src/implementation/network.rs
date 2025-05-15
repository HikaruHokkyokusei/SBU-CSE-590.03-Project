use super::{Message, NetworkOperation};
use crate::{
    axiom_message_obeys_hash_table_key_model,
    distributed_system::low_level::{
        network::{step as low_step, Constants as LowConstants, Variables as LowVariables},
        Message as LowMessage,
    },
};
use std::collections::HashSet;
use vstd::prelude::*;

verus! {
    pub struct Constants {}

    pub struct Variables {
        pub in_flight_messages: HashSet<Message>,
    }

    impl Constants {
        pub open spec fn well_formed(&self) -> bool {
            true
        }

        pub open spec fn into_spec(&self) -> LowConstants {
            LowConstants { }
        }
    }

    impl Variables {
        pub open spec fn well_formed(&self, c: &Constants) -> bool {
            &&& c.well_formed()
        }

        pub open spec fn into_spec(&self) -> LowVariables {
            LowVariables {
                in_flight_messages: Set::new(|message: LowMessage| Message::valid_spec(message) && self.in_flight_messages@.contains(Message::from_spec(message))),
            }
        }
    }

    impl Constants {
        pub exec fn new() -> Self {
            Self { }
        }
    }

    impl Clone for Variables {
        exec fn clone(&self) -> (clone: Self)
        ensures
            clone == self,
        {
            Self {
                in_flight_messages: self.in_flight_messages.clone(),
            }
        }
    }

    impl Variables {
        pub exec fn new() -> (res: Self)
        ensures
            res.in_flight_messages@.is_empty(),
        {
            Self {
                in_flight_messages: HashSet::new(),
            }
        }

        pub exec fn fill_in_flight_messages(&mut self, msg: Message)
        ensures ({
            let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());

            &&& new_spec =~= LowVariables { in_flight_messages: old_spec.in_flight_messages.insert(msg.into_spec()) }
            &&& self.in_flight_messages@ == old(self).in_flight_messages@.insert(msg)
        })
        {
            self.in_flight_messages.insert(msg);
            proof! {
                axiom_message_obeys_hash_table_key_model();
                let (old_spec, new_spec) = (old(self).into_spec(), self.into_spec());
                assert(new_spec.in_flight_messages =~= old_spec.in_flight_messages.insert(msg.into_spec()));
            };
        }

        pub exec fn step(&mut self, c: &Constants, net_op: &NetworkOperation)
        requires
            net_op.recv.is_some() ==> old(self).in_flight_messages@.contains(net_op.recv.unwrap()),
        ensures
            low_step(&c.into_spec(), &old(self).into_spec(), &self.into_spec(), net_op.into_spec()),
            net_op.send.is_some() ==> self.in_flight_messages@ =~= old(self).in_flight_messages@.insert(net_op.send.unwrap()),
        {
            if let Some(send) = net_op.send.as_ref() {
                self.fill_in_flight_messages(send.clone());
            }
        }
    }
}
