mod distributed_system;

use distributed_system::{
    all_hosts_zero_counter_sum_is_zero, conditional_host_counter_sum, constants_abstraction,
    counter_sum_eq_counter_of_only_host_holding_counter, get_counter_in_network_messages,
    high_level::{init as high_init, next as high_next},
    low_level::{
        host, inductive, init as low_init, is_valid_transition, next as low_next,
        Constants as LowConstants, Message, Transition, Variables as LowVariables,
    },
    no_host_holds_counter_sum_is_zero, variables_abstraction, Event,
};
use vstd::{calc, prelude::*};

verus! {
    // Corresponds to `init(c, u) ==> inductive(c, u)`
    proof fn refinement_init(c: &LowConstants, u: &LowVariables)
    requires
        low_init(c, u),
    ensures
        inductive(c, u),
        high_init(&constants_abstraction(c), &variables_abstraction(c, u)),
    {
        assert((forall |i: int| #![auto] 0 <= i < u.hosts.len() ==> !u.hosts[i].holds_counter) ==> (exists |m: Message| u.network.in_flight_messages =~= set![m])) by {
            assert(u.hosts[0].holds_counter);
            assert(exists |i: int| #![auto] 0 <= i < u.hosts.len() ==> u.hosts[i].holds_counter);
        };

        let high_constants = constants_abstraction(c);
        let high_variables = variables_abstraction(c, u);
        all_hosts_zero_counter_sum_is_zero(u.hosts);
        assert(high_init(&high_constants, &high_variables));
    }

    // Corresponds to `inductive(c, u) && next(c, u, v) ==> inductive(c, v)`
    proof fn refinement_next(c: &LowConstants, u: &LowVariables, v: &LowVariables, event: Event)
    requires
        inductive(c, u),
        low_next(c, u, v, event),
    ensures
        inductive(c, v),
        high_next(&constants_abstraction(c), &variables_abstraction(c, u), &variables_abstraction(c, v), event),
    {
        assert(inductive(c, v));

        assert(high_next(&constants_abstraction(c), &variables_abstraction(c, u), &variables_abstraction(c, v), event)) by {
            let Transition::HostStep { host_id, net_op } = choose |transition: Transition| is_valid_transition(c, u, v, transition, event);
            let (hc, hu, hv) = (&c.hosts[host_id], &u.hosts[host_id], &v.hosts[host_id]);

            match event {
                Event::Increment => {
                    calc! {
                        (==)
                        variables_abstraction(c, v).counter; { }
                        conditional_host_counter_sum(v.hosts) + get_counter_in_network_messages(v.network.in_flight_messages); { assert(get_counter_in_network_messages(v.network.in_flight_messages) == 0); }
                        conditional_host_counter_sum(v.hosts); { counter_sum_eq_counter_of_only_host_holding_counter(v.hosts, host_id); }
                        hv.counter;  { }
                        hu.counter + 1; { counter_sum_eq_counter_of_only_host_holding_counter(u.hosts, host_id); }
                        conditional_host_counter_sum(u.hosts) + 1; { }
                        conditional_host_counter_sum(u.hosts) + get_counter_in_network_messages(u.network.in_flight_messages) + 1; { }
                        variables_abstraction(c, u).counter + 1;
                    }
                    assert(variables_abstraction(c, v).counter == variables_abstraction(c, u).counter + 1);
                },
                Event::NoOp => {
                    if (host::send_counter(&hc, &hu, &hv, net_op, event)) {
                        calc! {
                            (==)
                            variables_abstraction(c, u).counter; { }
                            conditional_host_counter_sum(u.hosts) + get_counter_in_network_messages(u.network.in_flight_messages); { }
                            conditional_host_counter_sum(u.hosts); { counter_sum_eq_counter_of_only_host_holding_counter(u.hosts, host_id); }
                            hu.counter; { }
                            { let Message::Transfer { counter: sent_counter } = net_op.send.unwrap(); sent_counter }; {
                                let Message::Transfer { counter: sent_counter } = net_op.send.unwrap();
                                if let Some(sent_message) = net_op.send {
                                    assert(v.network.in_flight_messages =~= set![sent_message]);
                                    let Message::Transfer { counter: counter_in_network } = v.network.in_flight_messages.choose();
                                    assert(counter_in_network == sent_counter);
                                }
                            }
                            { let Message::Transfer { counter: counter_in_network } = v.network.in_flight_messages.choose(); counter_in_network }; { }
                            get_counter_in_network_messages(v.network.in_flight_messages); { no_host_holds_counter_sum_is_zero(v.hosts); }
                            conditional_host_counter_sum(v.hosts) + get_counter_in_network_messages(v.network.in_flight_messages); { }
                            variables_abstraction(c, v).counter;
                        }
                        assert(variables_abstraction(c, v) == variables_abstraction(c, u));
                    } else {
                        calc! {
                            (==)
                            variables_abstraction(c, u).counter; { }
                            conditional_host_counter_sum(u.hosts) + get_counter_in_network_messages(u.network.in_flight_messages); {
                                no_host_holds_counter_sum_is_zero(u.hosts);
                            }
                            get_counter_in_network_messages(u.network.in_flight_messages); { }
                            { let Message::Transfer { counter: counter_in_network } = u.network.in_flight_messages.choose(); counter_in_network }; {
                                let Message::Transfer { counter: recv_counter } = net_op.recv.unwrap();
                                if let Some(recv_message) = net_op.recv {
                                    assert(u.network.in_flight_messages == v.network.in_flight_messages + set![recv_message]);
                                    let Message::Transfer { counter: counter_in_network } = u.network.in_flight_messages.choose();
                                    assert(counter_in_network == recv_counter);
                                }
                            }
                            { let Message::Transfer { counter: recv_counter } = net_op.recv.unwrap(); recv_counter }; { }
                            hv.counter; { counter_sum_eq_counter_of_only_host_holding_counter(v.hosts, host_id); }
                            conditional_host_counter_sum(v.hosts); { }
                            conditional_host_counter_sum(v.hosts) + get_counter_in_network_messages(v.network.in_flight_messages); { }
                            variables_abstraction(c, v).counter;
                        }
                        assert(variables_abstraction(c, v) == variables_abstraction(c, u));
                    }
                },
            };
        };
    }

    fn main() { }
}
