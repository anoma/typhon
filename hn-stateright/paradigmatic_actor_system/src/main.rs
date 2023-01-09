// simple ping and pong, for two actors of the same kind
use stateright::actor::{*};
use std::borrow::Cow; // https://doc.rust-lang.org/std/borrow/enum.Cow.html
// use std::net::{SocketAddrV4, Ipv4Addr};

// type RequestId = u64;

#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum PingPong {
    Ping(),
    Pong(u64),
}

use crate::PingPong::*;

#[derive(Clone)]
struct ServerActor;


impl Actor for ServerActor {
    type Msg = PingPong;
    type State = (Id, u64, bool);

    fn on_start(&self, id: Id, _o: &mut Out<Self>) -> Self::State {
        (id, 0, false) // default value for one ping pong
    }

    fn on_msg(&self, _id: Id, state: &mut Cow<Self::State>,
              src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        match msg {
            Ping() => {
                if state.2 {
                    *state.to_mut() = (state.0, 1+state.1, false);
                    o.send(src, Pong(state.1));
                } else {
                }
            }
            Pong(n) => {
                if !state.2 {
                    *state.to_mut() = (state.0, n+state.1, true);
                    o.send(src, Ping());
                } else {
                }
            }
            // _ => {} nothing else
        }
    }
}

