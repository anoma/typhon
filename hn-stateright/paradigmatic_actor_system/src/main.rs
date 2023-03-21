// a simple ping and pong interaction between two or more actors
use stateright::actor::{*};
use std::borrow::Cow; 
// use std::net::{SocketAddrV4, Ipv4Addr};

// type RequestId = u64;

// we have a "global" type of messages
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum MessageEnum {
    Ping(),
    Pong(u64),
}

use crate::MessageEnum::*;

// each actor may have some immutable parameters
#[derive(Clone)]
struct AnActor{
    // a parameter for whether to start the interaction
    // by sending to some actor with the given id
    start : Option<Id>,
}

// the global state type 
// typically this is an Enum and the "delegation pattern" via ambassador
// the state has
// - the immutable id
// - a counter for counting the interactions
// - whether an actor awaits a ping-response, i.e., a Pong
type ActorState = (Id, u64, Option<Id>); 

// This is the 
impl Actor for AnActor {
    type Msg = MessageEnum;
    type State = ActorState;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {

        let mut init = None;
        if let Some(i) = self.start {
            init = Some(i);
            o.send(i, Ping());
        };
        (id, 0, init) // default value for one ping pong
    }

    fn on_msg(&self, _id: Id, state: &mut Cow<Self::State>,
              src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        match msg {
            Ping() => {
                // we respond to every message
                o.send(src, Pong(state.1));
            },
            Pong(n) => {
                // we respond to Pongs only if we "requested them"
                if let Some(i) = state.2 {
                    // check that the sender is who we asked
                    if i == src {
                        *state.to_mut() = (state.0, n+state.1, None);
                        // now, Ping again to keep the ball rolling
                        o.send(src, Ping());
                    }
                } else {}
            },
            // _ => {} nothing else
        }
    }
}

fn main(){
}

