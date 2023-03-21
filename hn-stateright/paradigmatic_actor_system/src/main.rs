// a simple ping and pong interaction between two or more actors
use stateright::actor::*;
use std::{borrow::Cow, collections::BTreeMap};
// use std::net::{SocketAddrV4, Ipv4Addr};

// type RequestId = u64;

// we have a "global" type of messages
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum MessageEnum {
    Ping(),
    Pong(u64),
}

use crate::MessageEnum::*;

// each actor may have some immutable parameters
#[derive(Clone)]
struct AnActor {
    // a parameter for whether to start the interaction
    // by sending to some actor with the given id
    start: Option<usize>,
}

// the global state type
// typically this is an Enum and the "delegation pattern" via ambassador
// the state has
// - the immutable id
// - a counter for counting the interactions
// - whether an actor awaits a ping-response, i.e., a Pong
type ActorState = (Id, u64, Option<Id>);

// First we specify the behavior of AnActor
impl Actor for AnActor {
    type Msg = MessageEnum;
    type State = ActorState;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        let mut init = None;
        if let Some(i) = self.start {
            let the_id = Id::from(i);
            init = Some(the_id);
            o.send(the_id, Ping());
        } else {};
        (id, 0, init) // default value for one ping pong
    }

    fn on_msg(
        &self,
        _id: Id,
        state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg,
        o: &mut Out<Self>,
    ) {
        match msg {
            Ping() => {
                // we respond to every message
                o.send(src, Pong(state.1));
            }
            Pong(n) => {
                // we respond to Pongs only if we "requested them"
                if let Some(i) = state.2 {
                    // check that the sender is who we asked
                    if i == src {
                        *state.to_mut() = (state.0, n + state.1, None);
                        // now, Ping again to
                        o.send(src, Ping());
                    }
                } else {
                }
            }
            // _ => {} nothing else
        }
    }
}

// The system configuration (how actors start out),
// which can become
// --
#[derive(Clone)]
struct PingPongCfg {
    // the number of actors
    number_of_actors: usize,
    // the (partial) map of initial pings
    the_map: BTreeMap<usize, usize>,
    // the network (just to show that this is a paramter)
    network: Network<<AnActor as Actor>::Msg>,
}

use cute::c; // for “pythonic” vec comprehension
             // simplest examples
             // const SQUARES = c![x*x, for x in 0..10];
             // const EVEN_SQUARES = c![x*x, for x in 0..10, if x % 2 == 0];

impl PingPongCfg {
    fn into_model(self) -> ActorModel<AnActor, Self, ()> {
        // make a new model 
        ActorModel::new(self.clone(), ())
        // add the actors (given in terms of the structs of initial prams)
            .actors(c![
                AnActor{start: 
                        if let Some(i) = self.the_map.get(&x) {
                            Some(*i)
                        } else {
                            None
                        }
                }, 
                for x in 0..self.number_of_actors]
            )
        // initialize the network (which does nothing in our example, but ... )
        .init_network(self.network)
    }
}

#[macro_use]
extern crate lazy_static;
// our model configuration, fixed once and for all, roughly at compile time
lazy_static! {
    static ref THE_CFG : PingPongCfg = PingPongCfg{
        // we have two actors
        number_of_actors:2,
        // starting to ping each other 
        the_map: BTreeMap::from([(0,1),(1,0)]),
        // just to show that the model has certain network parameters
        network: Network::new_unordered_nonduplicating([]),
    };

}
fn main() {
    // exploration mode
    let address = String::from("localhost:3000");
    use stateright::Model;
    crate::THE_CFG.clone()
        .into_model()
        .checker()
        .threads(num_cpus::get())
        .serve(address);
}
