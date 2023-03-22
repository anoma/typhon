

// a simple ping and pong interaction between two or more actors
use stateright::actor::*;

use std::{borrow::Cow, collections::BTreeMap};
// use std::net::{SocketAddrV4, Ipv4Addr};

// type RequestId = u64;
use serde::{Deserialize, Serialize};

// we have a "global" type of messages
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
enum MessageEnum {
    Ping(),
    Pong(u64),
}

use crate::MessageEnum::*;

// each actor may have some immutable parameters
#[derive(Clone)]
struct PingPongActor {
    // a parameter for whether to start the interaction
    // by sending to some actor with the given id
    start: Option<Id>,
    // TODO add "silent mode" for exploration / model checking 
}

// the global state type
// typically this is an Enum and the "delegation pattern" via ambassador
// the state has
// - the immutable id
// - a counter for counting the interactions
// - whether an actor awaits a ping-response, i.e., a Pong
type ActorState = (Id, u64, Option<Id>);

// First we specify the behavior of AnActor
impl Actor for PingPongActor {
    type Msg = MessageEnum;
    type State = ActorState;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        println!("Starting {}", id);
        let mut init = None;
        if let Some(the_id) = self.start {
            init = Some(the_id);
            o.send(the_id, Ping());
        } else {};

        (id, 0, init) // default value for one ping pong
    }

    fn on_msg(
        &self,
        id: Id,
        state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg,
        o: &mut Out<Self>,
    ) {
        match msg {
            Ping() => {
                // we respond to every message
                o.send(src, Pong(state.1));
                println!("will eventually respond to {} with Pong from {}", src, id);
            }
            Pong(n) => {
                // we respond to Pongs only if we "requested them"
                if let Some(i) = state.2 {
                    // check that the sender is who we asked
                    if i == src {
                        *state.to_mut() = (state.0, n + state.1, None);
                        // now, Ping again to
                        o.send(src, Ping());
                        println!("will eventually send Ping from {} to {}", id, src);
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
    number_of_actors: u16,
    // the (partial) map of initial pings
    logical_map: BTreeMap<u16, u16>,
    // the network (just to show that this is a paramter)
    network_model: Network<<PingPongActor as Actor>::Msg>,
    // port assignment, one for each actor (for spawning locally)
    port_map : BTreeMap<u16, u16>,
}

use cute::c; // for “pythonic” vec comprehension
             // simplest examples
             // const SQUARES = c![x*x, for x in 0..10];
             // const EVEN_SQUARES = c![x*x, for x in 0..10, if x % 2 == 0];

use std::net::{SocketAddrV4, Ipv4Addr};


// generate a model id from u16 (right now, a wrapped u16)
fn model_id_of(i : u16) -> Id{
    Id::from(i as usize)
}

impl PingPongCfg {

    fn spawn_id_of(&self, logical_id : u16) -> Id{
        if let Some(port) = self.port_map.get(&logical_id) {
            Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, *port))
        } else {
            panic!();
        }
    }

    // fn get_model_ids(&self) -> Vec<Id>{
    //     c![model_id_of(i), for i in 0..self.number_of_actors]
    // }

    // fn get_spawn_ids(&self) -> Vec<Id>{
    //     c![self.spawn_id_of(i), for i in 0..self.number_of_actors]
    // }

    fn get_model_map_vec(&self) -> Vec<(Id,Option<Id>)>{
        c![ (model_id_of(i), 
             self.logical_map.get(&i).map(|j| model_id_of(*j))
             // if let Some(j) = 
             // {
             //     Some(model_id_of(*j))
             // } else {
             //     None
             // }
        ),
             for i in 0..self.number_of_actors
        ]
    }

    fn get_spawn_map_vec(&self) -> Vec<(Id,Option<Id>)>{
        c![ 
            (self.spawn_id_of(i), self.logical_map.get(&i).map(|j| self.spawn_id_of(*j))
             // if let Some(j) = self.logical_map.get(&i) {
             //                 Some(self.spawn_id_of(*j))
             //             } else {
             //                 None
             //             }
            ),
             for i in 0..self.number_of_actors
        ]
    }

    fn get_actor_vec(&self, map_vec : Vec<(Id,Option<Id>)>) -> Vec<PingPongActor>{
        c![
            PingPongActor{start: x.1}, 
            for x in map_vec
        ]
    }

    fn into_model(self) -> ActorModel<PingPongActor, Self, ()> {
        // make a new model 
        ActorModel::new(self.clone(), ())
        // add the actors (given in terms of the structs of initial prams)
            .actors(self.get_actor_vec(self.get_model_map_vec()))
        // initialize the network (which does nothing in our example, but ... )
            .init_network(self.network_model)
    }

    // for "spawning" a model, we "just" additionally use
    // a map from ids to actor paramter struct
    fn into_spawnable(self) -> Vec<(Id,PingPongActor)>{
        c![
            (x.0,PingPongActor{start: x.1}), 
            for x in self.get_spawn_map_vec()
        ]
    }
}

#[macro_use]
extern crate lazy_static;
// our model configuration, fixed once and for all, roughly at compile time
lazy_static! {
    static ref PING_PONG : PingPongCfg = PingPongCfg{
        // we have two actors
        number_of_actors:2,
        // starting to ping each other 
        logical_map: BTreeMap::from([(0,1),(1,0)]),
        // just to show that the model has certain network parameters
        network_model: Network::new_unordered_nonduplicating([]),
        // "actual" network ids
        port_map : BTreeMap::from([(0,3001),(1,3002)]),
    };
}

use std::io;
use stateright::Model;
fn main() -> io::Result<()> {
    let mut user_input = String::new();

    loop {
        let stdin = io::stdin(); // We get `Stdin` here.
        println!("Type e/E for Exploration mode and s/S for Spawning mode, or x/X for quitting!");
        stdin.read_line(&mut user_input).unwrap();
        println!("your input was : {}", user_input);

        match user_input.as_str().get(0..1).unwrap(){
            "e"|"E" => {
                // exploration mode
                println!("Good choice, open a browser at `localhost:3000` and enjoy!");
                let address = String::from("localhost:3000");
                crate::PING_PONG.clone()
                    .into_model()
                    .checker()
                    .threads(num_cpus::get())
                    .serve(address);
                break;
            },
            "s"|"S" => {
                // spawning based on the "same" configuration
                spawn(
                    serde_json::to_vec,
                    |bytes| serde_json::from_slice(bytes),
                    PING_PONG.clone().into_spawnable()
                ).unwrap();
                break;
            },
            "x"|"X" => {
                break;
            },
            _ => {println!("Please press only one of the mentioned options");
            }
        }
    }
    Ok(())
}
