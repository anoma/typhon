// `main.rs` of Heterogeneous Narwhal

use stateright::actor::{*};
// clone-on-write → doc.rust-lang.org/std/borrow/enum.Cow.html
use std::borrow::Cow; 
// for spawning actors (locally)
// use std::net::{SocketAddrV4, Ipv4Addr};

// for learner graphs
use std::collections::HashMap;
use std::iter::Iterator;

// Dummy Message Kind
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct DummyMessageType; // PLACEHOLDER

// the enumeration of all possible message types
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum MessageEnum {
    SomeKindOfMessage(DummyMessageType), // PLACEHOLDER
}

use crate::MessageEnum::*;

// the state type of workers
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct WorkerState;
// the state type of primaries
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct PrimaryState;

// the state type of clients
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct ClientState;

// states can be either of a worker or a primary
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum StateEnum {
    Worker(WorkerState),
    Primary(PrimaryState),
    Client(ClientState),
}

use crate::StateEnum::*;

// learnergraph trait
trait LearnerGraph{
    type Learner;
    type Validator;

    fn get_learners(&self) 
                    -> dyn Iterator<Item = Self::Learner>;

    fn get_quorums(&self) 
                   -> HashMap<Self::Learner, Self::Validator>;

    fn are_entangled(&self, lrn_one : Self::Learner, lrn_two :Self::Learner)
                     -> bool;
}


type ValidatorID = u64;

type WorkerIndex = u64;

#[derive(Clone)]
struct WorkerActor{
    // the index of a worker
    index : WorkerIndex,
    primary : ValidatorID,
}


#[derive(Clone)]
struct PrimaryActor{
    // some immutable information
    id : ValidatorID, 
}

impl Actor for WorkerActor {
    
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, _id: Id, _o: &mut Out<Self>) -> Self::State {
        Worker(WorkerState{}) // default value for one ping pongk
    }

    fn on_msg(&self, _id: Id, _state: &mut Cow<Self::State>,
              src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        match msg {
            _ => { 
                o.send(src, SomeKindOfMessage(DummyMessageType{}));
            }
        }
    }
}

impl Actor for PrimaryActor {
    
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, _id: Id, _o: &mut Out<Self>) -> Self::State {
        Primary(PrimaryState{}) // default value for one ping pongk
    }

    fn on_msg(&self, _id: Id, _state: &mut Cow<Self::State>,
              src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        match msg {
            _ => { 
                o.send(src, SomeKindOfMessage(DummyMessageType{}));
            }
        }
    }
}

