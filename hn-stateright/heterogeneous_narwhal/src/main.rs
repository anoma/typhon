// `main.rs` of heterogeneous narwhal

use stateright::actor::{*};
use std::borrow::Cow; // https://doc.rust-lang.org/std/borrow/enum.Cow.html
// use std::net::{SocketAddrV4, Ipv4Addr};

// Dummy Message Kind
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct Dummy; // FIXME

// the enumeration of all possible message types
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum MessageEnum {
    SomeKindOfMessage(Dummy), // FIXME
}

use crate::MessageEnum::*;

// the state type of workers
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct WorkerState;
// the state type of primaries
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct PrimaryState;

// states can be either of a worker or a primary
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum StateEnum {
    Worker(WorkerState),
    Primary(PrimaryState),
}

use crate::StateEnum::*;


#[derive(Clone)]
struct WorkerActor{
    // some immutable information
    info : (), 
}

#[derive(Clone)]
struct PrimaryActor{
    // some immutable information
    info : (), 
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
                o.send(src, SomeKindOfMessage(Dummy{}));
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
                o.send(src, SomeKindOfMessage(Dummy{}));
            }
        }
    }
}

