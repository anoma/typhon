// `main.rs` of Heterogeneousp Narwhal


// For hashing, we take 
// these 8 (eight) lines from doc.rust-lang.org/std/hash/index.html
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn hash_of<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

// definition of learner graph
mod learner_graph {
    // the learner graph trait uses
    use std::collections::{HashMap, HashSet};
    use std::iter::Iterator;

    // learnergraph trait
    // ... compatible with github.com/isheff/het_paxos_ref
    pub trait LearnerGraph{
        type Learner;
        type Validator;

        fn get_learners(&self) 
                        -> dyn Iterator<Item = Self::Learner>;

        fn get_quorums(&self) 
                       -> HashMap<Self::Learner, HashSet<Self::Validator>>;

        fn are_entangled(&self, learner_a : Self::Learner, learner_b :Self::Learner)
                         -> bool;
    }
}

mod pki {
    // ------- elliptic curve signatures imports (kudos to Daniel) ------
    use std::convert::TryFrom;
    use rand::thread_rng;
    use ed25519_consensus::*;

    pub trait Registry {
        fn register (&mut self, _ :stateright::actor::Id, _:VerificationKey) ->
            bool;
    }

    use std::collections::HashMap;
    pub struct KeyTable{
        map : HashMap<stateright::actor::Id, VerificationKey>,
    }
    
    impl Registry for KeyTable {
        fn register (&mut self, id : stateright::actor::Id, vk : VerificationKey) -> 
            bool{
                self.map.insert(id, vk) != None
            }
    }


    fn get_vk (sk : SigningKey) -> VerificationKey {
        VerificationKey::from(&sk)
    }

    fn private_test_ed25519_consensus(){
        
        // ------- elliptic curve signatures example usage 
        let msg = b"ed25519-consensus";

        // Signer's context
        let (vk_bytes, sig_bytes) = {
            // Generate a signing key and sign the message
            let sk = SigningKey::new(thread_rng());
            let sig = sk.sign(msg);

            // Types can be converted to raw byte arrays with From/Into
            let sig_bytes: [u8; 64] = sig.into();
            let vk_bytes: [u8; 32] = VerificationKey::from(&sk).into();

            (vk_bytes, sig_bytes)
        };

        // Verify the signature
        assert!(
            VerificationKey::try_from(vk_bytes)
                .and_then(|vk| vk.verify(&sig_bytes.into(), msg))
                .is_ok()
        );

        // -- end elliptic curves usage
    }
}



// all about actors from stateright
use stateright::actor::{*};

// this ↑ uses clone-on-write
// → doc.rust-lang.org/std/borrow/enum.Cow.html
use std::borrow::Cow;

// for spawning actors (locally)
// use std::net::{SocketAddrV4, Ipv4Addr};

// the type of transactions, sent by the client
type TxData = u64;

// the type of transaction batches, sent by the client
type Batch = Vec<TxData>;

use serde::{Serialize, Deserialize};
// worker hash data type
// serialization matters as in https://crates.io/crates/bincode
#[derive(Deserialize, Serialize,Clone,Debug,Eq,PartialEq,Hash)]
struct WorkerHashData{
    // the round
    rnd : u64, 
    // the number of txs of this worker hash
    length : usize, 
    // the hash
    hash : u64,
}

// the type of worker hash signatures
type WorkerHashSignature = [u8; 64];


// the IDs of validators
type ValidatorId = Id;

// the IDs of workers
type WorkerId = Id;

// the IDs of workers
type ClientId = Id;

// the indices of workers (globally fixed, for all validators)
type WorkerIndex = u64;

// the enumeration of all possible message types
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum MessageEnum {
    // submissions of transactions by the client/user 
    SubmitTx(TxData, ClientId), 
    // acknowledgments of transactions by the worker 
    TxAck(TxData, WorkerId),
    // broadcasting a tx (or its erasure code) to mirror workers
    TxToAll(TxData, ClientId),
    // Worker Hash / referencing a batch of transactions
    WorkerHash(WorkerHashData, WorkerHashSignature)//
}

use crate::MessageEnum::*;

const GENESIS_ROUND : u64 = 0;
const BATCH_SIZE : usize = 3;

// the state type of workers
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct WorkerState{
    // the buffer for received transactions
    tx_buffer : Vec<(TxData, ClientId)>,
    // a copy of the primary information ()
    primary : ValidatorId,
    // a copy of the mirror worker information
    mirrors : Vec<WorkerId>,
    // round number
    rnd : u64,
}

// the state type of primaries
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct PrimaryState;

// the state type of clients 
// it is the number of requests 
type ClientState = Vec<WorkerId>;

// states can be either of a worker or a primary
#[derive(Clone,Debug,Eq,PartialEq,Hash)]
enum StateEnum {
    // every actor has a signing key (seed)
    Worker(WorkerState, [u8; 32]),
    Primary(PrimaryState, [u8; 32]),
    Client(ClientState, [u8; 32]),
}

use crate::StateEnum::*;



#[derive(Clone)]
struct WorkerActor{
    // the index of a worker
    index : WorkerIndex,
    // the primary
    primary : ValidatorId,
    // the ids of workers of the same index, aka mirro workers
    mirror_workers : Vec<Id>,

}


#[derive(Clone)]
struct PrimaryActor{
    // some immutable information
    id : ValidatorId,
    //
    peer_validators : Vec<Id>,
}


#[derive(Clone,Debug,Eq,PartialEq,Hash)]
struct ClientActor{
    // some immutable information
    /// random_seed : Option<u64>,
    // initial request number
    /// initial_requests : u64,
    // function for new requests, optionally pseudo-random
    new_req : fn(u64) -> u64,
    // the vector of workers to which requests can/will be sent
    known_workers : Vec<WorkerId>,
}

// the client actor
// - sends new requests, ideally constantly and uniformly
impl Actor for ClientActor {

    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key = SigningKey::new(thread_rng()).to_bytes();
        // send a tx to every work
        let mut x = 0;
        for k in &self.known_workers{
            x = x+1; 
            o.send(*k, SubmitTx(x, id));
        }
        // the known workers are the only state of the client
        // ... so far 
        Client(self.known_workers.clone(), key) 
    }

    fn on_msg(&self, id: Id, _state: &mut Cow<Self::State>,
              src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        match msg {
            TxAck(tx, worker) => {
                let new_tx = // this should be "random", but ... 
                    if tx%2 == 0 {
                        tx / 2 
                    } else {
                        3*tx + 1
                    };
                o.send(worker, SubmitTx(new_tx, id));
            },
            _ => {}
        }
    }
}

impl Actor for WorkerActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, _id: Id, _o: &mut Out<Self>) -> Self::State {
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key_seed = SigningKey::new(thread_rng()).to_bytes();
        Worker(
            WorkerState{
                tx_buffer: vec![], 
                primary: self.primary, 
                rnd: GENESIS_ROUND,
                mirrors: self.mirror_workers.clone(), 
            },
            key_seed
        ) 
    }

    fn on_msg(&self, w_id: Id, state: &mut Cow<Self::State>,
              src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        use ed25519_consensus::SigningKey;
        match msg {
            SubmitTx(tx, client) => {
                if let Worker(state, key_seed) = state.to_mut() {
                    if client != src {
                        panic!("source not client");
                    } else {
                        // push the tx
                        state.tx_buffer.push((tx, client));
                        // ack the tx 
                        o.send(src, TxAck(tx, w_id));
                        // "broadcast" tx to mirror_workers : Vec<Id>
                        for k in &state.mirrors{
                            o.send(*k, TxToAll(tx, client));
                        }
                        if state.tx_buffer.len() >= BATCH_SIZE {
                            // create and process batch hash
                            let w_hash = WorkerHashData{
                                rnd: state.rnd,
                                length : state.tx_buffer.len(), 
                                hash : hash_of(&state.tx_buffer),
                            };
                            let w_bytes :&[u8] = &bincode::serialize(&w_hash).unwrap();
                            assert!(false);
                            let key = SigningKey::from(*key_seed);
                            let sig : WorkerHashSignature = key.sign(w_bytes).to_bytes();
                            o.send(state.primary, WorkerHash(w_hash, sig)); 
                        }
                    }
                } else {
                    // issue 
                    panic!("Worker state incorrect");
                }
            },
            _ => { 
                // o.send(src, SomeKindOfMessage(DummyMessageType{}));
            }
        }
    }
}

impl Actor for PrimaryActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, _id: Id, _o: &mut Out<Self>) ->
        Self::State {
            use ed25519_consensus::SigningKey;
            use rand::thread_rng;
            let key_seed = SigningKey::new(thread_rng()).to_bytes();
            Primary(PrimaryState{}, key_seed) // default value for one ping pongk
        }

    fn on_msg(&self, _id: Id, _state: &mut Cow<Self::State>,
              src: Id, msg: Self::Msg, o: &mut Out<Self>) {
        match msg {
            _ => { 
                //o.send(src, SomeKindOfMessage(DummyMessageType{}));
            }
        }
    }
}

fn main(){

    use ed25519_consensus::{VerificationKey,SigningKey};
    use rand::thread_rng;

    let key = SigningKey::new(thread_rng());
    let key_seed = key.to_bytes();
    let key_again : SigningKey = SigningKey::from(key_seed);
    assert!(key.to_bytes()==key_again.to_bytes());
    print!("⇒yeah, true! key.to_bytes()==key_again.to_bytes() ⇐");
    
    // ------- elliptic curve signatures example usage 
    let msg = b"ed25519-consensus";

    // Signer's context
    let (vk_bytes, sig_bytes) = {
        // Generate a signing key and sign the message
        let sk = SigningKey::new(thread_rng());
        let sig = sk.sign(msg);

        // Types can be converted to raw byte arrays with From/Into
        let sig_bytes: [u8; 64] = sig.into();
        let vk_bytes: [u8; 32] = VerificationKey::from(&sk).into();

        (vk_bytes, sig_bytes)
    };

    // Verify the signature
    assert!(
        VerificationKey::try_from(vk_bytes)
            .and_then(|vk| vk.verify(&sig_bytes.into(), msg))
            .is_ok()
    );

    // -- end elliptic curves usage
}

