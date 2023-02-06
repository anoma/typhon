// -------------------------------------------------------
// The Heterogeneous Narwhal implementation in stateright
// -------------------------------------------------------
// 
// This code is geared toward clarity and correctness,
// w.r.t. tech report
// https://github.com/anoma/ ..
// .. research/tree/master/distributed-systems/heterogeneous-narwhal

use serde::{Deserialize,Serialize};
use std::fmt::Debug;

// For hashing,
// based on doc.rust-lang.org/std/hash/index.html,
// we use the following 8 (eight) lines of code:
use std::collections::hash_map::DefaultHasher;
use std::collections::BTreeMap;
// use std::collections::HashMap;
// fn hash_to_btree<K:std::cmp::Ord,V>(
//     hash: HashMap<K, V>
// ) -> BTreeMap<K, V> {
//     // make hashmap iterator, then collect ?!
//     hash.into_iter().collect()
// }

use cute::c; // for “pythonic” vec comprehension
             // simplest example
             //const SQUARES = c![x*x, for x in 0..10];
             //const EVEN_SQUARES = c![x*x, for x in 0..10, if x % 2 == 0];

// https://docs.rs/mapcomp/latest/mapcomp/macro.btreemapc.html
// use mapcomp::btreemapc; // for “pythonic” btree comprehension
use std::hash::{Hash, Hasher};

fn hash_of<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

// the data type of learner graphs
mod learner_graph {
    // the learner graph trait uses
    use std::collections::{HashMap,HashSet};
    use std::iter::Iterator;

    // learner graph trait
    // ... compatible with github.com/isheff/het_paxos_ref
    pub trait LearnerGraph {
        type Learner;
        type Validator;

        fn get_learners(
            &self
        ) -> dyn Iterator<Item = Self::Learner>;

        fn get_quorums(
            &self
        ) -> HashMap<Self::Learner, HashSet<Self::Validator>>;

        fn are_entangled(
            &self,
            learner_a: Self::Learner,
            learner_b: Self::Learner
        ) -> bool;
    }
}

// this module is for the purpose of “faking” a PKI-infrastructure
mod pki {
    // elliptic curve signatures imports (kudos to Daniel)
    use ed25519_consensus::*;
    use rand::thread_rng;
    use stateright::actor::Id;
    use std::collections::BTreeMap;
    use std::convert::TryFrom;

    // The Registry is responsible for
    // - regsitering keys via `register_key`
    // - lookup of verification keys via `lookup_vk`
    pub trait Registry {
        // registering a verification key for the id
        fn register_key(
            &mut self, 
            _: Id,
            _:VerificationKey,
            _: [u8; 64]
        ) -> bool;

        // looking up the key for the id
        fn lookup_vk(
            &self,
            _: Id
        ) -> Option<VerificationKey>;

    }

    pub struct KeyTable {
        pub map: BTreeMap<Id, VerificationKey>,
    }

    impl Registry for KeyTable {

        fn register_key(
            &mut self,
            id: Id,
            vk: VerificationKey, 
            _sig : [u8; 64]
        ) -> bool {
            // MENDME, add signature check
            self.map.insert(id, vk) != None
        }

        fn lookup_vk(
            &self,
            id: Id
        ) -> Option<VerificationKey> {
            if let Some(vk) = self.map.get(&id){
                Some(*vk)
            } else {
                None
            }
        }
    }

    // fn private_test_ed25519_consensus() {
    //     // ------- ed25519-consensus signatures example usage
    //     let msg = b"ed25519-consensus";
    // 
    //     // Signer's context
    //     let (vk_bytes, sig_bytes) = {
    //         // Generate a signing key and sign the message
    //         let sk = SigningKey::new(thread_rng());
    //         let sig = sk.sign(msg);
    // 
    //         // Types can be converted to raw byte arrays with From/Into
    //         let sig_bytes: [u8; 64];
    //         sig_bytes = sig.into();
    //         let vk_bytes: [u8; 32];
    //         vk_bytes = VerificationKey::from(&sk).into();
    // 
    //         (vk_bytes, sig_bytes)
    //     };

    //     // Verify the signature
    //     assert!(VerificationKey::try_from(vk_bytes)
    //         .and_then(|vk| vk.verify(&sig_bytes.into(), msg))
    //         .is_ok());
    // }
    // -- end ed25519-consensus usage
}

// all about actors from stateright
use stateright::actor::*;
use stateright::*;

// stateright uses clone-on-write for state-changes
// → doc.rust-lang.org/std/borrow/enum.Cow.html
use std::borrow::Cow;

// -------------------------------
// actual actor model starts here
// -------------------------------

// for spawning actors (locally)
// use std::net::{SocketAddrV4, Ipv4Addr};

type TxChunk = u64;
type TxData = Vec<TxChunk>;

// FIXME: batches "generic" **and** serializable -- ̈"somehow" ?!
// right now, a batch is just a vector of TxData

// worker hash data type
// serialization matters as in https://crates.io/crates/bincode
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
struct WorkerHashData {
    // the round
    rnd: u64,
    // the number of txs of this worker hash
    length: usize,
    // the hasho
    hash: u64,
}

// the hashing library uses [u8; 64], which makes us use BigArray
use serde_big_array::BigArray;

// the type of worker hash signatures
type WorkerHashSignature = [u8; 64];

// the IDs of validators is a stateright Id
type ValidatorId = Id;

// the IDs of workers is a stateright Id
type WorkerId = Id;

// the IDs of workers
type ClientId = Id;

// the indices of workers (globally fixed, for all validators)
type WorkerIndex = u64;

// the enumeration of all possible kinds of messages
//
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
enum MessageEnum {
    // transaction requests, sent by the client/user
    TxReq(TxData, ClientId),
    // acknowledgments of transactions by the worker
    TxAck(TxData, WorkerId),
    // broadcasting a tx (or its erasure code) to mirror workers
    TxToAll(TxData, ClientId, usize, u64),
    // Worker Hash (to the primary)
    WorkerHx(
        WorkerHashData,
        #[serde(with = "BigArray")] WorkerHashSignature,
    ),
    // Worker Hash (broadcast to mirror workers)
    WHxToAll(
        WorkerHashData,
        #[serde(with = "BigArray")] WorkerHashSignature,
    ),
    // Worker Hash (forwarded to primary)
    WHxOK(
        WorkerHashData,
        #[serde(with = "BigArray")] WorkerHashSignature,
    ),

}


use crate::MessageEnum::*;

const GENESIS_ROUND: u64 = 0;
const BATCH_SIZE: usize = 3;

// the state type of workers
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct WorkerState {
    // the buffer for received transactions
    tx_buffer: Vec<(TxData, ClientId)>,
    // hashmap to stores of transaction copies
    tx_buffer_map: BTreeMap<WorkerId, Vec<(TxData, ClientId, usize, u64)>>,
    // a copy of the primary information ()
    primary: ValidatorId,
    // a copy of the mirror worker information
    mirrors: Vec<WorkerId>,
    // round number
    rnd: u64,
}

// the state type of primaries
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct PrimaryState;

// the state type of clients
// it is the number of requests
type ClientState = Vec<WorkerId>;

// states can be either of a worker or a primary
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum StateEnum {
    // every actor has a signing key (seed)
    Worker(WorkerState, [u8; 32]),
    Primary(PrimaryState, [u8; 32]),
    Client(ClientState, [u8; 32]),
}

use crate::StateEnum::*;

// WorkerActor holds the static information about actors
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct WorkerActor {
    // key (as seed)
    key_seed: [u8; 32],
    // the index of a worker
    index: WorkerIndex,
    // the primary
    primary: ValidatorId,
    // the ids of workers of the same index, aka mirro workers
    mirror_workers: Vec<Id>,
    // my_expected_id is for debugging
    my_expected_id: Id,
    // round number
    rnd: u64,
}

// PrimaryActor holds the static information about primaries
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct PrimaryActor {
    // key (as seed) -- NB: this needs to be fixed before `on_start`
    key_seed: [u8; 32],
    // the ids of all (known) peer validators
    peer_validators: Vec<Id>,
    // my_expected_id (for debugging)
    my_expected_id: Id,
}

// ClientActor holds the static information about clients
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct ClientActor {
    // key (as seed) -- NB: this needs to be fixed before `on_start`
    key_seed: [u8; 32],
    // verification key,
    
    // the vector of workers to which requests can/will be sent
    known_workers: Vec<WorkerId>,
    // my_expected_id (for debugging)
    my_expected_id: Id,
}

// -----------------------------------------------------------------------------
// // experiment _delegation_ begin
// -----------------------------------------------------------------------------
// #[delegatable_trait]
// pub trait ExampleTrait : Sized {
//     fn do_this (&self, o: &mut Vec<Self>);
// }

// #[derive(Clone)]
// struct ExOne;
// #[derive(Clone)]
// struct ExTwo;


// impl ExampleTrait for ExOne {
//     fn do_this (&self, o: &mut Vec<Self>){
//         o.push(self.clone());
//     }
// }
// impl ExampleTrait for ExTwo {
//     fn do_this (&self, o: &mut Vec<Self>){
//         o.push(self.clone());
//     }
// }

// // this of course does not work, because self is changing its meaning
// // #[derive(Delegate,Clone)]
// // #[delegate(ExampleTrait)]
// // enum ExEnum {
// //     ExOne(ExOne),
// //     ExTwo(ExTwo),
// // }
// -----------------------------------------------------------------------------
// // experiment _delegation_ end
// -----------------------------------------------------------------------------



// ideally, this _would_ be part of the `Vactor` trait
// ... well, now it is public :-/ 
pub enum Outputs<I, M> {
    Snd(I, M),
    //Cast(M),
    //Timer(usize),
}

// ambassador (see also https://github.com/Heliozoa/impl-enum)
// it is used to “lift” trait implementations on enum items
// to the whole enum .. possibly repeatedly
use ambassador::{delegatable_trait, Delegate};

// The following is based on stateright's Actor trait,
// which can be lifted to enums via amabassor,
// as opposed the present Actor trait -- cf. experiement above.
// Ambassador delegates calls to the enum to the respective types
// the relation to the Actor trait is then given later by
// the Actor impl for HNActor below.

#[delegatable_trait]
pub trait Vactor: Sized {
    type Msg: Clone + Debug + Eq + Hash;
    type State: Clone + Debug + PartialEq + Hash;

    fn send(&self, id : Id, m : Self::Msg, o : &mut Vec<Outputs<Id, Self::Msg>>){
        o.push(Outputs::Snd(id, m));
    }
    fn send_(&self, ids : Vec<Id>, m : Self::Msg, o : &mut Vec<Outputs<Id, Self::Msg>>){
        for i in ids {
            self.send(i, m.clone(), o);
        }
    }
    fn on_start_vec(
        &self, id: Id
    ) -> (Self::State, Vec<Outputs<Id, Self::Msg>>);

    fn on_msg_vec(
        &self,
        id: Id,
        state: &mut Cow<'_, Self::State>,
        src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id, Self::Msg>>;

    fn on_timeout_vec(
        &self,
        _id: Id,
        _state: &mut Cow<'_, Self::State>,
    ) -> Vec<Outputs<Id, Self::Msg>> {
        Vec::new()
    }
}

impl ClientActor{

    // a function for generating the next tx
    fn next_tx(tx : TxData) -> TxChunk {
        // could be "random", but, to keep things simple for the moment:
                    if tx[0]%2 == 0 {
                        tx[0] / 2
                    } else {
                        3*tx[0] + 1
                    }
    }
}

// the client's behaviour: on_start_vec, on_msg_vec
impl Vactor for ClientActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start_vec(
        &self,
        id: Id
    ) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        if cfg!(debug_assertions) {
            print!("Start client {}", id);
        }
        let key = self.key_seed;
        match ed25519_consensus::VerificationKey::try_from(key) {
            // MENDME: mover the key registration to Vactor trait (code copies) 
            Ok(vk) => {
                use pki::*;
                REGISTRY.register_key(id, vk, DUMMY_SIG);
            }
            _ => {
                panic!("bad key at client {:?}", self); 
            }
        }
            
        let client_state = Client(self.known_workers.clone(), key);
        let mut o = vec![];

        // send a different tx to every worker, to get started
        let mut x = 0;
        for k in &self.known_workers {
            x = x + 1;
            &self.send(*k, TxReq(vec![x], id), &mut o);
        }

        let res = (client_state, o);
        res
    }

    fn on_msg_vec(
        &self,
        id: Id,
        _state: &mut Cow<'_, Self::State>,
        _src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id, Self::Msg>> {
        match msg {
            TxAck(ref tx, ref worker) => {
                // wait some to keep output rate civilized
                use std::{thread, time};
                let hundred_millis = time::Duration::from_millis(100);
                thread::sleep(hundred_millis);

                // send the new transaction
                let new_tx = Self::next_tx(tx.to_vec());
                let mut o = vec![];
                self.send(*worker, TxReq(vec![new_tx], id), &mut o);
                o
            }
            _ => {
                println!(
                    "oops, message {:?} was sent to me little client {:?}",
                    msg, self
                );
                vec![]
            }
        }
    }
}

// the behaviour of workers, according to the spec
impl WorkerActor{
    fn process_tx_req(
        &self,
        src: Id,
        client: ClientId,
        tx: TxData,
        ack: <WorkerActor as Vactor>::Msg,
        state: &mut WorkerState,
        key_seed: [u8; 32],
    ) -> Vec<Outputs<Id, <WorkerActor as Vactor>::Msg>> {
        let mut o = vec![];
        if client != src {
            panic!("source of transaction request is not the client");
        } else {
            // push the tx to the worker's buffer
            let buffer_entry = (tx.clone(), client);
            let sequence_number = state.tx_buffer.len();
            state.tx_buffer.push(buffer_entry.clone());
            // the sequence number corresponds to the index
            assert!(state.tx_buffer[sequence_number] == buffer_entry);
            // ack the tx, optional, but nice to have
            assert!(client == src); // always true, just double checking
            self.send(client, ack, &mut o);

            // "broadcast" tx to mirror_workers : Vec<Id>
            self.send_(
                self.mirror_workers.clone(),
                TxToAll(tx.clone(), client, sequence_number, self.rnd),
                &mut o
            );


            // check if we can finish a batch
            if state.tx_buffer.len() >= BATCH_SIZE {
                // create and process batch hash
                let w_hash = WorkerHashData {
                    hash: hash_of(&state.tx_buffer),
                    rnd: state.rnd,
                    length: state.tx_buffer.len(),
                };
                let w_bytes: &[u8] = &bincode::serialize(&w_hash).unwrap();
                use ed25519_consensus::SigningKey;
                let key = SigningKey::from(key_seed);
                let sig: WorkerHashSignature = key.sign(w_bytes).to_bytes();

                // notify primary that a new batch hash is out
                // aka worker hash provision
                self.send(
                    state.primary,
                    WorkerHx(w_hash.clone(), sig),
                    &mut o
                );

                // broadcast the worker hash to
                // aka worker hash broadcast
                self.send_(
                    self.mirror_workers.clone(),
                    WHxToAll(w_hash, sig),
                    &mut o
                );
            }
            o
        }
    }

    // fn process_tx(
    //     &self
    //     //
    // ) -> Vec<Outputs<Id, <WorkerActor as Vactor>::Msg>> {
    //     vec![]
    // }

    // checking a worker hash and forwarding it 
    fn process_w_hx(
        &self, 
        src : WorkerId, 
        w_hash : &WorkerHashData, 
        sig: WorkerHashSignature,
        state: &mut WorkerState
    ) -> Vec<
            Outputs<
                    Id,
                <WorkerActor as Vactor>::Msg
                    >
            > {
        fn check_signature(
            src : WorkerId, 
            w_hash : &WorkerHashData, 
            sig: WorkerHashSignature
        ) -> bool {
            //fn verify(&self, &Signature, &[u8]) -> Result<(), Error>
            use ed25519_consensus::{VerificationKey,Signature};
            use pki::*;
            let key = VerificationKey::from(REGISTRY.lookup_vk(src).unwrap());
            let w_bytes = &bincode::serialize(&w_hash).unwrap();
            match key.verify(&Signature::from(sig), w_bytes){
                Ok(_) => {true},
                Err(_) => {
                    println!("got a bad signature from worker #{}", src); 
                    false
                }
            }
        }

        // we need to have the transactions ordered
        // the order is induced by the sequence number 
        fn sort_tx_vec_from<T:Clone, C:Clone, U :Ord+Clone>(
             vector : &mut Vec<(T,C,U, u64)>, 
            rnd : u64
        ) -> Vec<(T,C,U, u64)>{
            let i  = vector.iter().filter(|x| x.3  == rnd);
            // this should be just collecting the iterator into i
            let mut x = vec![];
            for k in i {
                let wow = &(*k);
                x.push(wow.clone());
            }
            // now x is the filtered vector
            x.sort_by(|x , y| x.2.cmp(&y.2));
            // and sorted
            x
        }

        let mut res = vec![];
        if check_signature(src, w_hash, sig){
            // TODO check round number 
            // (whether we already have a worker hash from the src ?) 
            let the_round = w_hash.rnd;
            let mut all_txs = state.tx_buffer_map[&src].clone();
            let relevant_txs = sort_tx_vec_from(
                &mut all_txs, 
                the_round
            );
            if relevant_txs.len() == w_hash.length {
                self.send(
                    state.primary, 
                    WHxOK(w_hash.clone(), sig),
                    &mut res
                )
            } else {
                // TODO set timer
            }
        } else {
            println!("Got bad worker hash");            
        }
        res
    }


}

impl Vactor for WorkerActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start_vec(
        &self, id: Id
    ) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        if cfg!(debug_assertions) {
            println!("Starting worker {}", id);
        }
        let map = c!{
            key =>vec![],
            for key in self.mirror_workers.clone()
        };
        let worker_state = WorkerState {
            tx_buffer: vec![], // empty transaction buffer
            tx_buffer_map: map.into_iter().collect(), 
            primary: self.primary,  // copy the primary
            rnd: GENESIS_ROUND, // start at genesis
            mirrors: self.mirror_workers.clone(), // copy mirror_workers
        };
        let state = Worker(
            worker_state,
            self.key_seed, // copy key
        );
        match ed25519_consensus::VerificationKey::try_from(self.key_seed) {
            Ok(vk) => {
                use pki::*;
                REGISTRY.register_key(id, vk, DUMMY_SIG);
            }
            _ => {
                panic!("bad key at worker {:?}", self); 
            }
        }
        (state,vec![])
    }

    // reacting to received messages
    fn on_msg_vec(
        &self,
        w_id: Id,
        state: &mut Cow<'_, Self::State>,
        src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id, Self::Msg>> {
        if cfg!(debug_assertions) {
            println!("Worker {} got a message {:?}", w_id, msg);
        }
        // check if state is proper
        let mut worker_state : &mut WorkerState;
        let key_seed : [u8; 32];
        if let Worker(ref mut s, k) = state.to_mut() {
            worker_state = s;
            key_seed = *k;
            // ok
        } else {
            // issue
            panic!("Worker state incorrect");
        }
        // choose the action to perform according to the message variant
        match msg {
            TxReq(tx, client) => {
                // we got a transaction request from a client

                // this is the expected ack
                let msg = TxAck(tx.clone(), w_id);
                // further processing
                self.process_tx_req(
                    src,
                    client,
                    tx,
                    msg,
                    &mut worker_state,
                    key_seed
                )
            }
            TxToAll(tx, client, seq_num, r) => {
                // we got a transaction copy (erasure code)
                // --
                // the info we want to store 
                let new_tx_info = (tx, client, seq_num, r);
                // updating the worker state
                worker_state.tx_buffer_map
                    .get_mut(&src).expect("because!") 
                    .push(new_tx_info); 
                // nothing else to do
                vec![]
            }
            WHxToAll(w_hash, sig) => {
            //   we got a worker hash from a mirror worker to process
                self.process_w_hx(src, &w_hash, sig, worker_state)
             }
            _ => {
                println!(
                    "oops, me little client {:?} received Message {:?}",
                    &self, msg
                );
                vec![]
            }
        }
    }
}

impl Vactor for PrimaryActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start_vec(&self, id: Id) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        println!("start primary {}", id);
        let key_seed = self.key_seed;
        match ed25519_consensus::VerificationKey::try_from(key_seed) {
            Ok(vk) => {
                use pki::*;
                REGISTRY.register_key(id, vk, DUMMY_SIG);
            }
            _ => {
                panic!("bad key at primary {:?}", self); 
            }
        }
        (Primary(PrimaryState {}, key_seed), vec![]) // default value for one ping pongk
    }

    fn on_msg_vec(
        &self,
        _id: Id,
        _state: &mut Cow<Self::State>,
        _src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id, Self::Msg>> {
        match msg {
            _ => {
                vec![]
                //o.send(src, SomeKindOfMessage(DummyMessageType{}));
            }
        }
    }
}

// the enumeration of all possible kinds of actor
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
enum ActorEnum {
    Client(ClientActor),
    Worker(WorkerActor),
    Primary(PrimaryActor),
}

// we collect all above kinds of Vactors into an enum
// and Vactor-behaviour of the enum obtained by
// delegating the function calls to the respective type
#[derive(Delegate, Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[delegate(Vactor)]
enum HNActor {
    ClientActor(ClientActor),
    WorkerActor(WorkerActor),
    PrimaryActor(PrimaryActor),
}

use HNActor::*;
impl Actor for HNActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        let (s, v) = self.on_start_vec(id);
        for x in v {
            match x {
                Outputs::Snd(i, m) => o.send(i, m),
                // _ => {
                //     panic!("not implemented in on_start");
                // }
            }
        }
        s
    }
    fn on_msg(
        &self,
        id: Id,
        state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg,
        o: &mut Out<Self>,
    ) {
        let v = self.on_msg_vec(id, state, src, msg);
        for x in v {
            match x {
                Outputs::Snd(i, m) => o.send(i, m),
                // _ => {
                //     panic!("not implemented in on_msg");
                // }
            }
        }
    }
}

// in rough analogy to stateright's `examples/paxos.rs`
// history will simply be state/action pairs
#[derive(Clone)]
struct NarwhalModelCfg {
    worker_index_count: usize,
    primary_count: usize,
    client_count: usize,
    network: Network<<HNActor as Actor>::Msg>,
}

// generates a key_seed,
// using ed25519_consensus::SigningKey rand::thread_rng
fn fresh_key_seed() -> [u8; 32] {
    use ed25519_consensus::SigningKey;
    use rand::thread_rng;
    let key = SigningKey::new(thread_rng());
    let key_seed = key.to_bytes();
    let key_again: SigningKey = SigningKey::from(key_seed);
    assert!(key.to_bytes() == key_again.to_bytes());
    key_seed
}

impl NarwhalModelCfg {
    // `into_model()` is meant for model checking (or exploration).
    // Ids of actors will actually be assigned implicitly.
    // The id of each actor is induced by the order in which
    // we add actors; the first actor to be added has index 0
    // (“wrapped” into Id, via `from`).

    // 1. workers: 0..wic*pc
    fn get_worker_idx(&self, index: usize, primary: usize) -> usize {
        assert!(index < self.worker_index_count); // 0<=index always true
        assert!(primary < self.primary_count); // 0<=primary always true
        index + primary * self.worker_index_count
    }
    // 2. primaries: wic*pc..(wic+1)*pc
    fn get_primary_idx(&self, primary: usize) -> usize {
        primary + self.primary_count * self.worker_index_count
    }
    // 3. clients: (wic+1)*pc..(wic+1)*pc+cc
    fn get_client_idx(&self, client: usize) -> usize {
        client + self.primary_count * (self.worker_index_count + 1)
    }

    fn calculate_known_workers(&self) -> Vec<Id> {
        c![Id::from(self.get_worker_idx(i,j)),
           for i in 0..self.worker_index_count,
           for j in 0..self.primary_count]
    }

    fn calculate_peer_validators_and_id(&self, primary: usize) -> (Vec<Id>, Id) {
        let range = 0..self.primary_count;
        (
            c![Id::from(self.get_primary_idx(i)), for i in range, if i != primary],
            self.get_primary_idx(primary).into(),
        )
    }
    fn calculate_mirror_workers_and_id(&self, index: usize, primary: usize) -> (Vec<Id>, Id) {
        (
            c![Id::from(self.get_worker_idx(index, j)),
           for j in 0..self.primary_count,
           if j != primary],
            self.get_worker_idx(index, primary).into(),
        )
    }

    fn record_msg_in<'a, 'b, 'c>(
        _cfg: &'a Self,
        history: &'b Vec<Envelope<<HNActor as Actor>::Msg>>,
        env: Envelope<&'c <HNActor as Actor>::Msg>,
    ) -> Option<Vec<Envelope<<HNActor as Actor>::Msg>>> {
        let mut h = history.clone();
        let e = env.to_cloned_msg();
        h.push(e);
        Some(h)
    }

    fn record_msg_out<'a, 'b, 'c>(
        _cfg: &'a Self,
        history: &'b Vec<Envelope<<HNActor as Actor>::Msg>>,
        env: Envelope<&'c <HNActor as Actor>::Msg>,
    ) -> Option<Vec<Envelope<<HNActor as Actor>::Msg>>> {
        let mut h = history.clone();
        let e = env.to_cloned_msg();
        h.push(e);
        Some(h)
    }

    // The actor ids in models of stateright are essentially hard-coded;
    // they are given by the position the `actors` field
    fn into_model(self) -> ActorModel<HNActor, Self, Vec<Envelope<<HNActor as Actor>::Msg>>> {
        ActorModel::new(
            self.clone(),
            vec![], // here will go histories, i.e., sequences of
        )
        // we **have**add actors in the following order
        // wic = worker_index_count
        // pc = primary_count
        // cc = client_count
        // 1. workers: 0..wic*pc
        // 2. primaries: wic*pc..(wic+1)*pc
        // 3. clients: (wic+1)*pc..(wic+1)*pc+cc
        .actors(c![WorkerActor(WorkerActor{
                index: i as u64,
                primary: Id::from(self.get_primary_idx(j)),
                mirror_workers: self.calculate_mirror_workers_and_id(i,j).0,
                my_expected_id: self.calculate_mirror_workers_and_id(i,j).1,
                key_seed: fresh_key_seed(),
                rnd: GENESIS_ROUND,
            }),
                       for i in 0..self.worker_index_count,
                       for j in 0..self.primary_count])
        .actors(c![PrimaryActor(PrimaryActor{
                peer_validators: self.calculate_peer_validators_and_id(p).0,
                my_expected_id: self.calculate_peer_validators_and_id(p).1,
                key_seed: fresh_key_seed(),
            }), for p in 0..self.primary_count])
        .actors(c![ClientActor(ClientActor{
                known_workers: self.calculate_known_workers(),
                my_expected_id: self.get_client_idx(c).into(),
                key_seed: fresh_key_seed(),
            }), for c in 0..self.client_count])
        .init_network(self.network)
        .property(Expectation::Eventually, "trivial progress", |_, state| {
            state.history.len() > 1
        })
        //  .property(Expectation::Always, "linearizable", |_, state| {
        //      state.history.serialized_history().is_some()
        //  })
        //  .property(Expectation::Sometimes, "value chosen", |_, state| {
        //      for env in state.network.iter_deliverable() {
        //          if let RegisterMsg::GetOk(_req_id, value) = env.msg {
        //              if *value != Value::default() { return true; }
        //          }
        //      }
        //      false
        //  })
        .record_msg_in(NarwhalModelCfg::record_msg_in)
        .record_msg_out(NarwhalModelCfg::record_msg_out)
    }
}

// we need an ActorModel now
// from https://docs.rs/stateright/latest/stateright/actor/struct.ActorModel.html
//
// pub struct ActorModel<A, C = (), H = ()> where
//     A: Actor, // ⇐ this will be A = HNActor
//     H: Clone + Debug + Hash,  {
//          pub actors: Vec<A>, // ⇐ that's our array of actors
//          pub cfg: C, //
//          pub init_history: H,
//          pub init_network: Network<A::Msg>, // ⇐ this will be any (non-lossy) nework
//          pub lossy_network: LossyNetwork,  // ⇐ this will be `LossyNetwork::No`
//          pub properties: Vec<Property<ActorModel<A, C, H>>>, // ⇐ this is exploratory mode
//          pub record_msg_in: fn(cfg: &C, history: &H, envelope: Envelope<&A::Msg>) -> Option<H>, //
//          pub record_msg_out: fn(cfg: &C, history: &H, envelope: Envelope<&A::Msg>) -> Option<H>,
//          pub within_boundary: fn(cfg: &C, state: &ActorModelState<A, H>) -> bool,
// }




#[derive(PartialEq)]
enum ThisEnum {
    Check,
    Spawn,
    Explore,
}
use ThisEnum::*;
// hardcoded choice, so far
//const SUP:ThisEnum = Check;
//const SUP:ThisEnum = Spawn;
const SUP: ThisEnum = Explore;

// this is the registry

const REGISTRY : pki::KeyTable =
// MENDME plz: make this proper with setters/getters/init
    pki::KeyTable{
        map : BTreeMap::new(),
    };
const DUMMY_SIG : [u8; 64] = [0; 64];
fn main() {
    // // this is an example on how to use REGISTRY
    // use ed25519_consensus::VerificationKey;
    // use pki::*;
    // match VerificationKey::try_from([0; 32]) {
    //     Ok(vk) => {
    //         // 
    //         let dumm_sig = [0; 64];// this would be a signature of the key
    //         REGISTRY.register_key(Id::from(0), vk, dumm_sig);
    //     }
    //     Err(_) => {
    //         // this is probably unreachable ❓ 
    //         println!("too bad"); 
    //     }
    // }
    match SUP {
        Spawn => {
            println!(" about to spawn HNarwhal");
            use std::net::{Ipv4Addr, SocketAddrV4};

            // the port is only required for spawning
            let worker_port = 3000; // ⇐ _NOT_ part of NarwhalModelCfg

            // generate all ids we need
            const WORKER_INDEX_COUNT: u16 = 10;
            const PRIMARY_COUNT: u16 = 10;
            const CLIENT_COUNT: u16 = 4;
            // a bunch of worker IDs
            let worker_ids = c![
                Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST,
                                           worker_port + WORKER_INDEX_COUNT*y + x)
                ),
                for x in 0..WORKER_INDEX_COUNT,
                for y in 0..PRIMARY_COUNT
            ];
            let primary_port = 4000; // hopefully big enough ...
            assert!(4000 > 3000 + (WORKER_INDEX_COUNT + 1) * PRIMARY_COUNT);

            // and their primaries
            let primary_ids = c![
                Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, primary_port + y)),
                for y in 0..PRIMARY_COUNT
            ];

            let client_port = 4200;
            assert!(4200 > 4000 + PRIMARY_COUNT);

            let client_ids = c![
                Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, client_port + y)),
                for y in 0..CLIENT_COUNT
            ];
            for x in &client_ids {
                println!("client  id: `{}` generated", x);
            }

            // now XYZ_ids for ZYZ ∈ {worker,primary,client} are generated

            // create actor structs:
            let clients = c![
                ClientActor{
                    known_workers:worker_ids.clone(),
                    my_expected_id:Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, client_port + y)),
                    key_seed: fresh_key_seed(),
                },
                for y in 0..CLIENT_COUNT
            ];
            // create primary structs:
            let primaries = c![
                PrimaryActor{peer_validators : primary_ids.clone(),
                             my_expected_id: Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, primary_port + y)),
                             key_seed: fresh_key_seed(),
                },
                for y in 0..PRIMARY_COUNT
            ];
            // create worker structs:
            let workers = c![
                WorkerActor{
                    index : x as u64,
                    primary : primary_ids[x as usize],
                    mirror_workers : c![
                        worker_ids[(WORKER_INDEX_COUNT*z + x) as usize],
                        for z in 0..PRIMARY_COUNT
                    ],
                    my_expected_id : Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST,
                                                                worker_port + WORKER_INDEX_COUNT*y + x)
                    ),
                    key_seed: fresh_key_seed(),
                    rnd: GENESIS_ROUND,
                },
                for x in 0..WORKER_INDEX_COUNT,
                for y in 0..PRIMARY_COUNT
            ];

            // let mut primary_actor_vec_dyn : Vec< Box< dyn Actor<Msg = MessageEnum, State = StateEnum>>>  = c![
            //     // (primary_ids[y as usize],
            //     primaries[y as usize].clone()
            //     //)
            //         ,
            //     for y in 0..PRIMARY_COUNT
            // ];

            let  primary_actor_vec = c![
                (primary_ids[y as usize], primaries[y as usize].clone()),
                for y in 0..PRIMARY_COUNT
            ];
            let  client_actor_vec = c![
                (client_ids[y as usize], clients[y as usize].clone()),
                for y in 0..CLIENT_COUNT
            ];
            let  worker_actor_vec = c![
                (worker_ids[(WORKER_INDEX_COUNT*y + x)as usize], workers[(WORKER_INDEX_COUNT*y + x)as usize].clone()),
                for x in 0..WORKER_INDEX_COUNT,
                for y in 0..PRIMARY_COUNT
            ];

            // the hacky version to spawn is by use of several threads
            // ---------
            // use std::thread;
            // print!("first spawn");
            // thread::spawn(|| {
            //     spawn(
            //         serde_json::to_vec,
            //         |bytes| serde_json::from_slice(bytes),
            //         client_actor_vec,
            //     )
            //     .unwrap();
            // });
            // print!("second spawn");
            // thread::spawn(|| {
            //     spawn(
            //         serde_json::to_vec,
            //         |bytes| serde_json::from_slice(bytes),
            //         primary_actor_vec,
            //     )
            //     .unwrap();
            // });
            // print!("third spawn is blocking");

            // spawn(
            //     serde_json::to_vec,
            //     |bytes| serde_json::from_slice(bytes),
            //     worker_actor_vec,
            // )
            // .unwrap();

            let mut all_vactor_vec: Vec<(Id, HNActor)> = Vec::new();
            for (i, a) in client_actor_vec {
                all_vactor_vec.push((i, HNActor::ClientActor(a)));
            }
            for (i, a) in primary_actor_vec {
                all_vactor_vec.push((i, HNActor::PrimaryActor(a)));
            }
            for (i, a) in worker_actor_vec {
                all_vactor_vec.push((i, HNActor::WorkerActor(a)));
            }

            spawn(
                serde_json::to_vec,
                |bytes| serde_json::from_slice(bytes),
                all_vactor_vec,
            )
                .unwrap();

            // "the
            use ed25519_consensus::{SigningKey, VerificationKey};
            use rand::thread_rng;

            let key = SigningKey::new(thread_rng());
            let key_seed = key.to_bytes();
            let key_again: SigningKey = SigningKey::from(key_seed);
            assert!(key.to_bytes() == key_again.to_bytes());
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
            assert!(VerificationKey::try_from(vk_bytes)
                    .and_then(|vk| vk.verify(&sig_bytes.into(), msg))
                    .is_ok());

            // -- end elliptic curves usage
        }
        Check => {
            let c_count = 3;
            let nw = Network::new_unordered_nonduplicating([]);
            println!("Model checking HNarwhal with {} clients.", c_count);
            NarwhalModelCfg {
                worker_index_count: 2,
                primary_count: 4,
                client_count: c_count,
                network: nw,
            }
            .into_model()
                .checker()
                .threads(num_cpus::get())
                .spawn_dfs()
                .report(&mut std::io::stdout());
        }
        Explore => {
            let c_count = 3;
            let address = String::from("localhost:3000");
            let nw = Network::new_unordered_nonduplicating([]);
            println!(
                "Exploring state space for Heterogeneous Narwhal with {} clients on {}.",
                c_count, address
            );
            NarwhalModelCfg {
                worker_index_count: 2,
                primary_count: 4,
                client_count: c_count,
                network: nw,
            }
            .into_model()
                .checker()
                .threads(num_cpus::get())
                .serve(address);
        }
        // _ => {
        //     panic!("noooo, SUP?!")
        // }
    }
}
