// -------------------------------------------------------
// The Heterogeneous Narwhal implementation in stateright
// -------------------------------------------------------
//
// This code is geared toward clarity and correctness,
// w.r.t. tech report
// https://github.com/anoma/ ..
// .. research/tree/master/distributed-systems/heterogeneous-narwhal

use serde::{Deserialize, Serialize};
use std::fmt::Debug;

// For hashing,
// based on doc.rust-lang.org/std/hash/index.html,
// we use the following 8 (eight) lines of code:
use std::collections::hash_map::DefaultHasher;
use std::collections::BTreeMap;
use std::collections::{HashMap,VecDeque};
// fn hash_to_btree<K:std::cmp::Ord,V>(
//     hash: HashMap<K, V>
// ) -> BTreeMap<K, V> {
//     // make hashmap iterator, then collect
//     hash.into_iter().collect()
// }
fn iter_to_vec<T: Clone>(i: &mut dyn Iterator<Item = T>) -> Vec<T> {
    i.collect()
}
fn iter_to_vec_<T: Clone>(iter: &mut dyn Iterator<Item = T>) -> Vec<T> {
    let mut x = vec![];
    for el in iter {
        x.push(el.clone());
    }
    x
}

use cute::c; // for “pythonic” vec comprehension
             // simplest example
             //const SQUARES = c![x*x, for x in 0..10];
             //const EVEN_SQUARES = c![x*x, for x in 0..10, if x % 2 == 0];

// https://docs.rs/mapcomp/latest/mapcomp/macro.btreemapc.html
// use mapcomp::btreemapc; // for “pythonic” btree comprehension
use std::hash::{Hash, Hasher};


fn hash_of<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    let mut s_ = DefaultHasher::new();
    t.hash(&mut s);
    let first_hash = s.finish();
    t.hash(&mut s_);
    let second_hash = s_.finish();
    assert!(first_hash == second_hash);
    first_hash
}

// the data type of learner graphs
mod learner_graph {
    // the learner graph trait uses
    use std::collections::{HashMap, HashSet};
    use std::iter::Iterator;

    // learner graph trait
    // ... compatible with github.com/isheff/het_paxos_ref
    pub trait LearnerGraph {
        type Learner;
        type Validator;

        fn get_learners(&self) -> dyn Iterator<Item = Self::Learner>;

        fn get_quorums(&self) -> HashMap<Self::Learner, HashSet<Self::Validator>>;

        fn are_entangled(&self, learner_a: Self::Learner, learner_b: Self::Learner) -> bool;
    }
}


// this module is for the purpose of “faking” a PKI-infrastructure
mod pki {
    // elliptic curve signatures imports (kudos to Daniel)
    use ed25519_consensus::*;
    use stateright::actor::Id;
    use std::collections::BTreeMap;
    // use std::convert::TryFrom;

    // The Registry is responsible for
    // - regsitering keys via `register_key`
    // - lookup of verification keys via `lookup_vk`
    pub trait Registry {
        // registering a verification key for the id
        fn register_key(&mut self, _: Id, _: VerificationKey, _: [u8; 64]) -> bool;

        // looking up the key for the id
        fn lookup_vk(&self, _: Id) -> Option<VerificationKey>;
    }

    pub struct KeyTable {
        pub map: BTreeMap<Id, VerificationKey>,
    }

    impl Registry for KeyTable {
        fn register_key(&mut self, id: Id, vk: VerificationKey, _sig: [u8; 64]) -> bool {
            // MENDME, add some form of authentication
            self.map.insert(id, vk) != None
        }

        fn lookup_vk(&self, id: Id) -> Option<VerificationKey> {
            if let Some(vk) = self.map.get(&id) {
                Some(*vk)
            } else {
                None
            }
        }
    }

    // fn private_test_ed25519_consensus() {
    //     // ------- ed25519-consensus signatures example usage
    //     use rand::thread_rng;
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
    // the take (formerly, the round of the primary)
    take: u32,
    // the number of txs of this worker hash
    length: usize,
    // the hash
    hash: u64,
    // the collector
    // collector: WorkerId
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

// header, the data structure for primaries
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
struct HeaderData {
    // the creator of the header
    creator: ValidatorId,
    // the worker hashes (produced by the creator's workers)
    worker_hashes: Vec<WorkerHashData>,
}

// the enumeration of all possible kinds of messages
//
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
enum MessageEnum {
    // transaction requests, sent by the client/user
    TxReq(TxData, ClientId),
    // acknowledgments of transactions by the worker
    TxAck(TxData, WorkerId),
    // broadcasting a tx (or its erasure code) to mirror workers
    TxToAll(TxData, ClientId, usize, u32),
    // Worker Hash (to the primary)
    WorkerHx(
        WorkerHashData,
        #[serde(with = "BigArray")] WorkerHashSignature,
    ),
    // Worker Hash Broadcast (to mirror workers)
    WHxToAll(
        WorkerHashData,
        #[serde(with = "BigArray")] WorkerHashSignature,
    ),
    // Worker Hash forwarding (to primary, received from mirror workers)
    WHxFwd(
        WorkerHashData,
        #[serde(with = "BigArray")] WorkerHashSignature,
    ),
}

use crate::MessageEnum::*;

const GENESIS_ROUND: u64 = 0;
const FIRST_TAKE: u32 = 0;
const BATCH_SIZE: usize = 3;

// the state type of workers
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct WorkerState {
    // the buffer for received transactions
    tx_buffer: Vec<(TxData, ClientId)>,
    // storing the pending worker hashes
    pending_hxs : VecDeque<(WorkerId, WorkerHashData, WorkerHashSignature)>,
    // hashmap to stores of transaction copies
    tx_buffer_map: BTreeMap<WorkerId, Vec<(TxData, ClientId, usize, u32)>>,
    // a copy of the primary information ()
    primary: ValidatorId,
    // a copy of the mirror worker information
    mirrors: Vec<WorkerId>,
    //  ̶r̶o̶u̶n̶d̶ ̶n̶u̶m̶b̶e̶r̶ => take
    take: u32,
    // the id
    the_id: WorkerId,
}

// the state type of primaries
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct PrimaryState {
    // map_of_worker_hashes loal or foreign (right ?)
    map_of_worker_hashes: BTreeMap<WorkerId, Vec<WorkerHashData>>,
    // the id
    the_id: ValidatorId,
}

// the state type of clients
// it is the number of requests
type ClientState = Vec<WorkerId>;

// states can be either of a worker or a primary
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum StateEnum {
    // every actor has a signing key (seed)
    Worker(WorkerState, [u8; 32], Id),
    Primary(PrimaryState, [u8; 32], Id),
    Client(ClientState, [u8; 32], Id),
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
    // take number
    take: u32,
}

// PrimaryActor holds the static information about primaries
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct PrimaryActor {
    // key (as seed) -- NB: this needs to be fixed before `on_start`
    key_seed: [u8; 32],
    // the ids of all (known) peer validators
    peer_validators: Vec<ValidatorId>,
    // my_expected_id (for debugging)
    my_expected_id: Id,
    //
    local_workers: Vec<WorkerId>,
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
    Timer(core::ops::Range<core::time::Duration>), // timer in seconds
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

    fn get_vk_bytes(&self) -> [u8; 32];

    fn send(&self, id: Id, m: Self::Msg, o: &mut Vec<Outputs<Id, Self::Msg>>) {
        o.push(Outputs::Snd(id, m));
    }
    fn send_(&self, ids: Vec<Id>, m: Self::Msg, o: &mut Vec<Outputs<Id, Self::Msg>>) {
        for i in ids {
            self.send(i, m.clone(), o);
        }
    }

    fn check_back_later(&self, o: &mut Vec<Outputs<Id, Self::Msg>>){
        use core::time::Duration;
        let duration = Duration::from_secs(1)..Duration::from_secs(2);
        o.push(Outputs::Timer(duration));
    }

    fn on_start_vec(&self, id: Id) -> (Self::State, Vec<Outputs<Id, Self::Msg>>);

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
        // by default, “ignore”
        Vec::new()
    }
}

impl ClientActor {
    // a function for generating the next tx
    fn next_tx(tx: TxData) -> TxChunk {
        // could be "random", but, to keep things simple for the moment:
        if tx[0] % 2 == 0 {
            tx[0] / 2
        } else {
            3 * tx[0] + 1
        }
    }
}

// the client's behaviour: on_start_vec, on_msg_vec
impl Vactor for ClientActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn get_vk_bytes(&self) -> [u8; 32] {
        use ed25519_consensus::*;
        VerificationKey::from(&SigningKey::from(self.key_seed)).into()
    }

    fn on_start_vec(&self, id: Id) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        if cfg!(debug_assertions) {
            print!("Start client {}", id);
        }
        let client_state = Client(self.known_workers.clone(), self.key_seed, id);
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


fn is_valid_signature(
    // src is the signing id
    src: WorkerId,
    w_hash: &WorkerHashData,
    sig: WorkerHashSignature,
) -> bool {
    //fn verify(&self, &Signature, &[u8]) -> Result<(), Error>
    use ed25519_consensus::{Signature, VerificationKey};
    use pki::*;
    let mut the_reg = REG_MUTEX.lock().unwrap();
    let key = VerificationKey::from(the_reg.lookup_vk(src).unwrap());
    let w_bytes = &bincode::serialize(&w_hash).unwrap();
    match key.verify(&Signature::from(sig), w_bytes) {
        Ok(_) => true,
        Err(_) => {
            println!("got a bad signature from worker #{}", src);
            false
        }
    }
}// end `fn check_signature`

// we need to order transaction vectors to produce worker hashes
// the order is induced by the sequence number 
// after filtering the take `tk`
// the code is pretty generic
fn filter_n_sort<T: Clone, C: Clone, U: Ord + Clone>(
    vector: &mut Vec<(T, C, U, u32)>,
    tk: u32,
) -> Vec<(T, C, U, u32)> {
    let iter = vector.iter().filter(|x| x.3 == tk);
    // the next two lines _should_ be just `let mut x = i.collect();`
    let mut x = vec![];
    for el in iter {
        x.push(el.clone());
    }
    // x is the vector of transaction data of the same “take”
    x.sort_by(|a, b| a.2.cmp(&b.2));
    // and sorted, ascending in the sequence number (within the take)
    // guess sequence number should be frame number ;-)
    x
} // end `fn filter_n_sort`




// the behaviour of workers, according to the spec
impl WorkerActor {
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
            panic!("sender of transaction request is not tx's client");
        } else {
            // push the tx to the worker's buffer
            let tx_entry = (tx.clone(), client);
            let sequence_number = state.tx_buffer.len();
            state.tx_buffer.push(tx_entry.clone());
            // sequence number should correspond to the tx's index in the tx_buffer
            assert!(state.tx_buffer[sequence_number] == tx_entry);

            // planning to send the (nice to have) ack
            self.send(client, ack, &mut o);
            assert!(client == src); // always true, just double checking

            // "broadcast" tx to mirror_workers : Vec<Id>
            self.send_(
                state.mirrors.clone(),
                TxToAll(tx, client, sequence_number, state.take),
                &mut o,
            );
            //
            state.take = state.take + 1;
            if cfg!(debug_assertions) {
                println!("Worker {:?} at take {}", self, state.take); 
            }

            // check if we can finish a batch
            if state.tx_buffer.len() >= BATCH_SIZE {
                
                // create and process batch hash
                let w_hash = WorkerHashData {
                    hash: hash_of(&state.tx_buffer),
                    take: state.take,
                    length: state.tx_buffer.len(),
                };
                let w_bytes: &[u8] = &bincode::serialize(&w_hash).unwrap();
                use ed25519_consensus::SigningKey;
                let key = SigningKey::from(key_seed);
                let sig: WorkerHashSignature = key.sign(w_bytes).to_bytes();

                // notify primary that a new batch hash is out
                // aka worker hash provision
                self.send(state.primary, WorkerHx(w_hash.clone(), sig), &mut o);

                // broadcast the worker hash to
                // aka worker hash broadcast
                if cfg!(debug_assertions) {
                    println!("Worker {:?} broadcasting {:?}", self, w_hash);
                }
                self.send_(state.mirrors.clone(), WHxToAll(w_hash, sig), &mut o);
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

    fn process_checked_w_hx(
        &self,
        src: WorkerId,
        w_hash: &WorkerHashData,
        sig: WorkerHashSignature,
        state: &mut WorkerState,
    ) -> Vec<Outputs<Id, <WorkerActor as Vactor>::Msg>> {
        let mut res = vec![];
        let hash_take = w_hash.take;
        let mut all_src_txs = state.tx_buffer_map[&src].clone();
        let relevant_txs = filter_n_sort(&mut all_src_txs, hash_take);
        if relevant_txs.len() == w_hash.length {
            if cfg!(debug_assertions) {
                println!(
                    "uploading worker hash {:?} at primary {:?}",
                    w_hash,
                    state.primary
                );
            }
            self.send(state.primary, WHxFwd(w_hash.clone(), sig), &mut res);
        } else {
            // we have some pending worker hash
            let pending = (src, w_hash.clone(), sig);
            state.pending_hxs.push_back(pending);
            self.check_back_later(&mut res);
        }
        res
    }

    // checking a worker hash and processing it if ok
    fn process_w_hx(
        &self,
        src: WorkerId,
        w_hash: &WorkerHashData,
        sig: WorkerHashSignature,
        state: &mut WorkerState,
    ) -> Vec<Outputs<Id, <WorkerActor as Vactor>::Msg>> {
        let mut res = vec![];
        if is_valid_signature(src, w_hash, sig) {
            if cfg!(debug_assertions) {
                println!("Worker {:?} got valid worker hash {:?}", self, w_hash );
            }
            // NB:
            // each worker has an independent counter of “takes/chunks”
            res = self.process_checked_w_hx(src, w_hash, sig, state)                     } else {
            println!("Got bad worker hash");
        }
        res
    }

    fn on_timeout_vec(
        &self,
        _id: Id,
        state: &mut Cow<'_, <WorkerActor as Vactor>::State>,
    ) -> Vec<
            Outputs<Id, <WorkerActor as Vactor>::Msg>
            > {
        // specifically check pending_hxs, fifo style, one at a time
        if let StateEnum::Worker(ref mut state, key, id) = state.to_mut() {
            let mut res = vec![];
            if state.pending_hxs.is_empty(){
                println!("got a spurious timer");
            } else {
                let (src, w_hash, sig) = state.pending_hxs.pop_front().unwrap();
                res = self.process_checked_w_hx(src, &w_hash, sig, state);
            }
            res
        } else {
            vec![]
        }

    }
}

impl Vactor for WorkerActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn get_vk_bytes(&self) -> [u8; 32] {
        use ed25519_consensus::*;
        VerificationKey::from(&SigningKey::from(self.key_seed)).into()
    }

    fn on_start_vec(&self, id: Id) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        if cfg!(debug_assertions) {
            println!("Starting worker {}", id);
        }
        let map = c! {
            key =>vec![],
            for key in self.mirror_workers.clone()
        };
        assert!(id == self.my_expected_id);
        let worker_state = WorkerState {
            tx_buffer: vec![], // empty transaction buffer
            tx_buffer_map: map.into_iter().collect(),
            pending_hxs: VecDeque::new(),
            primary: self.primary,                // copy the primary
            take: FIRST_TAKE,                     // start at 0
            mirrors: self.mirror_workers.clone(), // copy mirror_workers
            the_id: id,                           // copy id
        };
        let state = Worker(
            worker_state,
            self.key_seed, // copy key
            id,            // copy id
        );
        (state, vec![])
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
        let mut worker_state: &mut WorkerState;
        let key_seed: [u8; 32];
        if let Worker(ref mut s, k, _i) = state.to_mut() {
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
                self.process_tx_req(src, client, tx, msg, &mut worker_state, key_seed)
            }
            TxToAll(tx, client, seq_num, r) => {
                // we got a transaction copy (erasure code)
                // --
                // the info we want to store
                let new_tx_info = (tx, client, seq_num, r);
                // updating the worker state
                worker_state
                    .tx_buffer_map
                    .get_mut(&src)
                    .expect("because!")
                    .push(new_tx_info);
                // nothing else to do
                vec![]
            }
            WHxToAll(w_hash, sig) => {
                //   we got a worker hash from a mirror worker to process
                if cfg!(debug_assertions) {
                    // FIXME: worker hashes do not arrive !! BUG ALERT
                    // probably hiccup in the setup of (worker-)ids etc.
                    println!("Worker {} got a worker hash {:?}", w_id, w_hash);
                }
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

    fn get_vk_bytes(&self) -> [u8; 32] {
        use ed25519_consensus::*;
        VerificationKey::from(&SigningKey::from(self.key_seed)).into()
    }
    // cf. `on_start` of Actor
    fn on_start_vec(&self, id: Id) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        println!("start primary {}", id);
        let key_seed = self.key_seed;
        let map: HashMap<WorkerId, Vec<WorkerHashData>> = c! {
            key => vec![],
            for key in self.local_workers.clone()
        };
        assert!(id == self.my_expected_id);
        (
            Primary(
                PrimaryState {
                    map_of_worker_hashes: BTreeMap::new(),
                    the_id: id,
                },
                key_seed,
                id,
            ),
            vec![],
        ) // default value for one ping pongk
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

// ActorEnum wraps up all actor structs into an enum
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

    fn on_start(
        &self,
        id: Id,
        o: &mut Out<Self>
    ) -> Self::State {
        let vk_bytes = self.get_vk_bytes();
        match ed25519_consensus::VerificationKey::try_from(vk_bytes) {
            Ok(vk) => {
                use pki::*;
                let mut the_reg = REG_MUTEX.lock().unwrap();
                the_reg.register_key(id, vk, DUMMY_SIG);
            }
            _ => {
                panic!("bad key at `HNactor` {:?}", self);
            }
        }

        let (state, out_vec) = self.on_start_vec(id);
        for x in out_vec {
            match x {
                Outputs::Snd(i, m) => o.send(i, m),
                Outputs::Timer(d) => o.set_timer(d),
                // _ => {
                //     panic!("not implemented in on_start");
                // }
            }
        }
        state
    }

    fn on_msg(
        &self,
        id: Id,
        state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg,
        o: &mut Out<Self>,
    ) {
        let out_vec = self.on_msg_vec(id, state, src, msg);
        // MENDME code copy (see )
        for x in out_vec {
            match x {
                Outputs::Snd(i, m) => o.send(i, m),
                Outputs::Timer(d) => o.set_timer(d),
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
    fn calculate_local_workers(&self, primary: usize) -> Vec<Id> {
        c![self.get_worker_idx(index, primary).into(),
           for index in 0..self.worker_index_count
        ]
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
                take: FIRST_TAKE,
            }),
                       for i in 0..self.worker_index_count,
                       for j in 0..self.primary_count])
        .actors(c![PrimaryActor(PrimaryActor{
                peer_validators: self.calculate_peer_validators_and_id(p).0,
                my_expected_id: self.calculate_peer_validators_and_id(p).1,
                key_seed: fresh_key_seed(),
                local_workers:self.calculate_local_workers(p),
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

#[macro_use]
extern crate lazy_static;


lazy_static! {
    static ref ALL_ACTORS : Vec<ActorEnum> = {
        let mut v = vec![];
        // CONTINUE HERE
        // add all actors, used “uniformly” for
        // all modes of SUP
        v
    };
}





// right now, the registry is a global variable 
// ... wrapped into a mutex 
// usages should start `REG_MUTEX.lock()` followed by unwrap
// NTH: make this _immutable_ lazy static
use std::sync::Mutex;
lazy_static! {
    static ref REG_MUTEX:Mutex<pki::KeyTable> = 
    Mutex::new({
        let mut x = pki::KeyTable {
            map: BTreeMap::new(),
        };
        x 
    });
}




const DUMMY_SIG: [u8; 64] = [0; 64];
fn main() {
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
                             local_workers:
                             // a bunch of worker IDs (code copy!)
                             c![
                                 Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST,
                                                            worker_port + WORKER_INDEX_COUNT*y + x)
                                 ),
                                 for x in 0..WORKER_INDEX_COUNT]
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
                    take: FIRST_TAKE,
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

            let primary_actor_vec = c![
                (primary_ids[y as usize], primaries[y as usize].clone()),
                for y in 0..PRIMARY_COUNT
            ];
            let client_actor_vec = c![
                (client_ids[y as usize], clients[y as usize].clone()),
                for y in 0..CLIENT_COUNT
            ];
            let worker_actor_vec = c![
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
        } // _ => {
          //     panic!("noooo, SUP?!")
          // }
    }
}
