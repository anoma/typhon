// -------------------------------------------------------
// The Heterogeneous Narwhal implementation in stateright
// -------------------------------------------------------
//
// This code aims for clarity and correctness;
// it supplements the tech report https://github.com/anoma/…
// …research/tree/master/distributed-systems/heterogeneous-narwhal

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Debug;

use cute::c; // for “pythonic” vec comprehension
             // simplest examples
             // const SQUARES = c![x*x, for x in 0..10];
             // const EVEN_SQUARES = c![x*x, for x in 0..10, if x % 2 == 0];

// ----------------------------------------------------------------------
// Computing Hashes
// ----------------------------------------------------------------------
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
// Hashes are computed
// as in doc.rust-lang.org/std/hash/index.html,
fn hash_of<T: Hash>(t: &T) -> Digest {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    let the_hash = s.finish();

    if cfg!(debug_assertions) {
        // checking that the new hasher is "the same"
        let mut s_prime = DefaultHasher::new();
        t.hash(&mut s_prime);
        let second_hash = s_prime.finish();
        assert!(the_hash == second_hash);
    }
    the_hash // return
}

// ----------------------------------------------------------------------
// basic data structures
// ----------------------------------------------------------------------

// Digest is one of the aliases for the type of hashes
type Digest = u64;
// key-seed (bytes) (as in ed25519_consensus)
type KeySeed = [u8; 32];
// verification key / “public key” (based on ed25519_consensus)
type VKBytes = [u8; 32];
// signature (as in ed25519_consensus)
type Sig = [u8; 64];
// as signatures are [u8; 64], we serialize using BigArray
use serde_big_array::BigArray;

// signing byte slices with ed25519_consensus
fn sign_bytes(k: KeySeed, bytes: &[u8]) -> Sig {
    let key = ed25519_consensus::SigningKey::from(k);
    key.sign(bytes).to_bytes()
}

// signing serializable data via ed25519_consensus
fn sign_serializable<T: ?Sized>(k: KeySeed, x: &T) -> Sig
where
    T: serde::Serialize + Debug,
{
    let bytes = &bincode::serialize(x);
    let bytes_slice: &[u8] = match bytes {
        Ok(bytes) => bytes,
        Err(e) => {
            if cfg!(debug_assertions) {
                panic!("wow, serializing {:?} failed with error {}", x, e);
            } else {
                eprintln!("serializaion error {} for {:?}", e, x);
                b"anoma"
            }
        }
    };
    sign_bytes(k, bytes_slice)
}


// a module for associating state-right ids with other types of ids, such as
// - ip-addresses
// - anoma's external identities
mod id_mapping {
    // elliptic curve signatures imports (kudos to Daniel)
    use ed25519_consensus::*;
    use stateright::actor::Id;
    use std::collections::BTreeMap;

    // The Registry has the following functionality:
    // - registering verification keys via `register_key`
    // - lookup of verification keys via `lookup_vk`
    pub trait Registry {
        // registering a verification key for the id
        fn register_key(&mut self, _: Id, _: VerificationKey, _: Signature) -> bool;

        // looking up the key for the id
        fn lookup_vk(&self, _: Id) -> Option<VerificationKey>;
    }

    // map of "type" id => verification key
    pub struct KeyTable {
        pub map: BTreeMap<Id, VerificationKey>,
    }

    // implementing the registry based on a BTreeMap
    impl Registry for KeyTable {
        // insert key and report success as true
        fn register_key(&mut self, id: Id, vk: VerificationKey, _sig: Signature) -> bool {
            // MENDME, add some form of authentication
            self.map.insert(id, vk).is_some()
        }

        fn lookup_vk(&self, id: Id) -> Option<VerificationKey> {
            self.map.get(&id).copied()
        }
    }

    // // ------- ed25519-consensus signatures example usage
    // fn private_test_ed25519_consensus() {
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
    //         let sig_bytes: Signature;
    //         sig_bytes = sig.into();
    //         let vk_bytes: VKBytes;
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

// REG_MUTEX is a “global variable” for id managment,
// more precisly a static mutex holding the KeyTable.
// Unsing the “REGistry” should start with `REG_MUTEX.lock()`
// NTH: make this _immutable_
#[macro_use]
extern crate lazy_static;
use std::sync::Mutex;
lazy_static! {
    static ref REG_MUTEX: Mutex<id_mapping::KeyTable> = Mutex::new({
        id_mapping::KeyTable {
            map: BTreeMap::new(),
        }
    });
}

// ----------------------------------------------------------------------
// TODO: implement additional behavior for receiving ̈"pending" messages,
// ie, when receiving a message, we discern two cases:
// 1. the message is not being waited for;
// 2. it is "pending" and needs additional action to be taken.
// This can be done by having a general post-processing for messages,
// taking care of the non-trivial situations.
// In particular, this means, that the code can be better organized,
// in that we can read out the "happy" path from the specs in the code.
// concretely, each case for `on_msg_vec`, splits into
// 1. process message
// 2. post-process message (“wake up” the waiting process)
// for practical purposes,
// one might have dummy post-processing for starters
// ----------------------------------------------------------------------

// ----------------------------------------------------------------------
// TODO: add weak-links, (also on the level of specs)
// ----------------------------------------------------------------------

// --------------------------------------------------------------
// the actor model starts here
// --------------------------------------------------------------
// the actor model describes behaviour for three kinds of actors
// - clients, requesting transactions to be ordered
// - workers, receiving and processing transactions
// - primaries, building the actual mem-dag (with workers helping)
// --------------------------------------------------------------

// --------------------------------------------------------------
// how to cope with waiting for expected messages
// --------------------------------------------------------------
// sometimes, there we must wait for messages to arrive
// for each message that we are waiting for
// 1. we know the id from which it will come
// 2. the set of all other messages that are missing,
//    before we can proceed
// 3. the “exact” type of the message we can expect to receive,
//    called _message fingerprint_ for want of a better name
// 4. [conditions that make us stop waiting] 
// Thus, local states will have
// a) a map from (id, fingerprint)-pairs to (fingerprint-set, listener)-pairs
// b) calling the listener happens when the fingerprint-set becomes empty


// all about actors from stateright
use stateright::actor::*;
use stateright::*;
// stateright uses clone-on-write for state-changes
// -> doc.rust-lang.org/std/borrow/enum.Cow.html
use std::borrow::Cow;

// a blob of data, part of an (encrypted) transaction
type TxBlob = u64;
// a transaction is just an arbitrary "array" of blobs
type TxData = Vec<TxBlob>;
// each worker assigns a sequence number to transactions
type SeqNum = usize;
// batches of transactions are numbered as well, dubbed _take_
type Take = u32;
const FIRST_TAKE: Take = 0;

// availability certificate
type AC = (); // TO BE REFINED/DEFINED

// hashes of signed quorums
type SQHash = (); // TO BE REFINED

// worker hash data type `WorkerHash`
// (see https://crates.io/crates/bincode for serialization matters)
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
struct WorkerHash {
    // the hash (of a batch of transactions)
    hash: u64,
    // the number of txs in (the batch of) this worker hash
    length: usize,
    // the take (equal to the round number in Narwhal&Tusk)
    take: Take,
    // the id of the worker collecting the transactions
    collector: WorkerId,
}
// the (minimum) length of batches used in worker hashes
const BATCH_SIZE: usize = 3;

// the type of worker hash signatures
type WorkerHashSignature = Sig;

// the type of header signatures `HeaderSignature`
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct HeaderSignature {
    // the signing validator
    val: ValidatorId,
    // the signature
    #[serde(with = "BigArray")]
    sig: Sig,
}

// the type of signed quorum hashes (and any other hash)
type SignedQuorumHash = u64;

// the IDs of validators is a stateright Id
type ValidatorId = Id;

// the IDs of workers is a stateright Id
type WorkerId = Id;

// the IDs of workers
type ClientId = Id;

// the indices of workers (globally fixed, for all validators)
type WorkerIndex = u64;

// data type of headers (to be signed by primaries)
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
struct HeaderData {
    // the “creator” of the header
    creator: ValidatorId,
    // the worker hashes (produced by the creator's workers)
    worker_hashes: Vec<WorkerHash>,
    // the validity certificate
    certificate: Option<AC>,
    // the signed quorum hashes
    hashes: Option<Vec<SignedQuorumHash>>,
}

// the enumeration of all possible kinds of messages
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
enum MessageEnum {
    // --- transaction level --
    // transaction requests, sent by the client/user
    TxReq(TxData, ClientId),
    // acknowledgments of transactions (by workers)
    TxAck(TxData, WorkerId),
    // broadcasting a tx (or its erasure code) to mirror workers
    TxToAll(TxData, ClientId, SeqNum, Take),

    // --- worker hash level --
    // Worker Hash "upload"/provision (worker -> primary)
    WorkerHx(WorkerHash, #[serde(with = "BigArray")] WorkerHashSignature),
    // Worker Hash Broadcast (worker => worker)
    WHxToAll(WorkerHash, #[serde(with = "BigArray")] WorkerHashSignature),
    // Worker Hash forwarding (worker -> primary)
    WHxFwd(WorkerHash, #[serde(with = "BigArray")] WorkerHashSignature),

    // --- header level --
    // the request for header signature (primary => primary)
    NextHeader(
        // round Number
        Round,
        // list of collector-take pairs, identifying the worker hashes
        Vec<(WorkerId, Take)>,
        // availability certificate
        Option<AC>,
        // hashes of signed quorums
        Option<Vec<SQHash>>,
    ),

    // the header signature (primary -> primary)
    HeaderSig(
        // the creating primary
        ValidatorId,
        // the round number of the header to be
        Round,
        // the signature
        HeaderSignature,
    ),
}

use crate::MessageEnum::*;

// the round of a validator (e.g., u64)
type Round = u64;
// the first round, aka genesis
const GENESIS_ROUND: Round = 0;

// ----------------------------------------------------------------------
// state structs, holding the state of each and every actor
// ----------------------------------------------------------------------

// the state type of workers
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct WorkerState {
    // the buffer for received transactions
    tx_buffer: Vec<(TxData, ClientId)>,
    // storing the pending worker hashes
    pending_hxs: VecDeque<(WorkerId, WorkerHash, WorkerHashSignature)>,
    // hashmap to stores of transaction copies
    tx_buffer_map: BTreeMap<WorkerId, Vec<(TxData, ClientId, SeqNum, Take)>>,
    // the primary information
    primary: ValidatorId,
    // the mirror worker information
    mirrors: Vec<WorkerId>,
    //  take (corresponds to the round number in Narwhal&Tusk)
    take: Take,
    // the id of the worker
    the_id: WorkerId,
}

// the state type of primaries
#[derive(Clone, Debug, Eq, PartialEq, Hash)]

struct PrimaryState {
    // map_of_worker_hashes, foreign / forwarded
    map_of_worker_hashes: BTreeMap<WorkerId, BTreeMap<Take, WorkerHash>>,
    // local worker hashes
    worker_hash_set: BTreeSet<(WorkerId, WorkerHash)>,
    // the id
    the_id: ValidatorId,
    // peer validators
    validators: Vec<ValidatorId>,
    // round
    rnd: Round,
    // the pending signing requests
    #[allow(clippy::type_complexity)]
    pending_requests: BTreeMap<ValidatorId, Option<(Round, Vec<(WorkerId, Take)>)>>,
    // trigger map, from worker,take pairs to the pending validator
    expected_takes: BTreeMap<WorkerId, BTreeMap<Take, ValidatorId>>,
}

// the state type of clients
// each client knows a list of workers that can serve their requests
type ClientState = Vec<WorkerId>;

// the enumeration of state types, for workers, primaries, and clients
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum StateEnum {
    // every actor has a signing key (seed)
    Worker(WorkerState, KeySeed, Id),
    Primary(PrimaryState, KeySeed, Id),
    Client(ClientState, KeySeed, Id),
}

// ----------------------------------------------------------------------
// -- information about initial states
// ----------------------------------------------------------------------

// WorkerActor holds the static information about actors
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct Worker {
    // key (as seed)
    key_seed: KeySeed,
    // the index of a worker
    index: WorkerIndex,
    // the primary
    primary: ValidatorId,
    // the ids of workers of the same index, aka mirro workers
    mirror_workers: Vec<Id>,
    // my_expected_id is for debugging
    my_expected_id: Id,
    // take number
    take: Take,
}

// PrimaryActor holds the static information about primaries
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct Primary {
    // key (as seed) -- NB: this needs to be fixed before `on_start`
    key_seed: KeySeed,
    // the ids of all (known) peer validators
    peer_validators: Vec<ValidatorId>,
    // my_expected_id (for debugging)
    my_expected_id: Id,
    //
    local_workers: Vec<WorkerId>,
}

// ClientActor holds the static information about clients
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct Client {
    // key (as seed) -- NB: this needs to be fixed before `on_start`
    key_seed: KeySeed,
    // verification key,

    // the vector of workers to which requests can/will be sent
    known_workers: Vec<WorkerId>,
    // my_expected_id (for debugging)
    my_expected_id: Id,
}

// ideally, this _would_ be part of the `Vactor` trait
// ... well, now it is public :-/
pub enum Outputs<I, M> {
    // send a message to a single id
    Snd(I, M),
    // broadcast a message to a vec of ids
    // Cast(Vec<I>, M),
    // set a timer (so far, we only have one type of timer)
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

    fn get_vk_bytes(&self) -> VKBytes;

    fn send(&self, id: Id, m: Self::Msg, o: &mut Vec<Outputs<Id, Self::Msg>>) {
        o.push(Outputs::Snd(id, m));
    }
    fn send_(&self, ids: Vec<Id>, m: Self::Msg, o: &mut Vec<Outputs<Id, Self::Msg>>) {
        for i in ids {
            self.send(i, m.clone(), o);
        }
    }

    fn check_back_later(&self, o: &mut Vec<Outputs<Id, Self::Msg>>) {
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

impl Client {
    // a function for generating the next tx
    fn next_tx(tx: TxData) -> TxData {
        // could be "random", but, to keep things simple for the moment:
        vec![if tx[0] % 2 == 0 {
            tx[0] / 2
        } else {
            3 * tx[0] + 1
        }]
    }
}

// the client's behaviour: on_start_vec, on_msg_vec
impl Vactor for Client {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn get_vk_bytes(&self) -> VKBytes {
        use ed25519_consensus::*;
        VerificationKey::from(&SigningKey::from(self.key_seed)).into()
    }

    fn on_start_vec(&self, id: Id) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        if cfg!(debug_assertions) {
            print!("Start client {}", id);
        }
        let client_state = StateEnum::Client(self.known_workers.clone(), self.key_seed, id);
        let mut o = vec![];

        // send a different tx to every worker, to get started
        let mut x = 0;
        for k in &self.known_workers {
            x += 1;
            self.send(*k, TxReq(vec![x], id), &mut o);
        }

        (client_state, o) // return
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
                self.send(*worker, TxReq(new_tx, id), &mut o);
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
    w_hash: &WorkerHash,
    sig: WorkerHashSignature,
) -> bool {
    //fn verify(&self, &Sig, &[u8]) -> Result<(), Error>
    use ed25519_consensus::Signature;
    use id_mapping::*;
    let the_reg = REG_MUTEX.lock().unwrap();
    let key = the_reg.lookup_vk(src).unwrap();
    let w_bytes = &bincode::serialize(&w_hash).unwrap();
    match key.verify(&Signature::from(sig), w_bytes) {
        Ok(_) => true,
        Err(_) => {
            println!("got a bad signature from worker #{}", src);
            false
        }
    }
}

// we need to order transaction vectors to produce worker hashes
// the order is induced by the sequence number
// after filtering the take `tk`
// the code is pretty generic
fn filter_n_sort<T: Clone, C: Clone, U: Ord + Clone>(
    vector: &[(T, C, U, Take)],
    tk: Take,
) -> Vec<(T, C, U, Take)> {
    // let x be the vector of transaction whose “take” is tk
    let mut x = vector
        .iter()
        .cloned()
        .filter(|x| x.3 == tk)
        .collect::<Vec<(T, C, U, Take)>>();
    // sort x, ascending in the sequence number (within the take)
    x.sort_by(|a, b| a.2.cmp(&b.2));
    // "return" x
    x
}

// the behaviour of workers, according to the spec
impl Worker {
    fn process_tx_req(
        &self,
        src: Id,
        client: ClientId,
        tx: TxData,
        ack: <Worker as Vactor>::Msg,
        state: &mut WorkerState,
        key_seed: KeySeed,
    ) -> Vec<Outputs<Id, <Worker as Vactor>::Msg>> {
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
            state.take += 1;
            if cfg!(debug_assertions) {
                println!("Worker {:?} at take {}", self, state.take);
            }

            // check if we can finish a batch
            if state.tx_buffer.len() >= BATCH_SIZE {
                // MENDME: batches "generic" **and** serializable -- ̈"somehow" ?!
                // right now, a batch is just a vector of TxData, Vec<TxData>

                // create and process batch hash
                let w_hash = WorkerHash {
                    hash: hash_of(&state.tx_buffer),
                    take: state.take,
                    length: state.tx_buffer.len(),
                    collector: state.the_id,
                };
                if cfg!(debug_assertions) {
                    assert!(w_hash.collector == self.my_expected_id);
                }
                let sig: WorkerHashSignature = sign_serializable(key_seed, &w_hash);

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
        w_hash: &WorkerHash,
        sig: WorkerHashSignature,
        state: &mut WorkerState,
    ) -> Vec<Outputs<Id, <Worker as Vactor>::Msg>> {
        let mut res = vec![];
        let hash_take = w_hash.take;
        let all_src_txs = state.tx_buffer_map[&src].clone();
        let relevant_txs = filter_n_sort(&all_src_txs, hash_take);
        if relevant_txs.len() == w_hash.length {
            if cfg!(debug_assertions) {
                println!(
                    "uploading worker hash {:?} to primary {:?}",
                    w_hash, state.primary
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
    fn process_whx(
        &self,
        src: WorkerId,
        w_hash: &WorkerHash,
        sig: WorkerHashSignature,
        state: &mut WorkerState,
    ) -> Vec<Outputs<Id, <Worker as Vactor>::Msg>> {
        let mut res = vec![];
        if is_valid_signature(src, w_hash, sig) {
            if cfg!(debug_assertions) {
                println!("Worker {:?} got valid worker hash {:?}", self, w_hash);
            }
            // NB:
            // each worker has an independent counter of “takes/chunks”
            res = self.process_checked_w_hx(src, w_hash, sig, state)
        } else {
            println!("Got bad worker hash");
        }
        res
    }

    fn on_timeout_vec(
        &self,
        _id: Id,
        state: &mut Cow<'_, <Worker as Vactor>::State>,
    ) -> Vec<Outputs<Id, <Worker as Vactor>::Msg>> {
        // specifically check pending_hxs, fifo style, one at a time
        if let StateEnum::Worker(ref mut state, _, _) = state.to_mut() {
            let mut res = vec![];
            if state.pending_hxs.is_empty() {
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

impl Vactor for Worker {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn get_vk_bytes(&self) -> VKBytes {
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
        let state = StateEnum::Worker(
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
        let worker_state: &mut WorkerState;
        let key_seed: KeySeed;
        if let StateEnum::Worker(ref mut s, k, _i) = state.to_mut() {
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
                self.process_tx_req(src, client, tx, msg, worker_state, key_seed)
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
                self.process_whx(src, &w_hash, sig, worker_state)
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

const FULL_HEADER: usize = 5;
impl Primary {
    fn check_n_update_pending_requests(
        &self,
        _i: ValidatorId,
        _rnd: Round,
        _whxs: Vec<(WorkerId, Take)>,
        _p_state: &mut PrimaryState,
    ) -> bool {
        // let res : bool;
        // p_state.pending_requests.push_back((r,whxs));
        // CONTINUE HERE
        // match p_state.pending_requests.get(&i) {
        //     Some(x) => {
        //         match x {
        //             Some((r, whxs)) => {
        //             }
        //             None => {
        //             }
        //         }
        //     },
        //     None => {
        //     }
        // }
        false // res
    }

    fn new_header_announcement(
        &self,
        // the generating validator's id
        v: ValidatorId,
        p_state: &mut PrimaryState,
    ) -> Vec<Outputs<Id, <Primary as Vactor>::Msg>> {
        // prepare the “table of contents”
        let wh_contents: Vec<(WorkerId, Take)> = p_state
            .worker_hash_set
            .clone()
            .into_iter()
            // the WorkerId an Take
            .map(|(i, w)| (i, w.take))
            .collect();
        // the message to be sent to all fellow validators
        let msg = if p_state.rnd == GENESIS_ROUND {
            NextHeader(
                // the current round, i.e., GENESIS_ROUND
                p_state.rnd,
                // vector of collector-take pairs, identifying the worker hashes
                wh_contents,
                // availability certificate
                None, // Option<AC>,
                None, // hashes of signed quorums
                      // Option<Vec<SQHash>>
            )
        } else {
            panic!("not implemented yet");
            // NextHeader(
            //     p_state.rnd,
            //     wh_list,
            //     None, // PLACEHOLDER for proper availability certificate
            //     // Option<AC>
            //     None, // PLACEHOLDER for signed quorum information
            // )
        };

        // the result of "outputs" (in the sense of stateright)
        let mut res = vec![];
        self.send_(p_state.validators.clone(), msg, &mut res);
        res
    }

    // react to a forwarded worker hash (WHxFwd-msg)
    fn follow_up_whx_fwd(
        &self,
        wh_hash: WorkerHash,
        p_state: &mut PrimaryState,
    ) -> Vec<Outputs<Id, <Primary as Vactor>::Msg>> {
        // check if it belongs to a wanted header

        vec![]
    }

    fn check_availability(
        &self,
        i: ValidatorId,
        r: Round,
        whxs: Vec<(WorkerId, Take)>,
        p_state: &mut PrimaryState,
    ) -> Vec<WorkerHash> {
        let mut the_list = vec![];
        let mut no_takes_missing = true;
        for (i, t) in whxs.into_iter() {
            if let Some(i_takes) = p_state.map_of_worker_hashes.get(&i) {
                if let Some(wh) = i_takes.get(&t) {
                    the_list.push(wh.clone());
                }
            } else {
                no_takes_missing = false;
                break;
            }
        }
        if no_takes_missing {
            the_list
        } else {
            vec![]
        }
    }

    // when a primary gets a "bump" from a peer validator
    // it tries to generate a header, signs it, and commits
    fn process_sign_request(
        &self,
        i: ValidatorId,
        r: Round,
        whxs: Vec<(WorkerId, Take)>,
        p_state: &mut PrimaryState,
        key_seed: KeySeed,
    ) -> Vec<Outputs<Id, <Primary as Vactor>::Msg>> {
        // 1. retrieve the relevant worker hashes
        let list_to_sign = self.check_availability(i, r, whxs, p_state);
        if !list_to_sign.is_empty() {
            // ok, we got everything
            // 2. (hash-)sign the worker hash
            let the_sig = sign_serializable(key_seed, &list_to_sign);
            let signature = HeaderSignature {
                sig: the_sig,
                val: p_state.the_id,
            };
            // 3. “commit” to the signed worker hash, by sending it back
            let msg = HeaderSig(p_state.the_id, p_state.rnd, signature);
            let mut outs = vec![];
            self.send_(p_state.validators.clone(), msg, &mut outs); // FIXME this should go back to the creator
            outs // "return"
        } else {
            // we set a timer
            // 2'. set a timer
            let mut outs = vec![];
            self.check_back_later(&mut outs);
            outs // "return"
        }
    }
}
impl Vactor for Primary {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn get_vk_bytes(&self) -> VKBytes {
        use ed25519_consensus::*;
        VerificationKey::from(&SigningKey::from(self.key_seed)).into()
    }

    // cf. `on_start` of Actor
    fn on_start_vec(&self, id: Id) -> (Self::State, Vec<Outputs<Id, Self::Msg>>) {
        println!("start primary {}", id);
        let key_seed = self.key_seed;
        // let map: HashMap<WorkerId, Vec<WorkerHashData>> = c! {
        //     key => vec![],
        //     for key in self.local_workers.clone()
        // };
        if cfg!(debug_assertions) {
            assert!(id == self.my_expected_id);
            for x in self.peer_validators.clone() {
                assert!(x != id);
            }
        }
        (
            StateEnum::Primary(
                PrimaryState {
                    map_of_worker_hashes: BTreeMap::new(),
                    worker_hash_set: BTreeSet::new(),
                    the_id: id,
                    validators: self.peer_validators.clone(),
                    rnd: GENESIS_ROUND,
                    pending_requests: BTreeMap::new(),
                    expected_takes: BTreeMap::new(),
                },
                key_seed,
                id,
            ),
            vec![],
        ) // default value for one ping pongk
    }

    // the correct primary's behaviour
    fn on_msg_vec(
        &self,
        id: Id,
        state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id, Self::Msg>> {
        let p_state;
        let key_seed;
        if let StateEnum::Primary(ref mut state, key, _) = state.to_mut() {
            p_state = state;
            if cfg!(debug_assertions) {
                assert!(p_state.the_id == id);
                assert!(p_state.the_id == self.my_expected_id);
            }
            key_seed = *key;
        } else {
            // the following would be fatal bug
            panic!("The state {:?} is not even of the right kind", state);
        }
        match msg {
            WHxFwd(wh_data, sig) => {
                // we have received a foreign worker hash,
                // which we have to keep (as it will be part of a header)
                // 1. check_signature
                if !is_valid_signature(src, &wh_data, sig) {
                    // well, that's not good (behavior)
                    if cfg!(debug_assertions) {
                        println!("signature check failed for WHxFwd");
                    }
                    vec![] // return
                } else {
                    match p_state.map_of_worker_hashes.get_mut(&wh_data.collector) {
                        Some(v) => {
                            v.insert(wh_data.take, wh_data.clone());
                            // check if this triggers a header signature
                            self.follow_up_whx_fwd(wh_data, p_state) // "return"
                        }
                        None => {
                            // panic!{"map of worker hashes messed up at {:?}", self};
                            vec![]
                        }
                    }
                }
            }
            WorkerHx(w_hash, _) => {
                // we got a new, locally collected worker hash
                p_state.worker_hash_set.insert((src, w_hash));
                if p_state.worker_hash_set.len() > FULL_HEADER {
                    self.new_header_announcement(src, p_state)
                } else {
                    // nothing to do but (passively) wait for more hashes
                    vec![]
                }
            }
            NextHeader(r, whxs, _ac, _sqhx) => {
                // check if we have all relevant worker hashes
                // if so, sign (if this is the first header)
                // otherwise, the **next arriving WHxFwd-msg** will trigger a check
                if r > GENESIS_ROUND {
                    println!("not genesis");
                    vec![]
                } else {
                    self.process_sign_request(src, r, whxs, p_state, key_seed)
                }
            }
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
    Client(Client),
    Worker(Worker),
    Primary(Primary),
}

//
// fn generate_all_actors(cfg: NarwhalModelCfg, mode: ModesEnum, ports: Vec<u16>) -> Vec<ActorEnum> {
//     let mut res = vec![];
//     // match mode {
//     //     ModesEnum::Spawn =>
//     // }
//     res
// }

// we collect all above kinds of Vactors into an enum
// and Vactor-behaviour of the enum obtained by
// delegating the function calls to the respective type
#[derive(Delegate, Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[delegate(Vactor)]
enum HNActor {
    Client(Client),
    Worker(Worker),
    Primary(Primary),
}

lazy_static! {
    // a dummy signature for keys
    static ref DUMMY_SIG: ed25519_consensus::Signature = [0; 64].into();
}
impl Actor for HNActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        let vk_bytes = self.get_vk_bytes();
        match ed25519_consensus::VerificationKey::try_from(vk_bytes) {
            Ok(vk) => {
                use id_mapping::*;
                let mut the_reg = REG_MUTEX.lock().unwrap();
                the_reg.register_key(id, vk, *DUMMY_SIG);
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

// a module for learner graphs (cf. Heterogeneous Paxos)
// mod learner_graph {
//     // the learner graph trait uses
//     use std::collections::{HashMap, HashSet};
//     use std::iter::Iterator;

//     type HashSetMap<K,V> = HashMap<K, HashSet<V>>;
//     // learner graph trait
//     // ... based on github.com/isheff/het_paxos_ref
//     pub trait LearnerGraph {
//         type Learner;
//         type Validator;

//         fn get_learners(&self) -> dyn Iterator<Item = Self::Learner>;

//         fn get_quorums(&self) -> HashSetMap<Self::Learner, Self::Validator>;

//         fn are_entangled(&self, _: Self::Learner, _: Self::Learner) -> bool;
//     }
// }

#[derive(Clone)]
struct NarwhalModelCfg {
    worker_index_count: usize,
    primary_count: usize,
    client_count: usize,
    network: Network<<HNActor as Actor>::Msg>,
}

// generates a key_seed : KeySeed
// using ed25519_consensus::SigningKey rand::thread_rng
fn fresh_key_seed() -> KeySeed {
    use ed25519_consensus::SigningKey;
    use rand::thread_rng;
    let key = SigningKey::new(thread_rng());
    let key_seed = key.to_bytes();
    let key_again: SigningKey = SigningKey::from(key_seed);
    assert!(key.to_bytes() == key_again.to_bytes());
    key_seed
}

// we have to derive an ActorModel from based on a configuration of actors
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

    // we need the Copy trait for histories in stateright
    #[allow(clippy::ptr_arg)]
    fn record_msg_in(
        _cfg: &Self,
        // history collects the sequence of messages sent (&received ⁈)
        history: &Vec<Envelope<<HNActor as Actor>::Msg>>,
        env: Envelope<&<HNActor as Actor>::Msg>,
    ) -> Option<Vec<Envelope<<HNActor as Actor>::Msg>>> {
        let mut h = history.clone();
        let e = env.to_cloned_msg();
        h.push(e);
        Some(h)
    }

    // we need the Copy trait for histories in stateright
    #[allow(clippy::ptr_arg)]
    fn record_msg_out(
        _cfg: &Self,
        history: &Vec<Envelope<<HNActor as Actor>::Msg>>,
        env: Envelope<&<HNActor as Actor>::Msg>,
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
            Vec::new(), // here will go histories, i.e., sequences of
        )
        // we **have**add actors in the following order
        // wic = worker_index_count
        // pc = primary_count
        // cc = client_count
        // 1. workers: 0..wic*pc
        // 2. primaries: wic*pc..(wic+1)*pc
        // 3. clients: (wic+1)*pc..(wic+1)*pc+cc
        .actors(c![HNActor::Worker(Worker{
                index: i as u64,
                primary: Id::from(self.get_primary_idx(j)),
                mirror_workers: self.calculate_mirror_workers_and_id(i,j).0,
                my_expected_id: self.calculate_mirror_workers_and_id(i,j).1,
                key_seed: fresh_key_seed(),
                take: FIRST_TAKE,
            }),
                       for i in 0..self.worker_index_count,
                       for j in 0..self.primary_count])
        .actors(c![HNActor::Primary(Primary{
                peer_validators: self.calculate_peer_validators_and_id(p).0,
                my_expected_id: self.calculate_peer_validators_and_id(p).1,
                key_seed: fresh_key_seed(),
                local_workers:self.calculate_local_workers(p),
            }), for p in 0..self.primary_count])
        .actors(c![HNActor::Client(Client{
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





#[derive(PartialEq, Debug)]
enum ModesEnum {
    Check,
    Spawn,
    Explore,
}
use ModesEnum::*;

// choice for which mode to operate in (hard coded)
//const SUP:ModesEnum = Check;
//const SUP:ModesEnum = Spawn;
const SUP: ModesEnum = Explore;

// for spawning actors (locally)
// use std::net::{SocketAddrV4, Ipv4Addr};

#[allow(clippy::assertions_on_constants)]
fn main() {
    println!(
        "There are three modes of operation {:?}, {:?}, and {:?}",
        ModesEnum::Check,
        ModesEnum::Explore,
        ModesEnum::Spawn
    );
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
                Client{
                    known_workers:worker_ids.clone(),
                    my_expected_id:Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, client_port + y)),
                    key_seed: fresh_key_seed(),
                },
                for y in 0..CLIENT_COUNT
            ];
            // create primary structs:

            let primaries = c![
                Primary{peer_validators : primary_ids.clone(),
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
                Worker{
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
                all_vactor_vec.push((i, HNActor::Client(a)));
            }
            for (i, a) in primary_actor_vec {
                all_vactor_vec.push((i, HNActor::Primary(a)));
            }
            for (i, a) in worker_actor_vec {
                all_vactor_vec.push((i, HNActor::Worker(a)));
            }

            spawn(
                serde_json::to_vec,
                |bytes| serde_json::from_slice(bytes),
                all_vactor_vec,
            )
            .unwrap();

            // "the
            use ed25519_consensus::{Signature, SigningKey, VerificationKey};
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
                let sig_bytes: Signature = sig;
                let vk_bytes: VKBytes = VerificationKey::from(&sk).into();

                (vk_bytes, sig_bytes)
            };

            // Verify the signature
            assert!(VerificationKey::try_from(vk_bytes)
                .and_then(|vk| vk.verify(&sig_bytes, msg))
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
