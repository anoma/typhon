use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::collections::{BTreeMap};


// ----------------------------------------------------------------------
// basic data structures
// ----------------------------------------------------------------------

// Digest is one of the aliases for the type of hashes
type Digest = u64;
// signature (as in ed25519_consensus)
type Sig = [u8; 64];
// as signatures are [u8; 64], we serialize using BigArray
use serde_big_array::BigArray;

// signing byte slices with ed25519_consensus

// a module for associating state-right ids with other types of ids, such as
// - ip-addresses
// - anoma's external identities
mod id_mapping {
    // elliptic curve signatures imports (kudos to @D)
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
use std::sync::Mutex;
#[macro_use]
extern crate lazy_static;
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
// one might have dummy post-processing for starters.
//
// NB: There are at least two separate challenges to be resolved:
// a) if the last missing message is delivered via `on_msg` (by stateright),
//    we must be able to know if it is the last missing message that
//    we are waiting for in some of the sub-processes of an actor
// b) we need an efficient data structure, possibly calling for “rust-magic”
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
//    called `message fingerprint` for want of a better name
// 4. [conditions that make us stop waiting]
// Thus, local states will have
// a) a map from (id, fingerprint)-pairs to (fingerprint-set, listener)-pairs
// b) calling the listener happens when the fingerprint-set becomes empty

// all about actors from stateright
use stateright::actor::Id;
//use stateright::*;
// stateright uses clone-on-write for state-changes
// -> doc.rust-lang.org/std/borrow/enum.Cow.html
// use std::borrow::Cow;

// a blob of data, part of an (encrypted) transaction
type TxBlob = u64;
// a transaction is just an arbitrary "array" of blobs
type TxData = Vec<TxBlob>;
// each worker assigns a sequence number to transactions
type SeqNum = usize;
// batches of transactions are numbered as well by the worker
type BatchNumber = u32;
#[allow(dead_code)]
const FIRST_BATCH: BatchNumber = 0;

// availability certificate
type AC = (); // TO BE REFINED/DEFINED

// hashes of signed quorums
type SQHash = (); // TO BE REFINED

// worker hash data type `WorkerHashData`
// (see https://crates.io/crates/bincode for serialization matters)
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
struct WorkerHashData {
    // the hash (of a batch of transactions) 
    hash: u64,
    // the number of txs in (the references batch of) this worker hash
    length: usize,
    // the batch number (equal to the round number in Narwhal&Tusk)
    batch: BatchNumber,
    // the id of the worker collecting the transactions
    collector: WorkerId,
}
// the (minimum) length of batches used in worker hashes
#[allow(dead_code)]
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
#[allow(dead_code)]
type WorkerIndex = u64;

// data type of headers (to be signed by primaries)
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
struct HeaderData {
    // the “creator” of the header
    creator: ValidatorId,
    // the worker hashes (produced by the creator's workers)
    worker_hashes: Vec<WorkerHashData>,
    // the validity certificate
    certificate: Option<AC>,
    // the signed quorum hashes
    hashes: Option<Vec<SignedQuorumHash>>,
}

// the enumeration of all possible kinds of messages
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
enum MessageEnum {
    // --- transaction level --
    // transaction requests, sent by the client/user to a Narwhal worker
    TxReq(TxData, ClientId),
    // acknowledgments of transactions `TxReq` (by workers)
    TxAck(TxData, WorkerId),
    // broadcasting a transaction (its trivial erasure code) to mirror workers
    TxToAll(TxData, ClientId, SeqNum, BatchNumber),

    // --- worker hash level --
    // Worker Hash Broadcast (worker => worker)
    WHxToAll(WorkerHashData, #[serde(with = "BigArray")] WorkerHashSignature),
    // Worker Hash "upload"/provision (worker -> primary)
    WorkerHx(WorkerHashData, #[serde(with = "BigArray")] WorkerHashSignature),
    // Worker Hash forwarding (worker -> primary)
    WHxFwd(WorkerHashData, #[serde(with = "BigArray")] WorkerHashSignature),

    // --- header level --
    // header announcement: the request for header signature (primary => primary)
    NextHeader(
        // the announcing primary / validator
        ValidatorId,
        // round Number
        Round,
        // list of collector-batch number pairs, identifying the worker hashes
        Vec<(WorkerId, BatchNumber)>,
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

// use crate::MessageEnum::*;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum MessageFingerprint {
    #[allow(dead_code)]
    X(Digest), // a mere hash pointer
}

// the round of a validator (e.g., u64)
type Round = u64;
// the first round, aka genesis
#[allow(dead_code)]
const GENESIS_ROUND: Round = 0;

fn main() {
    println!("Hello, the source has some types for the Typhon Specs Synthesis https://hackmd.io/zxl_2-8rSe63hT689_jEDA !");
}
