// `main.rs` of Heterogeneousp Narwhal
use serde::{Deserialize, Serialize};
use std::fmt::Debug; // Display, Formatter (...to be added)

// ambassador (see also https://github.com/Heliozoa/impl-enum)
use ambassador::{delegatable_trait,Delegate}; 

// For hashing, we use
// these 8 (eight) lines, based on doc.rust-lang.org/std/hash/index.html
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
    pub trait LearnerGraph {
        type Learner;
        type Validator;

        fn get_learners(&self) -> dyn Iterator<Item = Self::Learner>;

        fn get_quorums(&self) -> HashMap<Self::Learner, HashSet<Self::Validator>>;

        fn are_entangled(&self, learner_a: Self::Learner, learner_b: Self::Learner) -> bool;
    }
}

mod pki {
    // ------- elliptic curve signatures imports (kudos to Daniel) ------
    use ed25519_consensus::*;
    use rand::thread_rng;
    use std::convert::TryFrom;

    pub trait Registry {
        fn register(&mut self, _: stateright::actor::Id, _: VerificationKey) -> bool;
    }

    use std::collections::HashMap;
    pub struct KeyTable {
        map: HashMap<stateright::actor::Id, VerificationKey>,
    }

    impl Registry for KeyTable {
        fn register(&mut self, id: stateright::actor::Id, vk: VerificationKey) -> bool {
            self.map.insert(id, vk) != None
        }
    }

    fn get_vk(sk: SigningKey) -> VerificationKey {
        VerificationKey::from(&sk)
    }

    fn private_test_ed25519_consensus() {
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
}

// all about actors from stateright
use stateright::actor::*;

// this ↑ uses clone-on-write
// → doc.rust-lang.org/std/borrow/enum.Cow.html
use std::borrow::Cow;

// for spawning actors (locally)
// use std::net::{SocketAddrV4, Ipv4Addr};

type TxData = u64;

// generic transaction: ‼ using rustc 1.69.0-nightly (5e37043d6 2023-01-22)
trait Tx<T>: serde_traitobject::Serialize + serde_traitobject::Deserialize {
    fn get_data(&self) -> T;
}

// simplest implementation instance
impl Tx<u64> for u64 {
    fn get_data(&self) -> u64{
        *self
    }
}

// FIXME: "generic" **and** serializable -- ̈"somehow" ?!
// #[derive(Serialize, Deserialize)]
// struct ConcreteTx<T:Serialize + ?Sized + 'static> {
//     #[serde(with = "serde_traitobject")]
//     tx_data: T,
// }
//
// impl Tx<u64> for ConcreteTx<u64>{
//     fn get_data(&self) -> u64{
//         *self
//     }
// }


// the type of batches of transactions, collected from clients
trait Batch<T> {
    fn get_txs(&self) -> Vec<Box<dyn Tx<T>>>;
}


// worker hash data type
// serialization matters as in https://crates.io/crates/bincode
#[derive(Serialize, Deserialize, Clone, Debug, Eq, PartialEq, Hash)]
struct WorkerHashData {
    // the round
    rnd: u64,
    // the number of txs of this worker hash
    length: usize,
    // the hash
    hash: u64,
}

use serde_big_array::BigArray;

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

// the enumeration of all possible kinds of message
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
enum MessageEnum {
    // submissions of transactions by the client/user
    SubmitTx(TxData, ClientId),
    // acknowledgments of transactions by the worker
    TxAck(TxData, WorkerId),
    // broadcasting a tx (or its erasure code) to mirror workers
    TxToAll(TxData, ClientId),
    // Worker Hash / referencing a batch of transactions
    WorkerHash(
        WorkerHashData,
        #[serde(with = "BigArray")] WorkerHashSignature,
    ), //
}

use crate::MessageEnum::*;

const GENESIS_ROUND: u64 = 0;
const BATCH_SIZE: usize = 3;

// the state type of workers
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct WorkerState {
    // the buffer for received transactions
    tx_buffer: Vec<(TxData, ClientId)>,
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

#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct WorkerActor {
    // the index of a worker
    index: WorkerIndex,
    // the primary
    primary: ValidatorId,
    // the ids of workers of the same index, aka mirro workers
    mirror_workers: Vec<Id>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct PrimaryActor {
    //
    peer_validators: Vec<Id>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
struct ClientActor {
    // some immutable information
    /// random_seed : Option<u64>,
    // initial request number
    /// initial_requests : u64,
    // function for new requests, optionally pseudo-random
    // new_req : fn(u64) -> u64,
    // the vector of workers to which requests can/will be sent
    known_workers: Vec<WorkerId>,
}

// ideally, this _would_ be part of the `Vactor` trait
// at least it is private 
enum Outputs<I,M> {
    Snd(I, M),
    Cast(M),
    Timer(usize),
}



// The following is based on stateright's Actor trait,
// which can be lifted to enums via amabassor,
// which in turn delegates calls to the enum to the respective types
// the relation to the Actor trait is then given later by
// TODO: add reference to where the Actor is implemented using Vactor 

#[delegatable_trait] 
trait Vactor: Sized {
    type Msg: Clone + Debug + Eq + Hash;
    type State: Clone + Debug + PartialEq + Hash;
    fn on_start_vec(
        &self,
        id: Id
    ) -> (Self::State, Vec<Outputs<Id,Self::Msg>>);

    fn on_msg_vec(
        &self,
        id: Id,
        state: &mut Cow<'_, Self::State>,
        src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id,Self::Msg>>;

    fn on_timeout_vec(
        &self,
        _id: Id, 
        _state: &mut Cow<'_, Self::State>
    ) -> Vec<Outputs<Id,Self::Msg>>{
        Vec::new()
    }
}

// the client actor, directly as an actor 
// - sends new requests, ideally constantly and uniformly
// > NB: not easily liftable at the present for stateright (via ambassador)
// > due to Out<Self> -- to be changed to Out<Self::Msg>
// > in the signatures of `on_start`, `on_msg`, `on_timeout`
impl Actor for ClientActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        print!("start client {}", id);
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key = SigningKey::new(thread_rng()).to_bytes();
        // send a tx to every work
        let mut x = 0;
        for k in &self.known_workers {
            x = x + 1;
            o.send(*k, SubmitTx(x, id));
        }
        // the known workers are the only state of the client
        // ... so far
        Client(self.known_workers.clone(), key)
    }

    fn on_msg(
        &self,
        id: Id,
        _state: &mut Cow<Self::State>,
        _src: Id,
        msg: Self::Msg,
        o: &mut Out<Self>,
    ) {
        match msg {
            TxAck(tx, worker) => {
                let new_tx = // this should be "random", but ... 
                    if tx%2 == 0 {
                        tx / 2
                    } else {
                        3*tx + 1
                    };
                o.send(worker, SubmitTx(new_tx, id));
                use std::{thread, time};

                let ten_millis = time::Duration::from_millis(10);
                let _now = time::Instant::now();

                thread::sleep(ten_millis);
            }
            _ => {}
        }
    }
}

impl Vactor for ClientActor {
    type Msg = MessageEnum;
    type State = StateEnum;
    
    fn on_start_vec(
        &self,
        id: Id
    ) -> (Self::State, Vec<Outputs<Id,Self::Msg>>){
        print!("start client {}", id);
        use Outputs::*;
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key = SigningKey::new(thread_rng()).to_bytes();
        // send a tx to every work
        let mut x = 0;
        let mut o : Vec<Outputs<Id,Self::Msg>> = vec![];
        for k in &self.known_workers {
            x = x + 1;
            o.push(Snd(*k, SubmitTx(x, id)));
        }
        // the known workers are the only state of the client
        // ... so far
        (Client(self.known_workers.clone(), key),o)
    }

    fn on_msg_vec(
        &self,
        id: Id,
        _state: &mut Cow<'_, Self::State>,
        _src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id,Self::Msg>>
    {
        use Outputs::*;
        match msg {
            TxAck(tx, worker) => {
                let new_tx = // this should be "random", but ... 
                    if tx%2 == 0 {
                        tx / 2
                    } else {
                        3*tx + 1
                    };
                use std::{thread, time};

                let ten_millis = time::Duration::from_millis(10);
                let _now = time::Instant::now();

                thread::sleep(ten_millis);
                vec![Snd(worker, SubmitTx(new_tx, id))]
            }
            _ => {
                println!("oops {:?}", self);
                vec![]
            }
        }
    }
}


impl Actor for WorkerActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, id: Id, _o: &mut Out<Self>) -> Self::State {
        print!("start worker {}", id);
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key_seed = SigningKey::new(thread_rng()).to_bytes();
        Worker(
            WorkerState {
                tx_buffer: vec![],
                primary: self.primary,
                rnd: GENESIS_ROUND,
                mirrors: self.mirror_workers.clone(),
            },
            key_seed,
        )
    }

    fn on_msg(
        &self,
        w_id: Id,
        state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg,
        o: &mut Out<Self>,
    ) {
        use ed25519_consensus::SigningKey;
        print!("worker {} got a message {:?}", w_id, msg);
        match msg {
            SubmitTx(tx, client) => {
                if let Worker(state, key_seed) = state.to_mut() {
                    if client != src {
                        panic!("source not client");
                    } else {
                        // push the tx
                        state.tx_buffer.push((tx, client));
                        // ack the tx
                        o.send(src, TxAck(tx, w_id)); // optional, but ...
                                                      // "broadcast" tx to mirror_workers : Vec<Id>
                        for k in &state.mirrors {
                            o.send(*k, TxToAll(tx, client));
                        }
                        if state.tx_buffer.len() >= BATCH_SIZE {
                            // create and process batch hash
                            let w_hash = WorkerHashData {
                                hash: hash_of(&state.tx_buffer),
                                rnd: state.rnd,
                                length: state.tx_buffer.len(),
                            };
                            let w_bytes: &[u8] = &bincode::serialize(&w_hash).unwrap();
                            let key = SigningKey::from(*key_seed);
                            let sig: WorkerHashSignature = key.sign(w_bytes).to_bytes();
                            o.send(state.primary, WorkerHash(w_hash, sig));
                            // TODO broadcast
                        }
                    }
                } else {
                    // issue
                    panic!("Worker state incorrect");
                }
            }
            _ => {
                // o.send(src, SomeKindOfMessage(DummyMessageType{}));
            }
        }
    }
}

impl Vactor for WorkerActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start_vec(
        &self,
        id: Id
    ) -> (Self::State, Vec<Outputs<Id,Self::Msg>>){
        print!("start worker {}", id);
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key_seed = SigningKey::new(thread_rng()).to_bytes();
        (Worker(
            WorkerState {
                tx_buffer: vec![],
                primary: self.primary,
                rnd: GENESIS_ROUND,
                mirrors: self.mirror_workers.clone(),
            },
            key_seed,
        ),vec![])
    }

    fn on_msg_vec(
        &self,
        w_id: Id,
        state: &mut Cow<'_, Self::State>,
        src: Id,
        msg: Self::Msg,
    ) -> Vec<Outputs<Id,Self::Msg>> {
        use Outputs::*;
        use ed25519_consensus::SigningKey;
        print!("worker {} got a message {:?}", w_id, msg);
        match msg {
            SubmitTx(tx, client) => {
                let mut o : Vec<Outputs<Id,Self::Msg>> = vec![];
                if let Worker(state, key_seed) = state.to_mut() {
                    if client != src {
                        panic!("source not client");
                    } else {
                        // push the tx
                        state.tx_buffer.push((tx, client));
                        // ack the tx
                        o.push(Snd(src, TxAck(tx, w_id))); // optional, but ...
                        // "broadcast" tx to mirror_workers : Vec<Id>
                        for k in &state.mirrors {
                            o.push(Snd(*k, TxToAll(tx, client)));
                            }
                            if state.tx_buffer.len() >= BATCH_SIZE {
                                // create and process batch hash
                                let w_hash = WorkerHashData {
                                    hash: hash_of(&state.tx_buffer),
                                    rnd: state.rnd,
                                    length: state.tx_buffer.len(),
                                };
                                let w_bytes: &[u8] = &bincode::serialize(&w_hash).unwrap();
                                let key = SigningKey::from(*key_seed);
                                let sig: WorkerHashSignature = key.sign(w_bytes).to_bytes();
                                o.push(Snd(state.primary, WorkerHash(w_hash, sig)));
                                // TODO broadcast
                            }
                            o
                        }
                    } else {
                        // issue
                        panic!("Worker state incorrect");
                    }
                }
                _ => {
                    println!("oops {:?}", &self);
                    vec![]
                    // o.send(src, SomeKindOfMessage(DummyMessageType{}));
                }
            }
        }
    }


impl Actor for PrimaryActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, id: Id, _o: &mut Out<Self>) -> Self::State {
        println!("start primary {}", id);
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key_seed = SigningKey::new(thread_rng()).to_bytes();
        Primary(PrimaryState {}, key_seed) // default value for one ping pongk
    }

    fn on_msg(
        &self,
        _id: Id,
        _state: &mut Cow<Self::State>,
        _src: Id,
        msg: Self::Msg,
        _o: &mut Out<Self>,
    ) {
        match msg {
            _ => {
                //o.send(src, SomeKindOfMessage(DummyMessageType{}));
            }
        }
    }
}

impl Vactor for PrimaryActor {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start_vec(
        &self,
        id: Id
    ) -> (Self::State,Vec<Outputs<Id,Self::Msg>>) {
        println!("start primary {}", id);
        use ed25519_consensus::SigningKey;
        use rand::thread_rng;
        let key_seed = SigningKey::new(thread_rng()).to_bytes();
        (Primary(PrimaryState {}, key_seed),vec![]) // default value for one ping pongk
    }

    fn on_msg_vec(
        &self,
        _id: Id,
        _state: &mut Cow<Self::State>,
        src: Id,
        msg: Self::Msg
    ) -> Vec<Outputs<Id,Self::Msg>> {
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

#[derive(Delegate,Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[delegate(Vactor)]
enum VactorEnum {
    ClientActor(ClientActor),
    WorkerActor(WorkerActor),
    PrimaryActor(PrimaryActor),
}

impl Actor for VactorEnum {
    type Msg = MessageEnum;
    type State = StateEnum;

    fn on_start(&self, id: Id, o: &mut Out<Self>) -> Self::State {
        let (s,v) = self.on_start_vec(id);
        for x in v {
            match x {
                Outputs::Snd(i,m) => o.send(i,m),
                _ => {panic!("not implemented in on_start");}
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
        let v = self.on_msg_vec(id,state,src,msg);
        for x in v {
            match x {
                Outputs::Snd(i,m) => o.send(i,m),
                _ => {panic!("not implemented in on_msg");}
            }
        }
    }
}

#[derive(Clone)]
struct NarwhalModelCfg {
    client_count: usize,
    primary_count: usize,
    worker_index_count: usize,
    network: Network<MessageEnum>,
}

// impl NarwhalModelCfg {
//     fn into_model(self) ->
//         ActorModel<
//             RegisterActor<MessageEnum>,
//             Self,
//             LinearizabilityTester<Id, Register<Value>>>
//     {
//         ActorModel::new(
//                 self.clone(),
//                 LinearizabilityTester::new(Register(Value::default()))
//             )
//             .actors((0..self.server_count)
//                     .map(|i| RegisterActor::Server(PaxosActor {
//                         peer_ids: model_peers(i, self.server_count),
//                     })))
//             .actors((0..self.client_count)
//                     .map(|_| RegisterActor::Client {
//                         put_count: 1,
//                         server_count: self.server_count,
//                     }))
//             .init_network(self.network)
//             .property(Expectation::Always, "linearizable", |_, state| {
//                 state.history.serialized_history().is_some()
//             })
//             .property(Expectation::Sometimes, "value chosen", |_, state| {
//                 for env in state.network.iter_deliverable() {
//                     if let RegisterMsg::GetOk(_req_id, value) = env.msg {
//                         if *value != Value::default() { return true; }
//                     }
//                 }
//                 false
//             })
//             .record_msg_in(RegisterMsg::record_returns)
//             .record_msg_out(RegisterMsg::record_invocations)
//     }
// }

fn main() {
    // let mut tx_vec : Vec<Box<dyn Tx<u64>>> = vec![Box::new(4)] ;
    use std::thread;
    //use stateright::actor::spawn;
    use std::net::{Ipv4Addr, SocketAddrV4};

    // well, "magic" number 3000
    let port = 3000;

    use cute::c; // for “pythonic” vec comprehension
                 // simplest example
    let _squares = c![x*x, for x in 0..10];

    // generate all ids we need
    const WORKER_INDEX_COUNT: u16 = 10;
    const PRIMARY_COUNT: u16 = 10;
    const CLIENT_COUNT: u16 = 4;
    // a bunch of worker IDs
    let worker_ids = c![
        Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST,
                                   port + WORKER_INDEX_COUNT*y + x)
        ),
        for x in 0..WORKER_INDEX_COUNT,
        for y in 0..PRIMARY_COUNT
    ];
    let port = 4000; // hopefully big enough ...
    assert!(4000 > 3000 + (WORKER_INDEX_COUNT + 1) * PRIMARY_COUNT);

    // and their primaries
    let primary_ids = c![
        Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, port + y)),
        for y in 0..PRIMARY_COUNT
    ];

    let port = 4200;
    assert!(4200 > 4000 + PRIMARY_COUNT);

    let client_ids = c![
        Id::from(SocketAddrV4::new(Ipv4Addr::LOCALHOST, port + y)),
        for y in 0..CLIENT_COUNT
    ];
    for x in &client_ids {
        println!("client  id: `{}` generated", x);
    }

    // now XYZ_ids for ZYZ ∈ {worker,primary,client} are generated

    // create actor structs:
    let mut clients = c![
        ClientActor{known_workers:worker_ids.clone()},
        for _x in 0..CLIENT_COUNT
    ];
    // create primary structs:
    let mut primaries = c![
        PrimaryActor{peer_validators : primary_ids.clone()},
        for _x in 0..PRIMARY_COUNT
    ];
    // create worker structs:
    let mut workers = c![
        WorkerActor{
            index : x as u64,
            primary : primary_ids[x as usize],
            mirror_workers : c![
                worker_ids[(WORKER_INDEX_COUNT*z + x) as usize],
                for z in 0..PRIMARY_COUNT
            ],
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

    let mut primary_actor_vec = c![
        (primary_ids[y as usize], primaries[y as usize].clone()),
        for y in 0..PRIMARY_COUNT
    ];
    let mut client_actor_vec = c![
        (client_ids[y as usize], clients[y as usize].clone()),
        for y in 0..CLIENT_COUNT
    ];
    let mut worker_actor_vec = c![
        (worker_ids[(WORKER_INDEX_COUNT*y + x)as usize], workers[(WORKER_INDEX_COUNT*y + x)as usize].clone()),
        for x in 0..WORKER_INDEX_COUNT,
        for y in 0..PRIMARY_COUNT
    ];

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

    
    let mut all_vactor_vec : Vec<(Id, VactorEnum)> = Vec::new();
    for (i,a) in client_actor_vec {
        all_vactor_vec.push((i,VactorEnum::ClientActor(a)));
    }
    for (i,a) in primary_actor_vec {
        all_vactor_vec.push((i,VactorEnum::PrimaryActor(a)));
    }
    for (i,a) in worker_actor_vec {
        all_vactor_vec.push((i,VactorEnum::WorkerActor(a)));
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
