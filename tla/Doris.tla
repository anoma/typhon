---------------------------- MODULE Doris -----------------------------------
(***************************************************************************)
(* Doris is DAG mempool that is similar to the Narwhal mempool with Tusk   *)
(* as consensus.  The latter was proposed by Danezis, Kokoris Kogias,      *)
(* Sonnino, and Spiegelman in their                                        *)
(* `^\href{https://arxiv.org/abs/2105.11827}{paper.}^' Further inspiration *)
(* is taken from `^\href{https://arxiv.org/abs/2102.08325}{DAG-rider,}^' a *)
(* precursor to Narwhal.                                                   *)
(*                                                                         *)
(* We shall refer to these papers as [N&T] and [DAG-R], respectively.      *)
(*                                                                         *)
(* The following differences deserve mention.                              *)
(*                                                                         *)
(* ① In Narwhal, [c]lients send transactions to worker machines at all     *)
(* validators.  [N&T].  This would lead possibly lead to duplicate         *)
(* transactions in batches.  "A load balancer ensures transactions data    *)
(* are received by all workers at a similar rate" [N&T].                   *)
(*                                                                         *)
(* Finally, we define *hashes* of batches and *digests* of blocks; in this *)
(* way, we get a short term for each of these two entities.                *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Functions

\* For the module "Functions", we rely on the \*
\*`^\href{https://tinyurl.com/2ybvzsrc}{Community Module.}^'

-----------------------------------------------------------------------------

(***************************************************************************)
(*                             GENERAL SETUP                               *)
(***************************************************************************)

(***************************************************************************)
(* We make the usual assumption about Byzantine failures.  That is,        *)
(* besides a partially synchronous network, we have                        *)
(*                                                                         *)
(* - a total number of validators                                          *)
(*                                                                         *)
(* - of which less than one third exhibit Byzantine behaviour.             *)
(*                                                                         *)
(* In the typical setting with N = 3f+1 validators,                        *)
(*                                                                         *)
(* - a "quorum" is any set that contains more than two thirds of all       *)
(*   nodes;                                                                *)
(*                                                                         *)
(* - a "weak quorum" is a set of nodes whose intersection with any quorum  *)
(*   is non-empty.                                                         *)
(***************************************************************************)

\* Following Lamport's formalization of 
\* `^\href{https://tinyurl.com/2dyuzs6y}{Paxos}^' and 
\* `^\href{https://tinyurl.com/7punrbs2}{Byzantine Paxos,}^'
\* we consider a more general formalization that
\* even could take care of infinite sets.

CONSTANTS Validator,     \* The set of non-faulty (aka good) validators.
          FakeValidator, \* The set of possibly faulty (aka bad) validators.
          ByzQuorum,
            (***************************************************************)
            (* A Byzantine quorum is set of validators that includes a     *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* validators and f bad ones, any set that contains at least   *)
            (* 2f+1 validators is a Byzantine quorum.                      *)
            (***************************************************************)
          WeakQuorum
            (***************************************************************)
            (* A weak quorum is a set of validators that includes at least *)
            (* one good one.  If there are f bad validators, then any set  *)
            (* that contaions f+1 validators is a weak quorum.             *)
            (***************************************************************)

(***************************************************************************)
(*  ByzValidator is the (disjoint) union of real or fake validators.       *)
(*  (See BQA below.)                                                       *)
(***************************************************************************)
ByzValidator == Validator \cup FakeValidator 

(***************************************************************************)
(* The following are the assumptions about validators and quorums as used  *)
(* by Lamport for safety.                                                  *)
(***************************************************************************)
ASSUME BQA == /\ Validator \cap FakeValidator = {}                       
              /\ \A Q \in ByzQuorum : Q \subseteq ByzValidator           
              /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Validator # {}
              /\ \A W \in WeakQuorum : /\ W \subseteq ByzValidator       
                                       /\ W \cap Validator # {}          
          

(***************************************************************************)
(* Based on Lamport's assumption for liveness, we assum BQLA               *)
(***************************************************************************)
ASSUME BQLA ==
          /\ \E Q \in ByzQuorum : Q \subseteq Validator
          /\ \E W \in WeakQuorum : W \subseteq Validator

-----------------------------------------------------------------------------

(***************************************************************************)
(* One idea of Narwhal is explicit parallelism via a number of workers.    *)
(* Each worker of a correct validator will have a "mirror" worker at every *)
(* other validator.  We use a public parameter, typically finite, which    *)
(* serves to index workers such that mirror workers share the same index.  *)
(* There is no point of using invalid indices by bad validators as these   *)
(* would be ignored.                                                       *)
(***************************************************************************)

CONSTANT WorkerIndex \* a publicy known set of indices

\* A specific worker has a worker index and serves a (Byzantine) validator 

Worker == [index : WorkerIndex, val : ByzValidator] 

\* Keep workers and their indices disjoint from validators/primaries

ASSUME WorkerIds ==
           /\ WorkerIndex \cap ByzValidator = {}
           /\ Worker \cap ByzValidator = {}

(***************************************************************************)
(* There is a bijection between ByzValidators and Primaries.  For the sake *)
(* of simplicity, we identify them in the specification.                   *)
(***************************************************************************)

Primary == ByzValidator \* no need to distinguish in the TLA-spec


\* end of "GENERAL SETUP"

-----------------------------------------------------------------------------

(***************************************************************************)
(*                         DATA STRUCTURES                                 *)
(***************************************************************************)

(***************************************************************************)
(* We define the data structures for blocks, and their components, such as *)
(* certificates, acknowledgements, and block digests as used in Narwhal    *)
(* [N&T] and DAG-rider [DAG-R].  We work directly with batches, such that  *)
(* processing individual transactions can be seen as a refinement.         *)
(***************************************************************************)

(***************************************************************************)
(* "On signatures":                                                        *)
(*                                                                         *)
(* The effect of signatures will be modelled via a set of constraints on   *)
(* the messages that Byzantine validators can send, s.t. they cannot       *)
(* impersonate other (non-byzantine) validators.                           *)
(***************************************************************************)

\* The set of batches
CONSTANT Batch

noBatch == CHOOSE x : x \notin Batch

\* Assume there are some batches (for the purpose of liveness)
ASSUME Batch # {}

(***************************************************************************)
(* For the purposes of formal verification, hash functions need to be      *)
(* treated in a peculiar manner, for the simple reason that hash           *)
(* collisions are not strictly impossible.                                 *)
(***************************************************************************)

\* The following fct. "hash" is convenient to model hash functions.

hash == [
         b \in Batch
         |-> 
         [h \in {"hash"} |-> b] \* [ "hash" |-> b] 
        ] 

\* The set of hashes of any possible batch is the range of "hash".

BatchHash == Range(hash)

\* "SomeHx" is an arbitrary finite set of batch-hashes
SomeHx == { X \in SUBSET BatchHash : IsFiniteSet(X) }



\* Concerning  block digests, we again imitate hashing.
\* The structure of blocks then later is restricted,
\* using the assumption BSA (block structure assumption).
\* "Block", the set of blocks whose structure is later ``defined''
\* as BlockStructure

CONSTANT Block

digest == 
        [
          b \in Block
         |-> 
         [d \in {"digest"} |-> b] \* [ "digest" |-> b] 
        ] 

BlockDigest == Range(digest)

(***************************************************************************)
(* "If a block is valid, the other validators store it and acknowledge it  *)
(* by signing its _block digest_, _round number_, and _creator’s           *)
(* identity_." [N&T]                                                       *)
(*                                                                         *)
(* In most cases, the signature will not be the creator, but it could be.  *)
(*                                                                         *)
(* We define the set "Ack" as the set of all acknowledgements of blocks,   *)
(* which are in particular signed by validators.  A correct validator has  *)
(* to store the block (or enough erasure coding segments) for later        *)
(* retrieval (until garbage collection or execution).                      *)
(***************************************************************************)

\*  "Ack", the set of acknowledgements
Ack == [digest : BlockDigest, \* the digest of the acknowledged block
        creator : ByzValidator, \* the id of the block creator
        rnd :     Nat, \* the round number of the block
        sig :     ByzValidator \* the signature of the acknowledgement
       ]

(***************************************************************************)
(* "Once the creator gets 2f + 1 distinct acknowledgments for a block, it  *)
(* combines them into a certificate of block availability, that includes   *)
(* the block digest, current round, and creator identity." [N&T]           *)
(*                                                                         *)
(* We separate out the presence of >= "2f + 1 distinct acknowledgments"    *)
(* and make explicit that they talk about the same block digest.           *)
(***************************************************************************)

\* the "Type" of acks
AckQuorumType == UNION {[Q -> Ack] : Q \in ByzQuorum} 

AckQuorum ==
    { ax \in AckQuorumType :     
             /\ \A v,w \in DOMAIN ax :                                          
                /\ ax[v].digest = ax[w].digest                       
                /\ ax[v].rnd = ax[w].rnd                             
                /\ ax[v].creator = ax[w].creator                 
             /\ \A v \in DOMAIN ax : ax[v].sig = v
    }

\* The second conjunct, 
\* i.e., "\A v \in DOMAIN ax : ax[v].sig = v",
\* implies that we actually have distinct acknowledgments of the same digest,
\* thus making ax an injection. 


\* LEMMA \A ax \in AckQuorum : IsInjective(ax) \* NTH

(***************************************************************************)
(* An AckQuorum is essentially a Certificate of availability.  We thus  *)
(* define an alias and provide commodity functions for reading the fields  *)
(* of the contained acknowledgments, which must all agree on the digest,   *)
(* round, and creator.                                                      *)
(***************************************************************************)

Certificate == AckQuorum
\* CoA == Certificate

getDigest(abq) == abq[CHOOSE v \in DOMAIN abq : TRUE].digest
getRnd(abq) == abq[CHOOSE v \in DOMAIN abq : TRUE].rnd
getCreator(abq) == abq[CHOOSE v \in DOMAIN abq : TRUE].creator

(***************************************************************************)
(* According to [N&T], a valid block must                                  *)
(*                                                                         *)
(* 1.  contain a valid signature from its creator;                         *)
(*                                                                         *)
(* 2.  be at the local round r of the ByzValidator checking it;            *)
(*                                                                         *)
(* 3.  be at round 0 (genesis), or contain certificates for                *)
(*     at least 2f + 1 blocks of round r-1;                                *)
(*                                                                         *)
(* 4.  be the first one received from the creator for round r .            *)
(*                                                                         *)
(* We allow for additional weak links in the sense of DAG-rider [DAG-R].   *)
(* It is not only convenient to define quoruums of certificats as a       *)
(* separate entity, they actually will feature as an important building    *)
(* block in the protocol: batches and certqourums will be signed           *)
(* independently                                                           *)
(***************************************************************************)

\* The "type" of a quorums of certificates of availability
CertQuorumType == UNION {[Q -> Certificate] : Q \in ByzQuorum} 

\* recall, a certificate's c values c[v] are of type Q -> Ack and
\* have getter methods getXYZ(c[v]) -- not c.XYZ
CertQuorum ==
    { cq \in CertQuorumType : \A v,w \in DOMAIN cq :
          \* cq[v] and cq[w] are certificates, i.e., quorums of acks
          /\ getRnd(cq[v]) = getRnd(cq[w])  \* common round 
          \* each element of the quorum concerns a different block
          /\ (v # w => getDigest(cq[v]) # getDigest(cq[w])) 
    } 

\* a bunch of weak Nat
WeakLinks == SUBSET Certificate

noCert == CHOOSE i \in [{} -> Certificate] : TRUE
noLinks == {}

BlockStructure ==
    { b \in [ creator : ByzValidator, \* the block proposer
              rnd :     Nat, \* the round of the block proposal
              bhxs :    SomeHx, \* the batch hashes of the block
              cq :      CertQuorum \cup {noCert}, \* a CoA-quorum 
              wl :      WeakLinks, \* possibly weak links             
              sig :     ByzValidator \* creator signature
            ] :
      /\ b.creator = b.sig \* on redundancy: cf. note on signatures
      /\ \A l \in b.wl : getRnd(l) < b.rnd-1 \* weak (!) links 
      /\ \/ /\ b.rnd = 0 \* either round zero and
            /\ b.cq = noCert \* empty domain allowed
         \/ /\ b.rnd > 0 \* or round non-zero and
            /\ b.cq # noCert \* a proper certificate
            /\ \A Q \in DOMAIN b.cq : getRnd(b.cq[Q]) = (b.rnd - 1)
    }

ASSUMPTION BSA == (Block = BlockStructure)

\* end of "DATA STRUCTURES" 
-----------------------------------------------------------------------------

(* ------------------------------------------------------------------------*)
(*                        MESSAGE STRUCTURE                                *)
(* ----------------------------------------------------------------------- *)


(***************************************************************************)
(* Following                                                               *)
(*  `^\href{https://bit.ly/3a6ydfc}{Lamport's specification of Paxos,}^'   *)
(* we keep all (broadcast) messages in a single set.  There are the        *)
(* following types of message.                                             *)
(*                                                                         *)
(* - "batch" broadcast a batch, **from** a worker (to workers of the same  *)
(*   index).                                                               *)
(*                                                                         *)
(* - "batch-ack" acknowledge a batch (by a worker)                         *)
(*                                                                         *)
(* - "block" a block creator broadcasts a new block                        *)
(*                                                                         *)
(* - "block-ack" acknowledgment *by* a Validator, storing a received block *)
(*                                                                         *)
(* - "cert" broadcasting a certificate from a validator                    *)
(*                                                                         *)
(* We call a "mirror worker" a worker of the same index at a different     *)
(* validator.  We assume that clients take care of resubmission of         *)
(* orphaned transactions.  We assume that clients send a transaction/batch *)
(* only to one validator at a time, and only if the transaction gets       *)
(* orphaned, resubmission is expected.  This assumes that the probability  *)
(* of orphaned transactions is extremely low.  Correct validators only     *)
(* make blocks with batches arriving there in the first place (and not     *)
(* broadcast by workers).                                                  *)
(*                                                                         *)
(* We abstract away all worker-primary communication "inside" validators.  *)
(* Validators should actually use remote direct memory access.  Further    *)
(* refinement could be applied if a message passing architecture was       *)
(* desired.                                                                *)
(***************************************************************************)

\* broadcast a fresh "batch" from a "worker" (to mirror workes)
BatchMessage == [type : {"batch"}, batch : Batch, from : Worker]

\* acknowledge a received "batch" (of mirror workes)
BatchAckMessage == [type : {"batch-ack"}, hx : BatchHash, sig : Worker]

\* creator produces a block and broadcasts it 
BlockMessage == [type : {"block"}, block: Block, creator : ByzValidator]

\* commmitment "by" a validator to have stored a block 
BlockAckMessage == [type : {"block-ack"}, ack : Ack, by : ByzValidator]

\* creator aggregates quorum of acks into a certificate and broadcasts it
CertMessage == [type : {"cert"}, cert : Certificate, creator : ByzValidator]


\* All messages that can be send between workers/primaries/validators
Message ==
    \* broadcast a fresh "batch" from a "worker" (to mirror workes)
    BatchMessage
    \cup
    \* acknowledge a received "batch" (of mirror workes)
    BatchAckMessage 
    \cup
    \* creator produces a block and broadcasts it 
    BlockMessage 
    \cup
    \* commmitment "by" a validator to have stored a block 
    BlockAckMessage
    \cup
    \* creator aggregates acks into a cert and broadcasts it
    CertMessage

\* The set of all messages that are sent by workers and primaries
VARIABLE msgs

\* The rough type of msgs
msgsTypeOK == msgs \in SUBSET Message 

msgsINIT == msgs = {}

\* end of "MESSAGE STRUCTURE"

-----------------------------------------------------------------------------

(*-------------------------------------------------------------------------*)
(*                           LOCAL STATE                                   *)
(*-------------------------------------------------------------------------*)

(***************************************************************************)
(* The local state of validators and workers at validators is              *)
(*                                                                         *)
(* 1. a local round number (corresponding a layer of DAG mempool);         *)
(*                                                                         *)
(* 2. a worker specific pool of received client batches;                   *)
(*                                                                         *)
(* 3. a pool of batch hashes to be included in the next block;             *)
(*                                                                         *)
(* 4. a local storage for (hashes of) batches;                             *)
(*                                                                         *)
(* 5. a local storage for blocks.                                          *)
(***************************************************************************)


\* Each ByzValidator has a local round number (initially 0) 
VARIABLE rndOf

\* The rough type for rndOf
rndOfTypeOK == rndOf \in [ByzValidator -> Nat]

\* "assert" INIT => \A v \in ByzValidator : rndOf[v] = 0
rndOfINIT ==      \A v \in ByzValidator : rndOf[v] = 0


\* Each Worker has a local pool of unprocessed batches (initially {})
VARIABLE batchPool

\* The rough type for batchPool
batchPoolTypeOK == batchPool \in [Worker -> SUBSET Batch]

\* "assert" INIT => \A w \in Worker : batchPool[w] = {}
batchPoolINIT == \A w \in Worker : batchPool[w] = {}



\* Primaries have pools of hashes for the next block (initially {}) 
VARIABLE nextHx

\* The rough type of nextHx
nextHxTypeOK == nextHx \in [Primary -> SomeHx]

\* "assert" INIT => \A p \in Primary : nextHx[p] = {}
nextHxINIT == \A p \in Primary : nextHx[p] = {}


\* Each ByzValidator has storage for batch hashes (initially {})
VARIABLE storedHx

\* The rough type of storedHx
storedHxTypeOK == storedHx \in [ByzValidator -> SUBSET BatchHash]

\* "assert" INIT => \A v \in ByzValidator : storedHx[v] = {}
storedHxINIT == \A v \in ByzValidator : storedHx[v] = {}


\* Each ByzValidator has storage for blocks (initially {}) 
VARIABLE storedBlx
\* The rough type of storedBlx
storedBlxTypeOK == storedBlx \in [ByzValidator -> SUBSET Block]

\* "assert" INIT => \A v \in ByzValidator : storedBlx[v] = {}
storedBlxINIT == \A v \in ByzValidator : storedBlx[v] = {}

\* The combined INIT-predicate concerning the local state
LocalStateINIT ==
  /\ rndOfINIT \* 1.
  /\ batchPoolINIT \* 2. 
  /\ nextHxINIT \* 3. 
  /\ storedHxINIT \* 4. 
  /\ storedBlxINIT  \* 5. 

\* end of "LOCAL STATE"

-----------------------------------------------------------------------------

vars == <<msgs, rndOf, batchPool, nextHx, storedHx, storedBlx>>
  (*************************************************************************)
  (* It is convenient to have a shorthand for all variables in a spec.     *)
  (*************************************************************************)
-----------------------------------------------------------------------------


(***************************************************************************)
(*                             ACTIONS                                     *)
(***************************************************************************)


(***************************************************************************)
(* We will specify the following actions.                                  *)
(*                                                                         *)
(* - [Batch arrival (no message, combined with 'BatchBC')]:                *)
(*                                                                         *)
(*   A new **batch** btch arrives at a **worker** wrkr and is included     *)
(*   into the worker's batchPool. The arriving batch might already be      *)
(*   "known" and/or been submitted to other workers, .e.g., if clients     *)
(*   "misbehave". (Recall that we assume that clients submit their         *)
(*   (batches of) transactions to only one worker.)  Resubmission of an    *)
(*   orphaned batch is a case, which we do not put particular attention    *)
(*   to (yet). We postulate that at most one "copy" of a batch will be     *)
(*   included within a block. We combine batch arrival with the next type  *)
(*   of action (for the sake of simplicity).                               *)
(*                                                                         *)
(* - Batch broadcast 'BatchBC' (message "batch"):                          *)
(*                                                                         *)
(*   A worker 2. broadcasts the                                            *)
(*   batch; then it has to wait for acknowledgements.                      *)
(*                                                                         *)
(* - Batch receive, store, hash, ack  'BatchAck' (message "batch-ack"):    *)
(*                                                                         *)
(*   Reception of a batch, storing and hashing such that later blocks can  *)
(*   be validated and acknowledgements the primary. Finally, a             *)
(*   "batch-ack" for the received batch is sent.                           *)
(*                                                                         *)
(* - Batch ready for block inclusion 'BatchReady' (internal to validator)  *)
(*                                                                         *)
(*   A worker collects acks of a batch, removes it from its "queue", and   *)
(*   puts the batch hash in the primary's pool for the next block.         *)
(*                                                                         *)
(*   "[A] worker [...] creates a batch of transactions, and sends it to the*)
(* [mirror] worker node of each of the other validators; once an           *)
(* [ack]nowledgment has been received by a quorum of these, the            *)
(* cryptographic hash of the batch is shared with the primary of the       *)
(* validator for inclusion in a block." [N&T]                              *)
(*                                                                         *)
(* - Block production and broadcast 'BlockBC' (message "block"):           *)
(*                                                                         *)
(*   A primary builds a block from enough certificates of availability     *)
(*   and batch hashes provided by its workers and broadcasts the           *)
(*   block. "One primary integrates references to [batches] in Mempool     *)
(*   primary blocks."  [N&T]                                               *)
(*                                                                         *)
(* - Block acknowledgement 'BlockAck' (message "block-ack")                  *)
(*                                                                         *)
(*   Receive a block, check its validity, store it, acknowledge it.        *)
(*                                                                         *)
(* - Certificate broadcats 'CertBC' (message "cert")                       *)
(*                                                                         *)
(*   Take enough acknowledgements of a proposed block, aggregate into a    *)
(*   ceritificat, and broadcast the certificate.                           *)
(*                                                                         *)
(* - Advancing the local round 'AdvanceRound' (no message)                 *)
(*                                                                         *)
(*   A validator receives enough certificates to move to the next round.   *)
(***************************************************************************)


(***************************************************************************)
(* We define the subactions of the next-state actions.  We begin by        *)
(* defining an action that will be used in those subactions.  The action   *)
(* Send(m) asserts that message m is added to the set msgs.                *)
(*                                                                         *)
(* taken from `^\href{https://tinyurl.com/2dyuzs6y}{Paxos.tla}^'           *)
(***************************************************************************)

\* sending a message will only be used as "part of" a "full" action 
\* ... and thus no UNCHANGED 
Send(m) == msgs' = msgs \cup {m}

\* ACT "BatchBC", broadcasting a new batch 'b' arriving at a worker 'w'
BatchBC(b, w) ==
  \* "trivial" precondition (checking the typing)
  /\ b \in Batch
  /\ w \in Worker
  \* postcondition: add the batch the the batch pool of w
  /\ batchPool' = [batchPool EXCEPT ![w] = @ \cup {b}]
  \* broadcast the batch {changes the variable set of messages 'msgs'}
  /\ Send([type |-> "batch", batch |-> b, from |-> w])               
  /\ UNCHANGED <<rndOf, nextHx, storedHx, storedBlx>>  

\* ACT "BatchAck", receiving and acknowledging a batch
BatchAck(w) == 
  /\ \E m \in msgs : \E h \in BatchHash :
        \* precondition
        /\ m.type = "batch" \* somebody sent a "batch" message ..
        /\ h = hash[m.batch] \* .. whose batch hash we call h, s.t., ..
        /\ h \notin storedHx[w.val] \* .. the batch is not stored (yet)
        \* postcondition
        \* store batch
        /\ storedHx' = [storedHx EXCEPT ![w] = @ \cup {h}]  
        \* send ack
        /\ Send([type |-> "batch-ack", hx |-> h, sig |-> w]) 
  /\ UNCHANGED <<rndOf, batchPool, nextHx, storedBlx>>

\* ACT "BatchReady" a batch is ready for block inclusion
BatchReady(w) == 
  /\ w \in Worker
  /\ \E b \in Batch : \E Q \in ByzQuorum : \E f \in [Q -> BatchAckMessage] :
     \* precondition
     \* the chosen quorum consists of signerns of the batch 'b'
     /\ \A q \in Q : 
        /\ f[q].sig = q \* thus injective
        /\ f[q].hx = hash[b]
     \* the batch is in the pool of worker w 
     /\ b \in batchPool[w]
     \* postcondition
     \* add hash to primary's set of next hashes
     /\ nextHx' = [nextHx EXCEPT ![w.val] = @ \cup {hash[b]}]
     \* worker 'w' "transfers" the batch (hash) to the primary  
     /\ batchPool' = [batchPool EXCEPT ![w] = @ \ { b } ] 
  /\ UNCHANGED <<msgs, rndOf, storedHx, storedBlx>>

\* A validator produces a block and broadcasts it
GenesisBlockBC(v) ==
  \* typing precondition
  /\ v \in ByzValidator
  \* precondition
  /\ rndOf[v] = 0 \* at local round 0
  \* 
  /\ \E b \in Block : \* "construct" a block of the desired shape
     /\ b.creator = v
     /\ b.rnd = 0
     /\ b.bhxs = nextHx[v]
     /\ b.cq = noCert
     /\ b.wl = noLinks
     \* postcondition
     \* send the block
     /\ Send([type |-> "block", block |-> b, creator |-> v])
     \* empty v's nextHx
     /\ nextHx' = [nextHx EXCEPT ![v] = {}]
  /\ UNCHANGED <<rndOf, batchPool, storedHx, storedBlx>>

\* A certificate c : Q -> Ack is justified if all acks were sent
IsJustifiedCert(c) ==
  /\ c \in Certificate  \* aka AckQuorum
  /\ \A v \in DOMAIN c : \E m \in Message :
     /\ m.type = "block-ack" \*  block-ack 
     /\ m.ack = c[v] \* the ack was sent

\* what's a proper quorum of certificates in (local) round r?
\* - must be at round r-1
\* - all certificates justified
IsProperCertQuorumAt(cq, r) == 
  \* the round is the previous round
  /\ \A v \in DOMAIN cq :
      /\ getRnd(cq[v]) = r - 1
      /\ IsJustifiedCert(cq[v])


\* what's a proper collection of weak links
AreProperWeakLinks(wl, r) == 
  /\ wl \in WeakLinks
  \* the round is smaller than the previous round
  /\ \A l \in wl : getRnd(l) < r - 1

GeneralBlockBC(v) ==
  /\ v \in ByzValidator
  \* precondition
  /\ rndOf[v] > 0 \* at local round > 0
  \* postcondition
  /\ \E cs \in CertQuorum : \E ws \in WeakLinks : \E b \in Block : 
     \* "construct" proper cert quorum
     /\ IsProperCertQuorumAt(cs, rndOf[v])
     \* "construct" proper links
     /\ AreProperWeakLinks(ws, rndOf[v])
     \* "construct" a block of the desired shape, with next batches
     /\ b.creator = v
     /\ b.rnd = rndOf[v]
     /\ b.bhxs = nextHx[v]
     /\ b.cq = cs
     /\ b.wl = ws
     \* send the block
     /\ Send([type |-> "block", block |-> b, creator |-> v])
     \* empty nextHx
     /\ nextHx' = [nextHx EXCEPT ![v] = {}]
  /\ UNCHANGED <<rndOf, batchPool, storedHx, storedBlx>>

\* ACT 'BlockBC': procudtion of a block and broad cast
BlockBC(v) ==
  /\ v \in ByzValidator
  /\ (GeneralBlockBC(v) \/ GenesisBlockBC(v))
  /\ (v \in Validator => ~\E m \in msgs :             
                            /\ m.type = "block"       
                            /\ m.creator = v          
                            /\ m.block.rnd = rndOf[v]
     )\* Lemma: always (~GeneralBlockBC(v) \/ ~GenesisBlockBC(v)) : NTH

\* predicate for checking the storage
HasBlockHashesStored(block, val) ==
 \* we know all batches
 \A h \in block.bhxs : h \in storedHx[val]

\* ACT 'BlockAck' validator accepting and storing a block, followed by ack
BlockAck(v) ==
    /\ v \in ByzValidator
    /\ \E b \in Block : \E w \in ByzValidator : 
       \* precondition
       \* v doesn't know the block yet
       /\ b \notin storedBlx[v] 
       \* block was proposed
       /\ [type |-> "block", block |-> b, creator |-> w] \in msgs
       \* all hashes are present (for correct validators ONLY) 
       /\ (v \in Validator => 
            HasBlockHashesStored(b, v))
       \* store the block for (for correct validators ONLY) 
       /\ (v \in Validator =>
            storedBlx' = [storedBlx EXCEPT ![v] = @ \cup {b}])
       \* construct ack .. 
       /\ \E a \in Ack : 
         /\ a.digest = digest[b]
         /\ a.creator = b.creator
         /\ a.rnd = b.rnd
         /\ a.sig = v
         \* .. to send
         /\ Send([type |-> "block-ack", ack |-> a, by |-> v])
    /\ UNCHANGED <<msgs, batchPool, nextHx, storedHx, storedBlx>>


\* ACT 'CertBC' Broadcast a Certificate
CertBC(v) ==
  /\ v \in ByzValidator
  /\ \E c \in Certificate : 
     \* precondition/test
     /\ IsJustifiedCert(c)      
     \* postcondition/effect (based on witness for \E c : ...)
     /\ Send([type |-> "cert", cert |-> c, creator |-> v])
  /\ UNCHANGED <<rndOf, batchPool, nextHx, storedHx, storedBlx>>


\* Can cert. quorum c trigger validator v to increment the local round?
CertQuorumAdvancesValRnd(c, v) ==
  /\ c \in CertQuorum \* in particular, c : Q -> Certificate, injective
  /\ v \in ByzValidator \* the validator that might increment
  /\ \A w \in DOMAIN c : \E m \in msgs : 
     /\ m.type = "cert"
     /\ m.creator = w
     /\ m.cert = c[w]
     /\ getRnd(c[w]) = rndOf[v]

\* ACT 'AdvanceRound'
AdvanceRound(v) ==
  \* precondition: existence of enough "cert" messages 
  /\ \E c \in CertQuorum : CertQuorumAdvancesValRnd(c, v)
  \* postcondition 
  /\ rndOf' = [rndOf EXCEPT ![v] = @ + 1]
  /\ UNCHANGED <<msgs, batchPool, nextHx, storedHx, storedBlx>>

(***************************************************************************)
(*                      CONSENSUS ABSTRACTION                              *)
(***************************************************************************)

(***************************************************************************)
(* We assume a Tusk like consensus [N&T] in the form of a demonic          *)
(* scheduler that chooses a leader block in each _k_-th round for a        *)
(* globally fixed _k_ > 0.                                                 *)
(***************************************************************************)

\* the constant number of rounds between each leader block commitment
CONSTANT WaveLength
ASSUME WaveLengthAssumption ==
  /\ WaveLength \in Nat
  /\ WaveLength >= 1


CONSTANT LeaderBlock

WaveLengthTimesNat == { n \in Nat : \E i \in Nat : n = WaveLength * i }
  
ASSUME ChoiceOfLeaderBlocks ==
  LeaderBlock \in [WaveLengthTimesNat -> ByzValidator]


(***************************************************************************)
(*                         COMMITTED BLOCK                                 *)
(***************************************************************************)
 
(***************************************************************************)
(* We define when a block is commited, relative to the LeaderBlock         *)
(* selection.  Later garbage collected blocks will remain commited.        *)
(*                                                                         *)
(* We take the following necessary (and sufficient) condition for          *)
(* commitment of a leader block (e.g., if chosen as candidate leader       *)
(* block):                                                                 *)
(*                                                                         *)
(* 1.  There is a weak quorum of blocks, each of which                     *)
(*   a) references the block via its certificate quorum and                *)
(*   b) has itself obtained a certificate of availability (broadcast by    *)
(*      its creator).                                                      *)
(*                                                                         *)
(* We define several auxiliary predicates .                                *)
(*                                                                         *)
(* - 'linksTo',                                                            *)
(*   the relation of direct links in the mempool DAG                       *)
(*                                                                         *)
(* - 'isCauseOf',                                                          *)
(*   the transitive closure of the (opposite of) 'liksTo'-relation         *)
(*                                                                         *)
(* - 'CausalHistory',                                                      *)
(*   the set of blocks that are causes of a block                          *)
(*                                                                         *)
(* - 'IsCertified',                                                        *)
(*   the predicate for checking if a block is certified                    *)
(*                                                                         *)
(* - 'CertifiedBlocks',                                                                      *)
(*   the set of all blocks that are certified via 'IsCertified'                                                                       *)
(*                                                                         *)
(* - 'hasSupport',                                                                      *)
(*   predicate that checks if a block counts as commited, reltive to the choice of leader block                                                                      *) 
(*                                                                         *)
(* - 'IsCommitingLeaderBlock', *)
(*    an operator that checks wheterh a leader block is a leader block                                                                         *)
(*                                                                         *)
(* -  'IsCommitted(b)',                                                                      *)
(*    the operator for checking if a block is commited *)
(***************************************************************************)

\* the relation of direct links in the mempool DAG
linksTo(b, y) ==
  /\ b \in Block
  /\ y \in Block
  /\ \E q \in DOMAIN (b.cq) : getDigest(b.cq[q]) = digest[y]

\* the transitive closure of the (opposite of) 'liksTo'-relation
RECURSIVE isCauseOf(_, _) 
isCauseOf(x, b) == 
  /\ b \in Block
  /\ x \in Block
  /\  \/ linksTo(b, x)
      \/ \E z \in Block : linksTo(b, z) /\ isCauseOf(x, z)

\* the set of blocks that are causes of a block
CausalHistory(b) == { x \in Block : isCauseOf(x,b) }

\* predicate for block certification via 'IsJustifiedCert' (based on msgs)
IsCertified(b) ==
  /\ b \in Block
  /\  \E c \in Certificate : 
     /\ IsJustifiedCert(c) 
     /\ getDigest(c) = digest[b]

CertifiedBlocks == { b \in Block : IsCertified(b) }

hasSupport(b) == 
  /\ b \in Block
  /\ \E W \in WeakQuorum : \E f \in Injection(W, CertifiedBlocks) :
       \A w \in W : linksTo(f[w], b) 

IsCommitingLeaderBlock(b) == 
  /\ b \in Block
  /\ b.rnd \in WaveLengthTimesNat
  /\ ChoiceOfLeaderBlocks[b.rnd] = b.creator
  /\ hasSupport(b)
  /\ IsCertified(b)

IsCommitted(b) ==
  /\ b \in Block
  /\ \/ IsCommitingLeaderBlock(b)
     \/ \E z \in Block : 
        /\ IsCommitingLeaderBlock(z)
        /\ b \in CausalHistory(z)

(***************************************************************************)
(*                         GARBAGE COLLECTION                              *)
(***************************************************************************)

(***************************************************************************)
(* Gargabge collection marks a block as "orphaned", either if it is not    *)
(* and never will be in the causal history of a leader block or if the     *)
(* distance from its commiting leader block is too long where the          *)
(* _commiting leader block_ of a block b is the leader block with the      *)
(* least round number whose causal history contains the block b. *)
(***************************************************************************)
=============================================================================

