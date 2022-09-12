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
(* In Narwhal, [c]lients send transactions to worker machines at all       *)
(* validators.  [N&T].  This would lead possibly lead to duplicate         *)
(* transactions in batches.  "A load balancer ensures transactions data    *)
(* are received by all workers at a similar rate" [N&T].                   *)
(*                                                                         *)
(* Finally, we define *hashes* of batches and *digests* of blocks; in this *)
(* way, we get a short term for each of these two entities.                *)
(***************************************************************************)

EXTENDS 
  Integers
  ,
  FiniteSets
  ,
  Functions 
  ,
  Quorums
  ,
  WorkersOfPrimaries
        \*,NaturalsInduction
        \*,WellFoundedInduction

\* For the module "Functions", we rely on the \*
\*`^\href{https://tinyurl.com/2ybvzsrc}{Community Module.}^'

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

CONSTANT
  \* @type: Set(BATCH);
  Batch

\* Assume there are some batches (for the purpose of liveness)
ASSUME Batch # {}

\* The following seems odd if you identify types and sets 
\* of valid batches. So, BATCH is more general than just batches
CONSTANT
  \* @type: BATCH;
  noBatch

ASSUME noBatchAssumption == noBatch \notin Batch

(***************************************************************************)
(* For the purposes of formal verification, hash functions need to be      *)
(* treated in a peculiar manner, for the simple reason that hash           *)
(* collisions are not strictly impossible.                                 *)
(***************************************************************************)
       
\* The set of hashes of any possible batch is the range of "hash".

\* @typeAlias: batchHash = { batch : BATCH };
\* @type: Set($batchHash);
BatchHash == [ batch : Batch ]

\* The following fct. "hash" is convenient to model hash functions.

\* @type: BATCH -> $batchHash;
hash[b \in Batch ] == [batch |-> b] 

\* LEMMA hash \in Bijection(Batch, BatchHash) \* NTH

-----------------------------------------------------------------------------
(***************************************************************************)
(*                       NEW DATA STRUCTURES                               *)
(***************************************************************************)


(*
Block digests serve to identify blocks
without including the whole block information. 
They can be thought of as pointers to blocks.
In the TLA-spec, "BlockDigest" will encode this idea, 
exploithing the fact, that we have a message set
of all messages that have been sent by any validator;
the type alias is `blockDigest`. 

IMPORTANT

- This is an encoding for ideal hashes (if correct).
- For correctness, we have to ensure that, indeed, BlockDigest(b)
  * either identifies a unique block or
  * none (of interest, as not sent by any Byzantine validatar). 


The generation/extraction of blockdigest will be much later,
after the details about the sent messages. 
*)

\* @typeAlias: blockDigest = {
\*   creator: BYZ_VAL 
\*   , 
\*   rnd:     Int
\*   , 
\*   nonce:   Int    
\*};

(* BlockDigest is a first approximation of *)
\* @type: Set($blockDigest);
BlockDigestType == [
    \* the creator of a block
    creator: ByzValidator
    ,               
    \* the round number of the block
    rnd:     Nat
    ,               
    \* a nonce, to keep track of spurious blocks beyond the first
    nonce:   Nat    
]

-------------------------------------------------------------------------- 

(***************************************************************************)
(* "If a block is valid, the other validators store it and acknowledge it  *)
(* by signing its _block digest_, _round number_, and _creator’s           *)
(* identity_." [N&T]                                                       *)
(***************************************************************************)

(*
In Doris, we deviate from the above/ [N&T].

- batch hashes are not acknowledged indivitually, but, instead
- batch hashes are acknowledged together with a whole block (header)
*)

(***************************************************************************)
(* In most cases, the signature will not be the creator's, but it could be.*)
(*                                                                         *)
(* We define the set "Ack" as the set of all block acknowledgements,   *)
(* which are in particular signed by validators.  A correct validator has  *)
(* to store the block (or enough erasure coding segments) for later        *)
(* retrieval (until garbage collection / execution).                      *)
(***************************************************************************)

\* "ack", the type of block acknowledgements 
\* @typeAlias: ack = {
\*    digest : $blockDigest,
\*    sig : BYZ_VAL
\* };

\* @type: Set($ack);
AckType == [
  digest : BlockDigestType, \* the digest of the acknowledged block
  sig :    ByzValidator \* the the acknowledging signature
]

-----------------------------------------------------------------------------

(***************************************************************************)
(* "Once the creator gets 2f + 1 distinct acknowledgments for a block, it  *)
(* combines them into a certificate of block availability, that includes   *)
(* the block digest, current round, and creator identity." [N&T]           *)
(*                                                                         *)
(* We separate out the presence of >= "2f + 1 distinct acknowledgments"    *)
(* and make explicit that they talk about the same block digest.           *)
(***************************************************************************)

\* the "Type" of ack quorums
\* @type: Set(BYZ_VAL -> $blockDigest);
AckQuorumType == 
  UNION {[Q -> BlockDigestType] : Q \in ByzQuorum \cup {{}} } 

\* LEMMA \A ax \in AckQuorumType : IsInjective(ax) \* NTH

(***************************************************************************)
(* An AckQuorums are certificates of availability (CoA) for a block.  We thus*)
(* define an alias and provide commodity functions for reading the fields  *)
(* of the contained acknowledgments, which must all agree on the digest,   *)
(* round, and creator.                                                      *)
(***************************************************************************)

Certificate == AckQuorumType
\* CoA == CertificateOfAvailability

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
(* We plan to allow for additional weak links in the sense of DAG-rider    *)
(* [DAG-R].   (coming soon ™) *)
(***************************************************************************)



\* @type: Set($batchHash);
SomeHx == BatchHash

\* @typeAlias: block = {
\*    creator : BYZ_VAL,            
\*    rnd :     Int,                     
\*    bhxs :    $batchHash,                  
\*    cq :      BYZ_VAL -> $blockDigest,
\*    wl :      BYZ_VAL -> $blockDigest 
\* };


\* @type: Set($block);
BlockType == [ 
  creator : ByzValidator, \* the block proposer \& signer
  rnd :     Nat, \* the round of the block proposal
  bhxs :    SomeHx, \* the batch hashes of the block
  cq :      Certificate, \* a CoA-quorum 
  wl :      [{} -> BlockDigestType] \* weak links (coming soon ™)
]

====    ← “Progress Bar END”


BlockStructure ==
   { b \in BlockStructureType :
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
BlockMessage == [type : {"block"}, block: Block, creator : ByzValidator, nonce: Nat]

\* commmitment "by" a validator to have stored a block 
BlockAckMessage == [type : {"block-ack"}, ack : Ack, by : ByzValidator]

\* creator aggregates quorum of acks into a certificate and broadcasts it
CertMessage == [type : {"cert"}, cert : Certificate, creator : ByzValidator]

\* a commit message commits a leader block, sent by consensus layer
CommitMessage == [type : {"commit"}, b : Block]

\* All messages that can be send between workers/primaries/validators ..
\* .. and the consensus engine
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
    \* a commit message commits a leader block, sent by consensus layer
    \cup
    CommitMessage
    
    
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
     /\ b \in batchPool[w] \* check that I am actually responsible
     \* postcondition
     \* add hash to primary's set of next hashes
     /\ nextHx' = [nextHx EXCEPT ![w.val] = @ \cup {hash[b]}]
     \* worker 'w' *transfers* the batch (hash) to the primary
     \* .. preventing the "same" batch to be included in multiple blocks
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
     /\ b.bhxs \subseteq nextHx[v]
     /\ (v \in Validator => b.bhxs = nextHx[v]) 
     /\ b.cq = noCert
     /\ b.wl = noLinks
     \* postcondition
     \* send the block
     /\ Send([type |-> "block", block |-> b, creator |-> v])
     \* empty v's nextHx (for validators)
     /\ (v \in Validator => nextHx' = [nextHx EXCEPT ![v] = {} ])
     \* Byzantine validators might drop some hashes, typically none 
     /\ \E X \in SUBSET nextHx[v] : 
          nextHx' = [nextHx EXCEPT ![v] = @ \ X ]
  /\ UNCHANGED <<rndOf, batchPool, storedHx, storedBlx>>

\* A certificate c : Q -> Ack is _justified_ if all "block-ack"s were sent
IsJustifiedCert(c) ==
  /\ c \in Certificate  \* aka AckQuorum
  /\ \A a \in Range(c) : \E m \in Message :
     /\ m.type = "block-ack" \*  block-ack 
     /\ m.ack = a \* the ack was sent
\* LEMMA "if block-ack sent, everything else necessary was sent" NTH!

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
  \* TODO: adapt to byzantine validatrs

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

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          DAG STRUCTURE                                  *)
(***************************************************************************)

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
(* - 'CertifiedBlocks',                                                    *)
(*   the set of all blocks that are certified via 'IsCertified'            *)
(*                                                                         *)
(***************************************************************************)


\* the relation of direct links in the mempool DAG b ~> y
linksTo(b, y) ==
  \* type checks
  /\ b \in Block
  /\ y \in Block
  \* the certificate list of block b contains digest of y
  /\ \E c \in Range(b.cq) : getDigest(c) = digest[y]

\* predicate for block certification via 'IsJustifiedCert' (based on msgs)
IsCertified(b) ==
  \* type check
  /\ b \in Block
  \* there is some certificate
  /\  \E c \in Certificate : 
     \* that was actually sent 
     /\ IsJustifiedCert(c) 
     \* and witnesses that b is available
     /\ getDigest(c) = digest[b]

\* the set of all blocks that are certified via 'IsCertified'
CertifiedBlocks == { b \in Block : IsCertified(b) }


\* the transitive closure of the (opposite of) 'liksTo'-relation
isCauseOf(x, y) == 
  \* a "recursive" causality test, only local for the moment
  LET isCauseTest[n \in Nat] == 
    [ c \in Block |->
      [ b \in Block |-> 
        CASE n = 0 -> FALSE
          [] n = 1 -> linksTo(b,c)
          [] OTHER -> \E z \in Block : 
                         /\ linksTo(b, z) 
                         /\ isCauseTest[n-1][c][z]
      ]
    ]
  IN 
    \* type checks
    /\ x \in Block
    /\ y \in Block
    \* existence of a link chain
    /\ \E n \in Nat : isCauseTest[n][x][y]

\* the set of blocks that are causes of a block
CausalHistory(b) == { x \in Block : isCauseOf(x,b) }

-----------------------------------------------------------------------------

(***************************************************************************)
(*                      CONSENSUS ABSTRACTION                              *)
(***************************************************************************)

(***************************************************************************)
(* Instead of the (pseudo-)random leader election of Tusk [N&T], we model  *)
(* a non-deterministic choice of leader blocks in each _k_-th round for a  *)
(* globally fixed _k_ > 0 with the additional guarantee that the block is  *)
(* referenced by at least a weak quorum.                                   *)
(***************************************************************************)

\* predicate that checks if a block counts as commitable
hasSupport(b) == 
  \* type check 
  /\ b \in Block
  /\ \E W \in WeakQuorum : \E f \in Injection(W, CertifiedBlocks) :
       \A w \in W : linksTo(f[w], b) 


\* the constant number of rounds between each leader block commitment
CONSTANT WaveLength ASSUME WaveLengthAssumption ==
  /\ WaveLength \in Nat
  /\ WaveLength >= 1

WaveLengthTimesNat == { n \in Nat : \E i \in Nat : n = WaveLength * i }
  
\*ASSUME ChoiceOfLeaderBlocks ==
\*  \* a choice of leader blocks: at round n, block created by LB[n]
\*  /\ LeaderBlock \in [WaveLengthTimesNat -> ByzValidator]
\*  \* and this choice is (weakly) fair
\*  /\ \A n \in WaveLengthTimesNat : \A v \in ByzValidator :
\*        \E m \in WaveLengthTimesNat : m > n /\ LeaderBlock[m] = v 


CommitBlock(b) == 
  \* type check
  /\ b \in Block
  \* precondition(s)
  /\ b.rnd \in WaveLengthTimesNat
  \* not yet committed any block at the round
  /\ ~\E m \in msgs : m.type = "commit" /\ m.block.rnd = b.rnd
  \* enough support
  /\ Send([type |-> "commit", block |-> b])
  /\ UNCHANGED <<rndOf, batchPool, nextHx, storedHx, storedBlx>>

-----------------------------------------------------------------------------

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
(***************************************************************************)


\* checks whether a leader block is a leader block
IsCommitingLeaderBlock(b) == 
  \* type check
  /\ b \in Block
  \* commit message was sent (by consensus layer)
  /\ [type |-> "commit", block |-> b] \in msgs \* ChoiceOfLeaderBlocks[b.rnd] = b.creator
  

\* checking if a block is commited
IsCommitted(b) ==
  /\ b \in Block
  /\ \/ IsCommitingLeaderBlock(b)
     \/ \E z \in Block : 
        /\ IsCommitingLeaderBlock(z)
        /\ b \in CausalHistory(z)

-----------------------------------------------------------------------------

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

