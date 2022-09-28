---------------------------- MODULE Doris -----------------------------------


(***************************************************************************)
(* Doris is a DAG mempool similar to the Narwhal mempool with Tusk playing *)
(* the role of consensus as proposed by Danezis, Kokoris Kogias, Sonnino,  *)
(* and Spiegelman in their                                                 *)
(* `^\href{https://arxiv.org/abs/2105.11827}{paper.}^' Further inspiration *)
(* is taken from `^\href{https://arxiv.org/abs/2102.08325}{DAG-rider,}^',  *)
(* a precursor to Narwhal.                                                 *)
(* (We shall refer to these papers as [N&T] and [DAG-R], respectively.)    *)
(*                                                                         *)
(* The following differences deserve mention.                              *)
(*                                                                         *)
(* ① In Narwhal, [c]lients send transactions to worker machines at all     *)
(* validators.  [N&T].  This would lead possibly to duplicate              *)
(* transactions in batches.  "A load balancer ensures transactions data    *)
(* are received by all workers at a similar rate" [N&T].                   *)
(*                                                                         *)
(* ② We use some minimal amout of weak links (see [DAG-R]).                *)
(***************************************************************************)

EXTENDS 
  Integers
  ,
  FiniteSets
  ,
  SubSingletons
  ,
  Functions 
  ,
  Quorums
  ,
  WorkersOfPrimaries
  , 
  Variants
        \*,NaturalsInduction
        \*,WellFoundedInduction

\* For the module "Functions", we rely on the \*
\*`^\href{https://tinyurl.com/2ybvzsrc}{Community Module.}^'

-----------------------------------------------------------------------------

(***************************************************************************)
(*                         DATA STRUCTURES                                 *)
(***************************************************************************)

(***************************************************************************)
(* We give encodings for blocks and their components, such as *)
(* certificates, block digests, and the like, as used in Narwhal    *)
(* [N&T] and DAG-rider [DAG-R].  We work directly with batches, such that  *)
(* processing individual transactions can be seen as a refinement.         *)
(***************************************************************************)

\* "Batch", the set of batches: elements have type "BATCH" (uninterpreted).

CONSTANT
  \* @type: Set(BATCH);
  Batch

\* Assume there are some batches (for the purpose of liveness)
ASSUME ExistenceOfBatches ==
  Batch # {}

\* The following seems odd if you identify types and sets 
\* of valid batches. So, BATCH is more general than just the batch elements
CONSTANT
  \* @type: BATCH;
  noBatch

ASSUME noBatchAssumption == 
  noBatch \notin Batch

(***************************************************************************)
(* We emulate hash functions on batches by a simple "wrapping" operation.  *)
(* This is for the simple reason that hash                                 *)
(* collisions are not strictly impossible.                                 *)
(***************************************************************************)
       
\* "BatchHash": the set of hashes of any possible batch 

(*
--- batchHash ---
- batch: the hashed Batch
@typeAlias: batchHash = {
    batch : BATCH 
};
*)


\* @type: Set($batchHash);
BatchHash == [ batch : Batch ]

\* The operator "hash" emulates hash functions.

\* @type: BATCH => $batchHash;
hash(b) == [batch |-> b] 

\* LEMMA hash \in Bijection(Batch, BatchHash) \* obvious, NTH

-----------------------------------------------------------------------------
(***************************************************************************)
(*                       NEW DATA STRUCTURES                               *)
(***************************************************************************)

(*
Block digests serve to identify blocks
without including the whole block information, 
emulating perfect hashing. 
"BlockDigest" is the encoding of such block digests, 
exploithing the fact that we have a message set
of all messages that have been sent by any validator;
the type alias is "$blockDigest". 

IMPORTANT

- "BlockDigest"-ing encodes ideal hashes (if correct).
- For correctness, we have to ensure that, indeed, 
  "digest(b)" identifies the block $b$.
*)

(*
--- blockDigest ---
- creator: the creator of the “digested block”

- rnd: the round of the “digested block”

- nonce: numbering the proposed blocks of malicious validators

@typeAlias: blockDigest = {
   creator: BYZ_VAL
   , 
   rnd:     Int
   , 
   nonce:   Int    
};
===
*)

\* @type: Set(Int);
Nonce == Nat

\* @type: Int;
THENONCE == 0 \* fixme later by calculating / keeping track of nonces   

(* BlockDigestType is a first over-approximation of "BlockDigest". *)
\* @type: Set($blockDigest);
BlockDigestType == [
    \* the creator of a block
    creator: ByzValidator
    ,               
    \* the round number of the block
    rnd:     Nat
    ,               
    \* a nonce, keeping track of spurious blocks beyond the first / zeroth
    nonce:   Nat
]



-----------------------------------------------------------------------------

(***************************************************************************)
(* "If a block is valid, the other validators store it and acknowledge it  *)
(* by signing its _block digest_, _round number_, and _creator’s           *)
(* identity_." [N&T]                                                       *)
(***************************************************************************)


(*
In Doris, we deviate from the above/ [N&T].

- batch hashes are not acknowledged indivitually, but, instead
- batch hashes are acknowledged jointly, being only part of a block (header)
*)

(***************************************************************************)
(* In most cases, the signature of a block acknowledgement will *)
(* be from a different validator, i.e., not the creator's. *)
(*                                                                         *)
(* We define the set "Ack" as the set of all block acknowledgements,   *)
(* which are in particular signed by validators.  A correct validator has  *)
(* to store the block (or enough erasure coding segments) for later        *)
(* retrieval (until garbage collection / execution).                      *)
(***************************************************************************)

(* 
--- ack ---
- digest: the digest of the acknowledged block

- sig: the signing validator
===
@typeAlias: ack = {
    digest : $blockDigest,
    sig :    BYZ_VAL
};
*)

\* "AckType" is an over-approximation of the set of all block acks.
\* @type: Set($ack);
AckType == [
  digest : BlockDigestType, \* the digest of the acknowledged block
  sig :    ByzValidator \* the signing validator
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

(*
--- digestFamily ---

“just” an (injective) function from validators to block digests; 
every element of the domain can be taken to be a signer (if needed)

===
@typeAlias: digestFamily = 
  BYZ_VAL -> $blockDigest
;
*)
\* @type: Set($digestFamily);
AckQuorumType == 
  UNION {Injection(Q,BlockDigestType) : Q \in ByzQuorum \cup {{}} } 

\* @type: $digestFamily;
emptyQuorum == CHOOSE f \in Injection({},BlockDigestType) : TRUE

\* @type: $digestFamily;
emptyLinks == emptyQuorum

(***************************************************************************)
(* AckQuorums are certificates of availability (CoA) for a block.  We thus *)
(* define an alias and provide commodity functions for reading the fields  *)
(* of the contained acknowledgments, which must all agree on the digest,   *)
(* round, and creator.                                                     *)
(***************************************************************************)

\* @type: Set($digestFamily);
CertificateOption == AckQuorumType

\* @type: Set($digestFamily);
Certificate == CertificateOption \ Injection({},BlockDigestType)

(***************************************************************************)
(* According to [N&T], a valid block must                                  *)
(*                                                                         *)
(* 1.  contain a valid signature from its creator;                         *)
(*                                                                         *)
(* 2.  be at the local round r of the ByzValidator checking it;            *)
(*                                                                         *)
(* 3.  be at round 1 (genesis), or contain certificates for                *)
(*     at least 2f + 1 blocks of round r-1;                                *)
(*                                                                         *)
(* 4.  be the first one received from the creator for round r .            *)
(*                                                                         *)
(* We plan to allow for additional weak links in the sense of DAG-rider    *)
(* [DAG-R].   (coming soon ™) *)
(***************************************************************************)

CONSTANT
  \* the maximal number of batches in a block
  \* @type: Int;
  BatchMax 

\* ASSUME BatchMax == 1  \* if in doubt

\* @type: Set(Set($batchHash));
BatchMaxBoundedBatchSubsets == 
  IF BatchMax < 0 
  THEN {}
  ELSE {{}} \cup { Range(f) : f \in [ 1..BatchMax -> BatchHash ] }


\* @type: Set(Set($batchHash));
SomeHxs == BatchMaxBoundedBatchSubsets

(*
--- block ---

- creator : the block's creator

- rnd     : the round in which the block is proposed

- bhxs    : the set of batch hashes in the block

- cq      : the certificate quroum    

- wl      : the weak links
===

@typeAlias: block = {
    creator : BYZ_VAL,            
    rnd :     Int,                     
    bhxs :    Set($batchHash),                  
    cq :      $digestFamily,
    wl :      $digestFamily
};
*)

\* @type: Set($block);
BlockType == [ 
  creator : ByzValidator, \* the block proposer \& signer
  rnd :     Nat, \* the round of the block proposal
  bhxs :    SomeHxs, \* the batch hashes of the block
  cq :      CertificateOption, \* a CoA (unless genesis block)
  wl :      [{} -> BlockDigestType] \* weak links (coming soon ™)
]

\* @type: $block => $blockDigest;
digest(block) == 
  LET
    \* @type: $block;
    b == block
    \* @type: BYZ_VAL;
    c == b.creator
    \* @type: Int;
    i == b.rnd
    \* @type: Int;
    n == THENONCE
  IN
    [creator |-> c, rnd |-> i, nonce |-> n]

\* end of "DATA STRUCTURES"
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
(* - "Batch" broadcast a batch, **from** a worker (to workers of the same  *)
(*   index).                                                               *)
(*                                                                         *)
(* - "Block" a block creator broadcasts a new block (header)               *)
(*                                                                         *)
(* - "Ack" acknowledgment *by* a Validator, having block availble          *)
(*                                                                         *)
(* - "Cert" broadcasting a (block) certificate (by a creator)              *)
(*                                                                         *)
(* We call a "mirror worker" a worker of the same index at a different     *)
(* validator.  We assume that clients send a transaction/batch             *)
(* only to one validator at a time, and only if the transaction gets       *)
(* orphaned, inclusion via a weak link is a possibility; *)
(* we "abuse" weak links for an additional link to the last proposed block.*)
(*  *)
(* Correct validators only     *)
(* make blocks with batches arriving at their workers in the first place.  *)
(*                                                                         *)
(* We abstract away all worker-primary communication "inside" validators;  *)
(* we have remote direct memory access (RDMA) in mind. *)
(* Further    *)
(* refinement could be applied if a message passing architecture was       *)
(* desired.                                                                *)
(***************************************************************************)

VARIABLE
  (*
   --- msg ---
   
   - Batch: broadcast a batch 

     - bactch: the batch being broadcast

     - from: the sending working
  
   «auto-complete plz»
  
   ===
   @typeAlias:msg = 
     Batch(     {batch : BATCH, from : $worker}                     )|
     Block(     {block: $block, creator : BYZ_VAL, nonce: Int}      )| 
     Ack(       {ack : $ack, by : BYZ_VAL}                          )| 
     Cert(      {digest : $blockDigest, creator : BYZ_VAL} )|
     Commit(    {digest : $blockDigest }                                 )|
     Executed(  {digest : $blockDigest }                                 )|
     Abort(NIL) ; 
  *)
  \* @type: Set($msg);
  msgs

\* Batch():
\* broadcast a fresh "batch" from a "worker" (to mirror workers)
\* @type: (BATCH, $worker) => $msg;
batchMsg(b, w) == 
  Variant("Batch", [ batch |-> b, from |-> w])

\* Block():
\* creator produces a block and broadcasts it
\* @type: ($block, BYZ_VAL, Int) => $msg;
blockMsg(b, c, n) == 
  Variant("Block", [block |-> b, creator |-> c, nonce |-> n])

\* Ack():
\* commmitment "by" a validator to have stored a block 
\* @type: ($ack, BYZ_VAL) => $msg;
ackMsg(a, v) == 
  Variant("Ack", [ack |-> a, by |-> v])

\* creator aggregates quorum of acks into a certificate and broadcasts it
\* @type: ($blockDigest, BYZ_VAL) => $msg;
certMsg(d, c) == 
  Variant("Cert", [digest |-> d, creator |-> c]) 

\* Commit():
\* a commit message commits a leader block (sent by the consensus layer)
\* @type: ($blockDigest) => $msg;
commitMsg(d) ==
  Variant("Commit", [digest |-> d])

\* the initial setting for the set of messages
msgsINIT ==
  msgs = {}

\* end of "MESSAGE STRUCTURE"

    
-----------------------------------------------------------------------------

(*-------------------------------------------------------------------------*)
(*                           LOCAL STATE                                   *)
(*-------------------------------------------------------------------------*)

(***************************************************************************)
(* The local state of validators and workers at validators is              *)
(*                                                                         *)
(* ① a local round number (corresponding a layer of DAG mempool);         *)
(*                                                                         *)
(* ② a worker specific pool of received client batches;                   *)
(*                                                                         *)
(* ③ a pool of batch hashes to be included in the next block;             *)
(*                                                                         *)
(* ④ a local storage for (hashes of) batches;                             *)
(*                                                                         *)
(* ⑤ a local storage for (digests of) block headers                        *)
(***************************************************************************)


\* Each ByzValidator has a local round number (initially 1), cf. ①
VARIABLE
  \* @type: BYZ_VAL -> Int;
  rndOf 

\* "assert" INIT => \A v \in ByzValidator : rndOf[v] = 1
rndOfINIT ==   
   \A v \in ByzValidator : rndOf[v] = 1

\* Workers' local pools of batched requests (initially {}), cf. ②
VARIABLE
  \* @type: $worker -> Set(BATCH);
  batchPool 

\* "assert" INIT => \A w \in Worker : batchPool[w] = {}
batchPoolINIT == 
  \A w \in Worker : batchPool[w] = {}

\* Primaries' pools of hashes for the next block (initially {}), cf. ③
VARIABLE
  \* @type: BYZ_VAL -> Set($batchHash);
  nextHx

\* "assert" INIT => \A p \in Primary : nextHx[p] = {}
nextHxINIT == 
  \A p \in Primary : nextHx[p] = {}

\* Primaries' stored batch hashes for availability (initially {}), cf. ④
VARIABLE
  \* @type: BYZ_VAL -> Set($batchHash);
  storedHx

\* "assert" INIT => \A v \in ByzValidator : storedHx[v] = {}
storedHxINIT == 
  \A v \in ByzValidator : storedHx[v] = {}

\* Each ByzValidator has storage for blocks (initially {}), cf. ⑤ 
\* with the following two different stages of knowing a block
AVL == FALSE 
COA == TRUE
VARIABLE
  \* @type: BYZ_VAL -> Set(<<$block, Bool>>);
  storedBlx


    

\* "assert" INIT => \A v \in ByzValidator : storedBlx[v] = {}
storedBlxINIT == 
  \A v \in ByzValidator : storedBlx[v] = {}

\* The combined INIT-predicate concerning the local state
\* @type: Bool;
LocalStateINIT ==
  /\ rndOfINIT \* ①
  /\ batchPoolINIT \* ②
  /\ nextHxINIT \* ③ 
  /\ storedHxINIT \* ④ 
  /\ storedBlxINIT  \* ⑤ 

\* end of "LOCAL STATE"

-----------------------------------------------------------------------------

vars == <<msgs, rndOf, batchPool, nextHx, storedHx, storedBlx>>
  (*************************************************************************)
  (* It is convenient to have a shorthand for all variables in a spec.     *)
  (*************************************************************************)

allBUTmsgs == 
  <<rndOf, batchPool, nextHx, storedHx, storedBlx>>
    
allBUTmsgsNbatchPoolNnextHxNstoredHx == 
  <<rndOf, storedBlx>>

allBUTbatchPoolNnextHx ==
  <<msgs, rndOf, storedHx, storedBlx>>

allBUTmsgsNnextHx ==  
  <<rndOf, batchPool, storedHx, storedBlx>>

allBUTstoredHx == 
  <<msgs, rndOf, batchPool, nextHx, storedBlx>>

allBUTmsgsNstoredBlx == 
  <<rndOf, batchPool, nextHx, storedHx>>    

allBUTrndOf == 
  <<msgs, batchPool, nextHx, storedHx, storedBlx>>

\* @type: Int;
maxRound == 
  CHOOSE n \in Range(rndOf) : n+1 \notin Range(rndOf)

\* @type: Set($blockDigest);
BlockDigest == 
  { d \in BlockDigestType : 
            /\ d.rnd <= maxRound+1
            /\ TRUE
  }

\* @type: Set($block);
Block ==
    { b \in BlockType : 
            /\ b.rnd <= maxRound+1
            /\ \E n \in Nonce : 
                    blockMsg(b, b.creator, n) \in msgs
    }

\* @type: (BYZ_VAL, Int) => Set($block);
proposedBlocksByValidatorInRound(validator, r) == 
  LET
    c == validator
  IN
  { b \in Block : 
      /\ b.rnd = r
      /\ \E n \in Nonce : 
            LET
              \* @type: $msg;
              m == Variant("Block", [block |-> b, creator |-> c, nonce |-> n])
            IN
              m \in msgs
  }
  
\* @type: (BYZ_VAL) => Set($block);
proposedBlocksByValidator(validator) == 
  LET
    c == validator
  IN
  { b \in Block : 
       \E n \in Nonce : 
          LET
            \* @type: $msg;
            m == Variant("Block", [block |-> b, creator |-> c, nonce |-> n])
          IN
            m \in msgs
  }

\* @type: Set($block);
proposedBlocks == 
  UNION { proposedBlocksByValidator(c) : c \in ByzValidator } 

\* @type: (Int) => Set($block);
proposedBlocksInRound(r) == 
   { b \in proposedBlocks : b.rnd = r }

\* @type: Set($msg);
allAckMsgs ==
  { m \in msgs : VariantTag(m) = "Ack" }

\* @type: Set($ack);
allAcks ==
  { VariantGetUnsafe("Ack", m).ack : m \in allAckMsgs}    


\* @type: ($blockDigest) => Set($ack);
acksOfDigest(dgst) == 
  LET
    \* the digest of interest
    \* @type: $blockDigest;
    d == dgst
  IN
    \* the set of 
    {a \in allAcks : a.digest = d}

    
-----------------------------------------------------------------------------
(***************************************************************************)
(*                             ACTIONS                                     *)
(***************************************************************************)


(***************************************************************************)
(* We will specify the following actions.                                  *)
(*                                                                         *)
(* - [NOT Batch arrival (no message, combined with 'BatchBC')]:            *)
(*                                                                         *)
(*   A new **batch** arrives at a **worker** and is included               *)
(*   into the worker's batchPool. The arriving batch might already be      *)
(*   "known" and/or been submitted to other workers, e.g., if clients      *)
(*   "misbehave". (Recall that, ideally, clients submit their         *)
(*   transactions to only one worker.) *)
(*   We combine batch arrival with broadCasting a batch. *)
(*   (The action of batch arrival is strictly local to the worker.)        *)
(*                                                                         *)
(* - Batch broadcast "BatchBC" (message "Batch"):                          *)
(*                                                                         *)
(*   A worker broadcasts the                                               *)
(*   batch, stores it, and forwards it to its primary for block inclusion. *)
(*                                                                         *)
(* - Batch receive, store, hash "StoreBatch" (NO message ):    *)
(*                                                                         *)
(*   Reception of a batch, storing and hashing such that later blocks can  *)
(*   be validated and acknowledged by the primary.                         *)
(*                                                                         *)
(* - Block production and broadcast "BlockBC" (message "Block"):           *)
(*                                                                         *)
(*   A primary builds a block from enough certificates of availability     *)
(*   and batch hashes provided by its workers and broadcasts the           *)
(*   block. "One primary integrates references to [batches] in Mempool     *)
(*   primary blocks."  [N&T]                                               *)
(*                                                                         *)
(* - Block acknowledgement "Ack" (message "Ack")                           *)
(*                                                                         *)
(*   Receive a block, check its validity, store it, Ack()acknowledge it.   *)
(*                                                                         *)
(* - Certificate broadcats "CertBC" (message "Cert")                       *)
(*                                                                         *)
(*   Take an acknowledgement quorum of a proposed block, aggregate it     *)
(*   into a ceritificate, and broadcast the certificate.                   *)
(*                                                                         *)
(* - Advancing the local round 'AdvanceRound' (NO message)                 *)
(*                                                                         *)
(*   A validator moves to the next round,  *)
(*   after receiving a quorum of block certificates. *)
(***************************************************************************)


(***************************************************************************)
(* We define the subactions of the next-state actions.  We begin by        *)
(* defining an action that will be used in those subactions.  The action   *)
(* Send(m) asserts that message m is added to the set msgs.                *)
(*                                                                         *)
(* taken from `^\href{https://tinyurl.com/2dyuzs6y}{Paxos.tla}^'           *)
(***************************************************************************)

\* SUB-ACTION "Send":
\*   sending a message will only be used as "part of" a "full" action
\* ... and thus no UNCHANGED
\* 
\* ¡msgs
\* @type: ($msg) => Bool; 
Send(message) == 
  LET
    \* type: $msg;
    m == message
  IN
  msgs' = msgs \cup {m} 

\* ACTION "BatchBC":
\*   broadcasting a new batch, triggerd by “incoming” request(s)
\*   and putting it in the hash storage and primary's pool of next hashes
\* 
\* ¡msgs, ¡batchPool, ¡nextHx, ¡storedHx
\* @type: (BATCH, $worker) => Bool; 
BatchBC(batch, worker) ==
  LET
    \* @type: BATCH;
    b == batch 
    \* @type: $worker;
    w == worker
    \* @type: BYZ_VAL;
    p == worker.val
  IN
  \* "trivial" pre-condition (checking the typing)
  /\ b \in Batch
  /\ w \in Worker
  \* post-condition: add the batch the the batch pool of w
  /\ batchPool' = \* ¡batchPool
       [batchPool EXCEPT ![w] = @ \cup {b}] 
  /\ nextHx' = \* ¡nextHx
       [nextHx EXCEPT ![p] = @ \cup {hash(b)}] 
  /\ storedHx' = \* ¡storedHx
       [storedHx EXCEPT ![p] = @ \cup {hash(b)}] 
  \* broadcast the batch 
  /\ Send(batchMsg(b,w)) \* ¡msgs
  /\ UNCHANGED allBUTmsgsNbatchPoolNnextHxNstoredHx

\* ACTION "StoreBatch": 
\*   store a received Batch 
\*
\* ¡storedHx, 
\* @type: (BATCH, $worker) => Bool;
StoreBatch(batch, worker) ==
  LET
    \* @type: BATCH;
    b == batch 
    \* @type: $worker;
    w == worker
    \* @type: BYZ_VAL;
    p == worker.val
  IN
  \* "typing"
  /\ b \in Batch
  /\ w \in Worker
  \* pre-condition:
  \* some other worker has sent this batch
  /\ \E ww \in Worker \ {w}: batchMsg(b,ww) \in msgs
  \* post-condition: add the batch hash to the set of known hashes
  /\ storedHx' = [storedHx EXCEPT ![p] = @ \cup {hash(b)}]
  \* we elide the details of storing the actual batch for availability
  /\ UNCHANGED allBUTstoredHx \* end of action StoreBatch

\* @type: (BYZ_VAL, Int) => Set($block);
currentBlocksProduced(creator, nonce) == 
  LET
    \* @type: BYZ_VAL;
    c == creator
    \* @type: Int;
    n == nonce
    \* @type: Set($msg);
    allBroadcastMessages == 
      { m \in msgs : VariantTag(m) = "Block" } 
  IN LET
    \* @type: Set({block: $block, creator : BYZ_VAL, nonce: Int});
    data == 
      { VariantGetUnsafe("Block", m) : m \in allBroadcastMessages } 
  IN LET
    \* @type: Set({block: $block, creator : BYZ_VAL, nonce: Int});
    filteredData == 
      { x \in data : /\ x.creator = c
                     /\ x.nonce = n
      }
  IN { x.block : x \in filteredData }

\* "fetchBlock" yields a block (or **should** raise an error)---
\* based on the messages sent (i.e., present in the variable "msg")
\* @type: $blockDigest => $block;
fetchBlock(dgst) == 
  LET
    \* @type: Set($block);
    allPossibleBlocks == currentBlocksProduced(dgst.creator, dgst.nonce)
  IN LET
    \* @type: Set($block);
    candidates == {c \in allPossibleBlocks : c.rnd = dgst.rnd}
  IN
    extract(candidates)

\* ACTION GenesisBlockBC [instance of BlockBC]:
\*  a validator produces a genesis block and broadcasts it
\* @typing: BYZ_VAL => Bool;
GenesisBlockBC(validator) ==
  LET
    \* @type: BYZ_VAL;
    v == validator
  IN
  \* pre-condition
  /\ rndOf[v] = 1 \* validator has local round 1
  \* 
  /\ \E b \in BlockType : \* "construct" a block of the desired shape
     /\ b.creator = v
     /\ b.rnd = 1
     /\ b.bhxs = nextHx[v] 
     /\ b.cq = emptyQuorum
     /\ b.wl = emptyLinks
     \* post-condition
     \* send the block
     /\ Send(blockMsg(b, v, THENONCE)) \* ¡msgs
     \* empty v's nextHx (for validators)
     /\ nextHx' = \* ¡nextHx
          [nextHx EXCEPT ![v] = {}] 
  /\ UNCHANGED allBUTmsgsNnextHx \* end of action "GenesisBlockBC"


\* predicate for checking the storage of hashes at a validator
\* @type: ($block, BYZ_VAL) => Bool;
hasBlockHashesStored(block, val) ==
 \* we know all batches
 \A h \in block.bhxs : h \in storedHx[val]

\* predicate for checking the storage of blocks of digests
\* @type: ($digestFamily, BYZ_VAL) => Bool;
checkCertificatesOfAvailability(certificate, validator) ==
  LET
    \* @type: $digestFamily;
    c == certificate
    \* @type: BYZ_VAL;
    v == validator
  IN  
  \A d \in Range(c) : 
       LET
         \* @type: $block;
         b == fetchBlock(d)
       IN  
         \* block is known certified 
         << b, COA >> \in storedBlx[v]  

\* @type: ($block, BYZ_VAL) => Bool;
validBlock(block, validator) == 
  LET 
    \* the block in question
    \* @type: $block;
    b == block
    \* the validator checking the validity
    \* @type: BYZ_VAL;
    v == validator 
  IN
     \* the round must be a positive natural number
  /\ b.rnd > 0 \*
     \* batch hashes stored (always needed)
  /\ hasBlockHashesStored(b, v)
     \* and block references stored
  /\ checkCertificatesOfAvailability(b.cq, v)
  /\ DOMAIN b.wl = {} 


\* ACTION Ack:
\*   Receive a block, check its validity, store it, Ack()acknowledge it.
\*
\* ¡msgs, ¡storedBlx
\* @type: (BYZ_VAL, $block) => Bool;
Ack(validator, block) == 
  LET
    \* @type: BYZ_VAL;
    v == validator
    \* @type: $block; 
    b == block 
  IN LET
    \* @type: $blockDigest;
    d == digest(b)
  IN LET
    \* @type: $ack;
    a == [digest |-> d, sig |-> v]
  IN
  \* typing of v (for TLC)
  /\ v \in ByzValidator
  \* pre-condition:
     \* check that block b was proposed
  /\ b \in proposedBlocks 
     \* check that b is valid (according to v)
  /\ validBlock(b, v) \* 
     \* check that b has neither available (nor certified)
  /\ << b, AVL >> \notin storedBlx[v]
  /\ << b, COA >> \notin storedBlx[v]  
  \* post-condition:
     \* send the acknowledgement 
  /\ Send(ackMsg(a, v)) \* ¡msgs
     \* store the block as "available" (but not certified)
  /\ storedBlx' = \* ¡storedBlx
       [storedBlx EXCEPT ![v] = @ \cup {<<b, AVL>>}] 
  /\ UNCHANGED allBUTmsgsNstoredBlx

\* ACTION CertBC:
\*   broadcast a certificate of availability of (the digest of) a block 
\* @type: ($blockDigest) => Bool;
CertBC(dgst) ==
  LET
    \* the block digest to be certified
    \* @type: $blockDigest;
    d == dgst
  IN
  \* typing 
  /\ dgst \in BlockDigest
  \* pre-condition
  /\ \E Q \in ByzQuorum : 
        LET
          theAcks == 
            {a \in acksOfDigest(d) : a.sig \in Q }
        IN
        /\ Q = { a.sig : a \in theAcks }
     \* post-condition
        /\ \* send the certificate
           LET
             \* @type: BYZ_VAL;
             theCreator == d.creator
           IN Send(certMsg(d, theCreator)) \* ¡msgs
           \* update *all* storages, s.t., the block is certified
        /\ LET 
             b == fetchBlock(d)
           IN storedBlx' = \* ¡storedBlx
                [v \in ByzValidator |-> storedBlx[v] \cup {<< b, COA >>}] 
  /\ UNCHANGED allBUTmsgsNstoredBlx

\* @type: (BYZ_VAL, Int) => Set($block);
preceedingBlocks(v, r) == 
      { b \in Block : 
          /\ b.rnd = r - 1
          /\ << b, COA >> \in storedBlx[v]
      }


\* ACTION AfterGenesisBlockBC [instance of BlockBC]:
\*  a validator produces a block, after genesis, and broadcasts it
\* @typing: BYZ_VAL => Bool;
AfterGenesisBlockBC(validator) ==
  LET
    \* @type: BYZ_VAL;
    v == validator   
    r == rndOf[v]
  IN LET
    \* @type: Set(BYZ_VAL);
    certifiedProposers == 
      { b.creator : b \in preceedingBlocks(v,r) }
  IN
  \* type check:
     \* it's a validator
  /\ v \in ByzValidator
  \* pre-condition
     \* validator has advanced to a non-genesis round
  /\ rndOf[v] > 1 
     \* no block proposed yet
  /\ proposedBlocksByValidatorInRound(v, rndOf[v]) = {}
     \* there exists a quorum of certified block in the previous round
  /\ \E Q \in ByzQuorum \cap SUBSET certifiedProposers : 
       LET 
         \* @type: Set($block);
         relevantBlocksByQ == 
           { b \in preceedingBlocks(v,r) : b.creator \in Q }
       IN LET
         \* @type: $block;
         theBlock == [
             creator |-> v, 
             rnd |-> rndOf[v],
             bhxs |-> nextHx[v],
             cq |-> [q \in Q |-> 
                       digest(CHOOSE b \in preceedingBlocks(v,r) : b.creator = q)
                    ], 
             wl |-> emptyLinks
           ]
       IN 
       \* post-condition
           \* send the block
         /\ Send(blockMsg(theBlock, v, THENONCE)) \* ¡msgs
         \* empty v's nextHx (for validators)
         /\ nextHx' = \* ¡nextHx
              [nextHx EXCEPT ![v] = {}] 
  /\ UNCHANGED allBUTmsgsNnextHx \* end of action "GenesisBlockBC"

BlockBC(validator) == 
  \/ GenesisBlockBC(validator)
  \/ AfterGenesisBlockBC(validator)
    
\* AdvanceRound:
\*   correct validators can increment their local round number 
\*   as soon as they have a quorum of CoA for blocks of the previous round 
\* @type: (BYZ_VAL) => Bool;
AdvanceRound(validator) == 
  LET
    \* @type: Set(BYZ_VAL);
    X == 
      {b.creator : b \in preceedingBlocks(validator, rndOf[validator]+1)}
  IN 
  \* pre-condition:
      \* enough block available
  /\ \E Q \in ByzQuorum \cap SUBSET X : TRUE
  \* post-condition
  /\ rndOf' = [rndOf EXCEPT ![validator] = @ + 1]
  /\ UNCHANGED allBUTrndOf

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          DAG STRUCTURE                                  *)
(***************************************************************************)

(* We define several auxiliary predicates .                                *)
(*                                                                         *)
(* - 'linksTo',                                                            *)
(*   the relation of direct links in the mempool DAG                       *)
(*                                                                         *)
(* - 'IsCertifiedBlock',                                                   *)
(*   the predicate for checking if a block is certified                    *)
(*                                                                         *)
(* - 'CertifiedBlocks',                                                    *)
(*   the set of all blocks that are certified via 'IsCertifiedBlock'       *)
(*                                                                         *)
(***************************************************************************)

\* the relation of direct links between blocks 
\* @type: ($block, $block) => Bool;
linksTo(b, y) ==
  \* type checks
  /\ b \in Block
  /\ y \in Block
  \* the certificate list of block b contains digest of y
  /\ \E c \in Range(b.cq) : 
     LET 
       \* @type: $block;
       blockOfC == fetchBlock(c)
     IN 
       blockOfC = y


\* checking whether a digest is justified via messages
\* @type: ($blockDigest) => Bool;
IsJustifiedDigest(dgst) == 
  \E v \in ByzValidator : 
        \* the digest was sent by v in a certMessage and …
     /\ certMsg(dgst, v) \in msgs 
        \* …, in turn, the certMessage was justified
     /\ LET
          relevantAcks == { a \in allAcks : a.digest = dgst }
        IN LET
          allSupporters == { a.sig : a \in relevantAcks }
        IN 
          \E X \in ByzQuorum \cap SUBSET allSupporters : TRUE

\* predicate for block certification
\* i.e., based msgs, there is a justified "Cert"-message 
\* @type: ($block) => Bool;
IsCertifiedBlock(b) ==
  \* type check
  /\ b \in Block
  \* check the digest
  /\ IsJustifiedDigest(digest(b))

\* the set of all blocks that are certified via 'IsCertifiedBlock'
\* @type: Set($block);
CertifiedBlocks == { b \in Block : IsCertifiedBlock(b) }

\* what's a proper quorum of certificates in (local) round r?
\* - must be at round r-1
\* - all certificates justified
\* @type: ($digestFamily, Int) => Bool;
IsProperCertQuorumAtRound(certificateQuorum, round) == 
  LET
    \* @type: $digestFamily;
    cq == certificateQuorum
    \* @type: Int;
    r == round
  IN
     \* we actually have a quorum (as domain)
  /\ (DOMAIN cq) \in ByzQuorum
     \* the round is the previous round
  /\ \A v \in DOMAIN cq : 
      /\ cq[v].rnd = r - 1
      /\ IsJustifiedDigest(cq[v])



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
\* @type: ($block) => Bool;
hasSupport(b) == 
     \* type check 
  /\ b \in Block
     \* 
  /\ \E W \in WeakQuorum : 
       \A w \in W : 
            \E y \in Block :
                 /\ y.creator = w
                 /\ << y, COA >> \in storedBlx[w]
                 /\ linksTo(y, b)                  


\* the constant number of rounds between each leader block commitment
CONSTANT
  \* @type: Int;
  WaveLength

ASSUME WaveLengthAssumption ==
  /\ WaveLength \in Nat
  /\ WaveLength >= 1

WaveLengthTimesNat == { n \in Nat : \E i \in Nat : n = WaveLength * i }
  
CommitBlock(b) == 
  \* type check
  /\ b \in Block
  \* pre-condition(s)
     \* proper round number
  /\ b.rnd \in WaveLengthTimesNat
     \* not yet committed any block at the round
  
  /\ ~\E y \in Block: 
           /\ commitMsg(digest(y)) \in msgs 
           /\ y.rnd = b.rnd                     
  \* enough support
  /\ hasSupport(b)
  /\ Send(commitMsg(digest(b)))
  /\ UNCHANGED allBUTmsgs


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
\* @type: ($block) => Bool;
IsCommitingLeaderBlock(b) == 
  \* type check
  /\ b \in Block
  \* commit message was sent (by consensus layer)
  /\ commitMsg(digest(b)) \in msgs 



(*    
\* checking if a block is commited
IsCommitted(b) ==
  /\ b \in Block
  /\ \/ IsCommitingLeaderBlock(b)
     \/ \E z \in Block : 
        /\ IsCommitingLeaderBlock(z)
        /\ b \in {} \* CausalHistory(z)

*)
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

\* coming soon ™
====
