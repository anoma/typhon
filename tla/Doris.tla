---------------------------- MODULE Doris -----------------------------------
\* **************************************************************************
\*
\* Doris is a DAG mempool similar to the Narwhal mempool as proposed
\* by Danezis, Kokoris Kogias, Sonnino, and Spiegelman in their
\* `^\href{https://arxiv.org/abs/2105.11827}{paper.}^' Further
\* inspiration is taken from
\* `^\href{https://arxiv.org/abs/2102.08325}{DAG-rider,}^', a
\* precursor to Narwhal.  (We shall refer to these papers as [N&T] and
\* [DAG-R], respectively.)
\*                                                                     
\* The following differences between Doris [N&T]/[DAG-R] deserve mention.
\* 
\* ① In Narwhal, “[c]lients send transactions to […] all validators”
\*   [N&T, Fig. 4].  This can lead to duplicate transactions in
\*   batches and high bandwidth usage/cost.  Our vision is to avoid
\*   this via a suitable protocol between clients that submit
\*   transactions to (workers at) validators; e.g., servers should
\*   respond with signed receipts (including a time stamp of the validator).
\*                                                                        
\* ② So far we do not use weak links (see [DAG-R]) — coming soon ™.
\* 
\* More generally, DAG-based consensus protocols, can be thought of as
\* as composition of a “logged” mempool, which is the first phase of a
\* consensus protocol, which in particular makes sure that the set of
\* transactions of interest at a given time is known to a super
\* majority of validators or _quorum_ in short.  Thus, only the client
\* server communication is epemeral, with the servers having the
\* (hugely problematic!) option of denying receipt of messages
\* (cf. the addition of time stamped proofs of receipt). Finally, the
\* best counterpart to bitcoint's mempool—as operated in the olden
\* days—in Anoma's architecture is the intent gossip network. 
\* **************************************************************************

\* ‼️ Note: so far no Byzantine behaviour is specified, yet ‼️ 

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

\* For the module "Functions", we rely on the 
\* `^\href{https://tinyurl.com/2ybvzsrc}{Community Module.}^'

-----------------------------------------------------------------------------

(***************************************************************************)
(*                         DATA STRUCTURES                                 *)
(***************************************************************************)

\* **************************************************************************
\* We encode certified vertices and their components.  The
\* components of certified vertices are certificates, vertex digests, and the like,
\* as used in Narwhal [N&T] and DAG-rider [DAG-R].  We consider
\* batches to be atomic; the processing of individual transactions can
\* be seen as a refinement.
\* **************************************************************************

CONSTANT
  \* "Batch": 
  \*   the set of batches
  \*   Elements of "Batch" have type BATCH, which is uninterpreted.
  \*
  \* @type: Set(BATCH);
  Batch

\* We assume that there is at least one batch.
ASSUME ExistenceOfBatches ==
  Batch # {}

\* *************************************************************************
\* We emulate hash functions on batches by a simple “wrapping”
\* operation, called "hash". Note that for actual crypographic hash
\* functions, hash collisions are in principle possible; this would
\* lead to issues in the proofs.
\* 
\* Vertex digests are going to be modelled in yet a different way
\* (to make model checking possible at all).
\* *************************************************************************

(* $batchHash: 
     the type alias for batch hashes 

--- batchHash ---
- batch: the hashed Batch

@typeAlias: batchHash = {
    batch : BATCH
};
*)

\* "BatchHash": 
\*   the set of hashes of batches
\* 
\* @type: Set($batchHash);
BatchHash == [ batch : Batch ]

\* "hash":
\*   operator modeling hash functions on batches
\* 
\* @type: (BATCH) => $batchHash;
hash(b) == [batch |-> b] 

\* LEMMA hash \in Bijection(Batch, BatchHash) \* obvious

-----------------------------------------------------------------------------
(***************************************************************************)
(*                         DATA STRUCTURES                                 *)
(***************************************************************************)

(*
Vertex digests serve to identify (certified) vertices without including the
whole vertex information, emulating “perfect” hashing.  "VertexDigest"
is the encoding of the set of all such vertex digests; we exploit that
the set of all messages (sent by any validator) includes all relevant
vertices. The type alias for vertex digests is "$vertexDigest". Later, we
shall define "fetchVertex", which retrieves the vertex that corresponds
to a digest, based on the set of sent messages.
 
Note the following! 

- "VertexDigest"s are “ideal” hashes (if correct).
- For correctness, we have to ensure that, indeed, "digest(b)"
  identifies a unique vertex `b`, retrievable via "fetchVertex".
*)

(* $vertexDigest: 
     type alias for vertex digests

--- vertexDigest ---
- creator: the creator of the “digested vertex”

- rnd: the round of the “digested vertex”

- nonce: fake validators might propose several vertices per round

@typeAlias: vertexDigest = {
   creator: BYZ_VAL
   , 
   rnd:     Int
   , 
   nonce:   Int    
};
===
*)

\* "Nonce":
\*   the set for nonces (numbers used once per round)
\* @type: Set(Int);
Nonce == Nat

\* "THENONCE":
\*   a placeholder (as no Byzantine behaviour is implemented, yet)
\* @type: Int;
THENONCE == 0 \* coming soon ™

\* "VertexDigestType":
\*   an over-approximation of "VertexDigest", the set of vertex digests 
\* 
\* @type: Set($vertexDigest);
VertexDigestType == [
    \* the creator of a vertex
    creator: ByzValidator
    ,               
    \* the round number of the vertex
    rnd:     Nat
    ,               
    \* a nonce, keeping track of spurious vertices beyond the first / zeroth
    nonce:   Nat
]

-----------------------------------------------------------------------------

(***************************************************************************)
(* "If a vertex is valid, the other validators store it and acknowledge it  *)
(* by signing its _vertex digest_, _round number_, and _creator’s           *)
(* identity_." [N&T]                                                       *)
(***************************************************************************)

(*
In Doris, we deviate from the above/[N&T].

- batch hashes are not acknowledged indivitually, but, instead
- batch hashes are acknowledged jointly, as part of the “enclosing” vertex 

*)

(***************************************************************************)

\* In most cases, acknowledging signatures of a vertex will 
\* be issued by validators differing from the creator.
                                                                        
\* We define the set "Ack" as the set of all vertex acknowledgements,   
\* which are in particular signed by validators.  A correct validator has  
\* to store the vertex (or enough erasure coding segments) for later        
\* retrieval (until garbage collection and/or execution) and 
\* also the referenced batches.                       

(***************************************************************************)

(* $ack: type alias for vertex acknowledgments 
--- ack ---
- digest: the digest of the acknowledged vertex

- sig: the signing validator
===
@typeAlias: ack = {
    digest : $vertexDigest,
    sig :    BYZ_VAL
};
*)

\* "AckType":
\*   an over-approximation of the set of vertex acknowledgements
\* 
\* @type: Set($ack);
AckType == [
  \* the digest of the acknowledged vertex
  digest : VertexDigestType, 
  \* the signing validator
  sig :    ByzValidator 
]

-----------------------------------------------------------------------------

(***************************************************************************)
(* “Once the creator gets 2f + 1 distinct acknowledgments for a vertex, it  *)
(* combines them into a certificate of vertex availability, that includes   *)
(* the vertex digest, current round, and creator identity.” [N&T]           *)
(***************************************************************************)

\* The type of such certificats are families of acks, which in turn can 
\* be simpliefied to the acknowleged digest and the signing validator

(* $digestFamily: the type of certificate quorums (and also weak links)
--- digestFamily ---
This is “just” an (injective) function from validators to vertex digests; 
every element of the domain can be taken to be a signer (by convention).
===
@typeAlias: digestFamily = 
  BYZ_VAL -> $vertexDigest
;
*)

\* "AckQuorumType":
\*   A quorum of vertex digests, where
\*   q |-> d encodes that validator `q` has signed the vertex digest `d`
\*
\* @type: Set($digestFamily);
AckQuorumType == 
  UNION (
     \* proper ack quorum
     {Injection(Q, VertexDigestType) : Q \in ByzQuorum} 
     \cup
     \* and the empty ack (e.g., for genesis vertex)
     {Injection({}, VertexDigestType)}
  )

\* "emptyQuorum":
\*   the empty quroum (e.g., for the genesis vertex)
\* 
\* @type: $digestFamily;
emptyQuorum == 
  CHOOSE f \in Injection({},VertexDigestType) : TRUE
\* Here↑, we could also use Apalache's `Guess` instead of `CHOOSE`. 

\* "emptyLinks":
\*   another name for the empty ack
\*
\* @type: $digestFamily;
emptyLinks == 
  emptyQuorum

\* @type: Set($digestFamily);
CertificateOption == AckQuorumType 

\* @type: Set($digestFamily);
Certificate == CertificateOption \ Injection({}, VertexDigestType)

(***************************************************************************)
(* According to [N&T], a valid vertex must                                 *)
(*                                                                         *)
(* 1.  contain a valid signature from its creator;                         *)
(*                                                                         *)
(* 2.  be at the local round r of the ByzValidator checking it;            *)
(*                                                                         *)
(* 3.  be at round 1 (genesis), or contain certificates for                *)
(*     at least 2f + 1 vertices of round r-1;                              *)
(*                                                                         *)
(* 4.  be the first one received from the creator for round r .            *)
(*                                                                         *)
(* We plan to allow for additional weak links in the sense of DAG-rider    *)
(* [DAG-R].   (coming soon ™)                                              *)
(***************************************************************************)

CONSTANT
  \* "BatchMax":
  \*   the maximal number of batches in a vertex (for model checking)
  \*
  \* @type: Int;
  BatchMax 

\* ASSUME BatchMax == 1  \* if in doubt

\* "BatchMaxBoundedBatchSubsets":
\*   a bounded subset operator, specifically for the $batchHash type
\* 
\* @type: Set(Set($batchHash));
BatchMaxBoundedBatchSubsets == 
  IF BatchMax < 0 
  THEN {}
  ELSE {{}} \cup { Range(f) : f \in [ 1..BatchMax -> BatchHash ] }

\* "SomeHxs":
\*   the set of possible batch hashes in a vertex 
\* 
\* @type: Set(Set($batchHash));
SomeHxs == BatchMaxBoundedBatchSubsets

(* $vertex: the type alias for a vertex 
--- vertex ---

- creator : the vertex's creator

- rnd     : the round in which the vertex is proposed

- bhxs    : the set of batch hashes in the vertex

- cq      : the certificate quroum    

- wl      : the weak links
===

@typeAlias: vertex = {
    creator : BYZ_VAL,            
    rnd :     Int,                     
    bhxs :    Set($batchHash),                  
    cq :      $digestFamily,
    wl :      $digestFamily
};
*)

\* "VertexType":
\*   an over-approximation of the set of Vertices to consider, cf. "Vertex"
\* 
\* @type: Set($vertex);
VertexType == [ 
  \* the vertex proposer \& signer
  creator : ByzValidator, 
  \* the round of the vertex proposal
  rnd :     Nat, 
  \* the batch hashes of the vertex
  bhxs :    SomeHxs, 
  \* a CoA (unless genesis vertex)
  cq :      CertificateOption, 
  \* weak links (coming soon ™)
  wl :      [{} -> VertexDigestType] 
]

\* "digest":
\*   the operator for constructing vertex digests 
\* 
\* @type: ($vertex) => $vertexDigest;
digest(vertex) == 
  LET
    \* @type: $vertex;
    b == vertex
  IN LET
    \* @type: BYZ_VAL;
    c == b.creator
    \* @type: Int;
    i == b.rnd
    \* @type: Int;
    n == THENONCE
  IN
    \* as we keep vertex proposals in the set of messages "msgs", 
    \* we only need to keep the following information
    [creator |-> c, rnd |-> i, nonce |-> n]
    \* the nonce is only necessary for 
    \* Byzantine validators to propose several vertices in a round

\* end of "DATA STRUCTURES"
-----------------------------------------------------------------------------

(* ----------------------------------------------------------------------- *)
(*                        MESSAGE STRUCTURE                                *)
(* ----------------------------------------------------------------------- *)

\* *************************************************************************
\* Following 
\* `^\href{https://bit.ly/3a6ydfc}{Lamport's specification of Paxos,}^'
\* we keep all messages in a single set.  There are the following types
\* of message.
                                                                         
\*   - "Batch" broadcast a batch, **from** a worker (to workers of the
\*     same index).
                                                                         
\*   - "Vertex" a vertex creator broadcasts a new vertex
                                                                         
\*   - "Ack" acknowledgment *by* a Validator, having vertex available          
                                                                         
\*   - "Cert" broadcasting a (vertex) certificate (by a creator)              
                                                                         
\* We call a "mirror worker" a worker of the same index at a different
\* validator.  We assume that clients send a transaction/batch only to
\* one validator at a time, and only if the transaction gets orphaned,
\* inclusion via a weak link is a desired possibility; thus, we "abuse"
\* weak links for an additional link to the last proposed vertex.
  
\* Correct validators make vertices of batches arriving at their workers,
\* to be broadcast to other workers.
                                                                         
\* We abstract away all worker-primary communication "inside" validators;
\* we have remote direct memory access (RDMA) in mind.  Further
\* refinement could be applied if a message passing architecture was
\* desired.
\* *************************************************************************

VARIABLE
  (* $msg: type alias for the set of messages sent
   --- msg ---
   
   - Batch: broadcast a batch 

     - batch: the batch being broadcast

     - from: the sending working
  
   - Vertex: broadcast a vertex

     - vertex: the vertex being broadcast

     - creator: the creator (and sender) of the vertex

     - nonce: (Byzantine validators only)


   - Ack: acknowledgment of vertex (including the batches)
    
     - ack: the actual acknowledgment information

     - by: the signer (and sender)

   - Cert: the certificate of availability (broadcast by vertex creator)

     - digest: the digest of the certified vertex

     - creator: the vertex creator (and sender)

   - Commit: message "from" the consensus layer

     - digest: the digest of the commited leader vertex

   - Executed: (coming soon ™ -- execution layer singal)  

   - Abort(NIL): (reserved, no use yet) 
  
   ===
   @typeAlias:msg = 
     Batch(     {batch : BATCH, from : $worker}                     )|
     Vertex(     {vertex: $vertex, creator : BYZ_VAL, nonce: Int}      )| 
     Ack(       {ack : $ack, by : BYZ_VAL}                          )| 
     Cert(      {digest : $vertexDigest, creator : BYZ_VAL}          )|
     Commit(    {digest : $vertexDigest }                            )|
     Executed(  {digest : $vertexDigest }                            )|
     Abort(NIL) ; 
  *)
  \* @type: Set($msg);
  msgs

\* Batch():
\*   broadcast a fresh "batch" from a "worker" (to mirror workers)
\*
\* @type: (BATCH, $worker) => $msg;
batchMsg(b, w) == 
  Variant("Batch", [ batch |-> b, from |-> w])

\* Vertex():
\*   creator produces a vertex and broadcasts it
\* 
\* @type: ($vertex, BYZ_VAL, Int) => $msg;
vertexMsg(b, c, n) == 
  Variant("Vertex", [vertex |-> b, creator |-> c, nonce |-> n])

\* Ack():
\*   commmitment "by" a validator to have stored a vertex 
\* 
\* @type: ($ack, BYZ_VAL) => $msg;
ackMsg(a, v) == 
  Variant("Ack", [ack |-> a, by |-> v])

\* Cert():
\*   creator aggregates quorum of acks into a certificate 
\*   and broadcasts it
\* 
\* @type: ($vertexDigest, BYZ_VAL) => $msg;
certMsg(d, c) == 
  Variant("Cert", [digest |-> d, creator |-> c]) 

\* Commit():
\*   a commit message commits a leader vertex (sent by the consensus layer)
\*  
\* @type: ($vertexDigest) => $msg;
commitMsg(d) ==
  Variant("Commit", [digest |-> d])

-----------------------------------------------------------------------------    
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
(* ① a local round number (corresponding a layer of DAG mempool);          *)
(*                                                                         *)
(* ② a worker specific pool of received client batches;                    *)
(*                                                                         *)
(* ③ a pool of batch hashes to be included in the next vertex;              *)
(*                                                                         *)
(* ④ a local storage for (hashes of) batches;                              *)
(*                                                                         *)
(* ⑤ a local storage for (digests of) vertices                        *)
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

\* Primaries' pools of hashes for the next vertex (initially {}), cf. ③
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

\* Each ByzValidator has storage for vertices (initially {}), cf. ⑤ 
\* with the following two different stages of knowing a vertex
AVL == FALSE 
COA == TRUE
VARIABLE
  \* @type: BYZ_VAL -> Set(<<$vertex, Bool>>);
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
  (* Moreover, we have shorthands for of the form `allBUT<x>N<y>N<z>`.     *)
  (*************************************************************************)

allBUTstoredBlx == 
  <<msgs, rndOf, batchPool, nextHx, storedHx, storedBlx>>

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

\* "maxRound":
\*   gives the (current) maximal round of any validator
\* 
\* @type: Int;
maxRound == 
  CHOOSE n \in Range(rndOf) : n+1 \notin Range(rndOf)

\* "Vertex":
\*   a smaller set than VertexType of currently relevant vertices
\*  
\* @type: Set($vertex);
Vertex ==
    { b \in VertexType : 
            /\ b.rnd <= maxRound+1
            /\ \E n \in Nonce : 
                    vertexMsg(b, b.creator, n) \in msgs
    }

\* "VertexDigest":
\*   the set of vertex digests based on Vertex
\* 
\* @type: Set($vertexDigest);
VertexDigest == 
  {digest(b) :  b \in Vertex}

\* "proposedVerticesByValidatorInRound":
\*   the set of vertices proposed by a validator in a given round
\*   
\* @type: (BYZ_VAL, Int) => Set($vertex);
proposedVerticesByValidatorInRound(validator, r) == 
  LET
    c == validator
  IN
  { b \in Vertex : 
      /\ b.rnd = r
      /\ \E n \in Nonce : 
            LET
              \* @type: $msg;
              m == vertexMsg(b, c, n)
            IN
              m \in msgs
  }
  
\* "proposedVerticesByValidator":
\*   the set of vertices proposed by a validtor
\*  
\* @type: (BYZ_VAL) => Set($vertex);
proposedVerticesByValidator(validator) == 
  LET
    c == validator
  IN
  { b \in Vertex : 
       \E n \in Nonce : 
          LET
            \* @type: $msg;
            m == vertexMsg(b, c, n)
          IN
            m \in msgs
  }

\* "proposedVertices":
\*   the set of all currently proposed vertices
\*  
\* @type: Set($vertex);
proposedVertices == 
  UNION { proposedVerticesByValidator(c) : c \in ByzValidator } 

\* "proposedVerticesInRound":
\*   the set of all vertices that were proposed for a given round
\* 
\* @type: (Int) => Set($vertex);
proposedVerticesInRound(r) == 
   { b \in proposedVertices : b.rnd = r }

\* "allAckMsgs":
\*   the set of all "Ack"-messages sent so far
\* 
\* @type: Set($msg);
allAckMsgs ==
  { m \in msgs : VariantTag(m) = "Ack" }

\* "allAcks":
\*   the set of all acknowledgments sent (via "Ack"-messages)
\* 
\* @type: Set($ack);
allAcks ==
  { VariantGetUnsafe("Ack", m).ack : m \in allAckMsgs}    

\* "acksOfDigest":
\*   the set of all acks for a given digest
\* 
\* @type: ($vertexDigest) => Set($ack);
acksOfDigest(dgst) == 
  LET
    \* the digest of interest
    \* @type: $vertexDigest;
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
(*   "misbehave". (Recall that, ideally, clients submit their              *)
(*   transactions to only one worker.)                                     *)
(*   We combine batch arrival with broadcasting a batch (cf. "BatchBC").   *)
(*   (The action of batch arrival is strictly local to the worker.)        *)
(*                                                                         *)
(* - Batch broadcast "BatchBC" (message "Batch"):                          *)
(*                                                                         *)
(*   A worker broadcasts a                                                 *)
(*   batch, stores it, and forwards it to its primary for vertex inclusion. *)
(*                                                                         *)
(* - Batch storing "StoreBatch" (NO message ):                             *)
(*                                                                         *)
(*   Reception of a batch, storing and hashing such that recieved vertices   *)
(*   can be validated and acknowledged by the primary.                     *)
(*                                                                         *)
(* - Vertex production and broadcast "VertexBC" (message "Vertex"):           *)
(*                                                                         *)
(*   A primary builds a vertex from enough certificates of availability     *)
(*   and batch hashes provided by its workers and broadcasts the           *)
(*   vertex. "One primary integrates references to [batches] in Mempool     *)
(*   primary vertices."  [N&T]                                               *)
(*                                                                         *)
(* - Vertex acknowledgement "Ack" (message "Ack")                           *)
(*                                                                         *)
(*   Receive a vertex, check its validity, store it, & acknowledge it.      *)
(*                                                                         *)
(* - Certificate broadcats "CertBC" (message "Cert")                       *)
(*                                                                         *)
(*   Take an acknowledgement quorum of a proposed vertex, aggregate it      *)
(*   into a ceritificate, and broadcast the certificate.                   *)
(*                                                                         *)
(* - Store a vertex certificate "StoreVertex" (NO message)                   *)
(*                                                                         *)
(*   “Receive” a certificate of availability and store it.                 *)
(*                                                                         *)
(* - Advancing the local round 'AdvanceRound' (NO message)                 *)
(*                                                                         *)
(*   A validator moves to the next round,                                  *)
(*   after receiving a quorum of vertex certificates.                       *)
(***************************************************************************)


(***************************************************************************)
(* We define some subactions of the next-state actions.  The action        *)
(* Send(m) has as effect the insertion of message m to the set msgs.       *)
(***************************************************************************)

\* SUB-ACTION (... and thus no UNCHANGED) "Send":
\*   sending a message will only be used as "part of" a "full" action
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
  \* type checking
  /\ b \in Batch
  /\ w \in Worker
  \* empty pre-condition
  \* post-condition: 
     \* add the batch `b` the the batch pool of `w`
  /\ batchPool' = \* ¡batchPool
       [batchPool EXCEPT ![w] = @ \cup {b}] 
     \* add the hash of the batch to the primary's next hashes
  /\ nextHx' = \* ¡nextHx
       [nextHx EXCEPT ![p] = @ \cup {hash(b)}] 
     \* also add the hash of the primary's stored hashes
  /\ storedHx' = \* ¡storedHx
       [storedHx EXCEPT ![p] = @ \cup {hash(b)}] 
     \* broadcast the batch 
  /\ Send(batchMsg(b,w)) \* ¡msgs
     \* nothing else changes
  /\ UNCHANGED allBUTmsgsNbatchPoolNnextHxNstoredHx
\* end of action "BatchBC"


\* ACTION "StoreBatch": 
\*   store a received Batch at the receiving worker 
\*
\* ¡storedHx
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
     \* it is not stored yet
  /\ hash(b) \notin storedHx[p] 
  \* post-condition: add the batch hash to the set of known hashes
     \* store the hash at the primary
  /\ storedHx' = 
       [storedHx EXCEPT ![p] = @ \cup {hash(b)}]
  \* we elide the details of storing the actual batch for availability
  /\ UNCHANGED allBUTstoredHx 
\* end of action "StoreBatch"

\* "currentVerticesProduced" (auxiliary set):
\*   the vertices produced by a certain validator that carry the nonce
\* 
\* @type: (BYZ_VAL, Int) => Set($vertex);
currentVerticesProduced(creator, nonce) == 
  LET
    \* @type: BYZ_VAL;
    c == creator
    \* @type: Int;
    n == nonce
    \* @type: Set($msg);
    allBroadcastMessages == 
      { m \in msgs : VariantTag(m) = "Vertex" } 
  IN LET
    \* @type: Set({vertex: $vertex, creator : BYZ_VAL, nonce: Int});
    data == 
      { VariantGetUnsafe("Vertex", m) : m \in allBroadcastMessages } 
  IN LET
    \* @type: Set({vertex: $vertex, creator : BYZ_VAL, nonce: Int});
    filteredData == 
      { x \in data : /\ x.creator = c
                     /\ x.nonce = n
      }
  IN { x.vertex : x \in filteredData }

\* "fetchVertex" (operator):
\*    yields the vertex of the digest (or **should** raise an error),
\*    based on the messages sent (i.e., present in the variable "msg")
\* 
\* @type: $vertexDigest => $vertex;
fetchVertex(dgst) == 
  LET
    \* @type: Set($vertex);
    allPossibleVertices ==
      currentVerticesProduced(dgst.creator, dgst.nonce)
  IN LET
    \* @type: Set($vertex);
    candidates == {c \in allPossibleVertices : c.rnd = dgst.rnd}
  IN
    \* extract the unique element (or error❓cf. SubSingletons.tla)
    extract(candidates) 


\* ACTION GenesisVertexBC [instance of VertexBC]:
\*   a validator produces a genesis vertex and broadcasts it
\* 
\* @typing: BYZ_VAL => Bool;
GenesisVertexBC(validator) ==
  LET
    \* @type: BYZ_VAL;
    v == validator
    \* @type: $vertex;
    b == [ creator |-> v,
           rnd |-> 1, 
           bhxs |-> nextHx[v],
           cq |-> emptyQuorum,
           wl |-> emptyLinks
     ]
  IN
  \* type check
  /\ v \in ByzValidator
  \* pre-condition
  /\ rndOf[v] = 1 \* validator has local round 1
  \* post-condition
     \* send the vertex
  /\ Send(vertexMsg(b, v, THENONCE)) \* ¡msgs
     \* empty v's nextHx (for validators)
  /\ nextHx' = \* ¡nextHx
          [nextHx EXCEPT ![v] = {}] 
  /\ UNCHANGED allBUTmsgsNnextHx \* end of action "GenesisVertexBC"

\* "hasVertexHashesStored" (auxiliary predicate):
\*   predicate for checking the storage of hashes at a validator
\*  
\* @type: ($vertex, BYZ_VAL) => Bool;
hasVertexHashesStored(vertex, val) ==
 \* we know all batches
  vertex.bhxs \subseteq storedHx[val]


\* "checkCertificatesOfAvailability":
\*   predicate for checking the storage of vertices of digests
\* 
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
         \* @type: $vertex;
         b == fetchVertex(d)
       IN  
         \* vertex is known with a certificate
         << b, COA >> \in storedBlx[v]  

\* "validVertex":
\*   predicate that checks whether a correct validator should 
\*   consider a given vertex to be valid
\* 
\* @type: ($vertex, BYZ_VAL) => Bool;
validVertex(vertex, validator) == 
  LET 
    \* the vertex in question
    \* @type: $vertex;
    b == vertex
    \* the validator checking the validity
    \* @type: BYZ_VAL;
    v == validator 
  IN
     \* the round must be a positive natural number 
  /\ b.rnd > 0 \*
     \* batch hashes stored (always needed)
  /\ hasVertexHashesStored(b, v)
     \* and vertex references stored
  /\ checkCertificatesOfAvailability(b.cq, v)
  /\ DOMAIN b.wl = {} 

\* ACTION Ack:
\*   Receive a vertex, check its validity, store it, acknowledge it.
\*
\* ¡msgs, ¡storedBlx
\* @type: (BYZ_VAL, $vertex) => Bool;
Ack(validator, vertex) == 
  LET
    \* @type: BYZ_VAL;
    v == validator
    \* @type: $vertex; 
    b == vertex 
  IN LET
    \* @type: $vertexDigest;
    d == digest(b)
  IN LET
    \* @type: $ack;
    a == [digest |-> d, sig |-> v]
  IN
  \* typing of v (for TLC)
  /\ v \in ByzValidator
  \* pre-condition:
     \* check that vertex b was proposed
  /\ b \in proposedVertices 
     \* check that b is valid (according to v)
  /\ validVertex(b, v) \* 
     \* check that b is “new”
  /\ << b, AVL >> \notin storedBlx[v]
  /\ << b, COA >> \notin storedBlx[v]  
  \* post-condition:
     \* send the acknowledgement 
  /\ Send(ackMsg(a, v)) \* ¡msgs
     \* store the vertex as "available" (but not certified)
  /\ storedBlx' = \* ¡storedBlx
       [storedBlx EXCEPT ![v] = @ \cup {<<b, AVL>>}] 
  /\ UNCHANGED allBUTmsgsNstoredBlx

\* ACTION CertBC:
\*   broadcast a certificate of availability of (the digest of) a vertex 
\*  
\* @type: ($vertexDigest) => Bool;
CertBC(dgst) ==
  LET
    \* the vertex digest to be certified
    \* @type: $vertexDigest;
    d == dgst
  IN
  \* typing 
  /\ dgst \in VertexDigest
  \* pre-condition
     \* enough ack messages sent (by a quorum)
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
  /\ UNCHANGED allBUTmsgs

\* ACTION StoreVertex:
\*   store a vertex whose certificate was sent around  
\* 
\* @type: ($vertex, BYZ_VAL) => Bool;
StoreVertex(vertex, validator) ==
  LET
    \* @type: $vertex;
    b == vertex
    \* @type: BYZ_VAL;
    v == validator
  IN    
    \* type check TLC
    /\ b \in Vertex
    /\ v \in ByzValidator
    \* pre-condition
       \* the validor has acknowledged and stored the vertex 
    /\ << b, AVL >> \in storedBlx[v]
    \* post-condition
       \* store also the certificate of availability of the vertex
    /\ storedBlx' = \* ¡storedBlx
         [storedBlx EXCEPT ![v] = @ \cup {<< b, COA >>}]
    /\ UNCHANGED allBUTstoredBlx   

\* "preceedingVertices":
\*   the set of vertices referencable by a validator in the previous round
\*   cf. \prec—the directly covers relation 
\* 
\* @type: (BYZ_VAL, Int) => Set($vertex);
preceedingVertices(v, r) == 
      { b \in Vertex : 
          /\ b.rnd = r - 1
          /\ << b, COA >> \in storedBlx[v]
      }

\* ACTION AfterGenesisVertexBC [instance of VertexBC]:
\*  a validator produces a vertex, after genesis, and broadcasts it
\* 
\* @typing: BYZ_VAL => Bool;
AfterGenesisVertexBC(validator) ==
  LET
    \* @type: BYZ_VAL;
    v == validator   
    \* @type: Int;
    r == rndOf[v]
  IN LET
    \* @type: Set(BYZ_VAL);
    certifiedProposers == 
      { b.creator : b \in preceedingVertices(v,r) }
  IN
  \* type check:
     \* it's a validator
  /\ v \in ByzValidator
  \* pre-condition
     \* validator has advanced to a non-genesis round
  /\ rndOf[v] > 1 
     \* no vertex proposed yet
  /\ proposedVerticesByValidatorInRound(v, rndOf[v]) = {}
     \* there exists a quorum of certified vertex in the previous round
  /\ \E Q \in ByzQuorum \cap SUBSET certifiedProposers : 
       LET 
         \* @type: Set($vertex);
         relevantVerticesByQ == 
           { b \in preceedingVertices(v,r) : b.creator \in Q }
       IN LET
         \* @type: $vertex;
         theVertex == [
             creator |-> v, 
             rnd |-> rndOf[v],
             bhxs |-> nextHx[v],
             cq |-> [q \in Q |-> 
                       digest(CHOOSE b \in preceedingVertices(v,r) : b.creator = q)
                    ], 
             wl |-> emptyLinks
           ]
       IN 
       \* post-condition
           \* send the vertex
         /\ Send(vertexMsg(theVertex, v, THENONCE)) \* ¡msgs
         \* empty v's nextHx (for validators)
         /\ nextHx' = \* ¡nextHx
              [nextHx EXCEPT ![v] = {}] 
  /\ UNCHANGED allBUTmsgsNnextHx \* end of action "GenesisVertexBC"

\* ACTION VertexBC:
\*   the combination of the two cases of vertex production, viz.
\*   - GenesisVertexBC
\*   - AfterGenesisVertexBC
\*
\* @typing: BYZ_VAL => Bool;
VertexBC(validator) == 
  \/ GenesisVertexBC(validator)
  \/ AfterGenesisVertexBC(validator)
    
\* AdvanceRound:
\*   correct validators can increment their local round number 
\*   as soon as they have a quorum of CoA for vertices of the previous round 
\*  
\* @type: (BYZ_VAL) => Bool;
AdvanceRound(validator) == 
  LET
    \* @type: Set(BYZ_VAL);
    X == 
      {b.creator : b \in preceedingVertices(validator, rndOf[validator]+1)}
  IN 
  \* pre-condition:
      \* enough vertex available
  /\ \E Q \in ByzQuorum \cap SUBSET X : TRUE
  \* post-condition
  /\ rndOf' = [rndOf EXCEPT ![validator] = @ + 1]
  /\ UNCHANGED allBUTrndOf

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          DAG STRUCTURE                                  *)
(***************************************************************************)

(* We define several auxiliary predicates and sets  *)

\* "linksTo":
\*   the relation of direct links between vertices 
\*   (the vertices do not have to be proposed)
\*
\* @type: ($vertex, $vertex) => Bool;
linksTo(b, y) ==
  \* type checks
  /\ b \in Vertex
  /\ y \in Vertex
  \* the certificate list of vertex b contains digest of y
  /\ \E c \in Range(b.cq) : 
     LET 
       \* @type: $vertex;
       vertexOfC == fetchVertex(c)
     IN 
       vertexOfC = y

\* checking whether a digest is certified via messages
\* @type: ($vertexDigest) => Bool;
IsCertifiedDigest(dgst) == 
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

\* predicate for vertex certification
\* i.e., based msgs, there is a justified "Cert"-message 
\* @type: ($vertex) => Bool;
IsCertifiedVertex(b) ==
  \* type check
  /\ b \in Vertex
  \* check the digest
  /\ IsCertifiedDigest(digest(b))

\* the set of all vertices that are certified via 'IsCertifiedVertex'
\* @type: Set($vertex);
CertifiedVertices == { b \in Vertex : IsCertifiedVertex(b) }

\* "IsProperCertQuorumAtRound":
\*    what's a proper quorum of certificates in (local) round r?
\*    - must be at round r-1
\*    - all certificates justified
\*
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
      /\ IsCertifiedDigest(cq[v])

-----------------------------------------------------------------------------
    
(***************************************************************************)
(*                      CONSENSUS ABSTRACTION                              *)
(***************************************************************************)

(***************************************************************************)
(* Instead of the (pseudo-)random leader election of Tusk [N&T], we model  *)
(* a non-deterministic choice of leader vertices in each _k_-th round for a  *)
(* globally fixed _k_ > 0 with the additional guarantee that the vertex is  *)
(* referenced by at least a weak quorum.                                   *)
(***************************************************************************)

\* hasSupport:
\*   predicate that checks if a vertex is a commitable leader vertex
\* 
\* @type: ($vertex) => Bool;
hasSupport(b) == 
     \* type check 
  /\ b \in Vertex
     \* 
  /\ \E W \in WeakQuorum : 
       \A w \in W : 
            \E y \in Vertex :
                 /\ y.creator = w
                 /\ << y, COA >> \in storedBlx[w]
                 /\ linksTo(y, b)

CONSTANT
  \* ̈"WaveLength":
  \*   the constant number of rounds between each leader vertex commitment
  \*
  \* @type: Int;
  WaveLength

ASSUME WaveLengthAssumption ==
  /\ WaveLength \in Nat
  /\ WaveLength >= 1

WaveLengthTimesNat == 
  { n \in Nat : \E i \in Nat : n = WaveLength * i }

\* ACTION "CommitVertex":  
\*   the action of commiting a vertex (by consensus)
\* 
\* @type: $vertex => Bool;
CommitVertex(b) == 
  \* type check
  /\ b \in Vertex
  \* pre-condition(s)
     \* proper round number
  /\ b.rnd \in WaveLengthTimesNat
     \* not yet committed any vertex at the round
  /\ ~\E y \in Vertex: 
           /\ commitMsg(digest(y)) \in msgs 
           /\ y.rnd = b.rnd                     
  \* enough support
  /\ hasSupport(b)
  /\ Send(commitMsg(digest(b)))
  /\ UNCHANGED allBUTmsgs

-----------------------------------------------------------------------------

(***************************************************************************)
(*                         COMMITTED VERTEX                                 *)
(***************************************************************************)
 
(***************************************************************************)
(* We define when a vertex is commited, relative to the LeaderVertex         *)
(* selection.  Later garbage collected vertices will remain commited.        *)
(*                                                                         *)
(* We take the following necessary (and sufficient) condition for          *)
(* commitment of a leader vertex (e.g., if chosen as candidate leader       *)
(* vertex):                                                                 *)
(*                                                                         *)
(* 1.  There is a weak quorum of vertices, each of which                     *)
(*   a) references the vertex via its certificate quorum and                *)
(*   b) has itself obtained a certificate of availability (broadcast by    *)
(*      its creator).                                                      *)
(***************************************************************************)

\* checks whether a leader vertex is a leader vertex
\* @type: ($vertex) => Bool;
IsCommitingLeaderVertex(b) == 
  \* type check
  /\ b \in Vertex
  \* commit message was sent (by consensus layer)
  /\ commitMsg(digest(b)) \in msgs 


(* (coming soon ™) 
\* checking if a vertex is commited
IsCommitted(b) ==
  /\ b \in Vertex
  /\ \/ IsCommitingLeaderVertex(b)
     \/ \E z \in Vertex : 
        /\ IsCommitingLeaderVertex(z)
        /\ b \in {} \* CausalHistory(z)
*)
-----------------------------------------------------------------------------

(***************************************************************************)
(*                         GARBAGE COLLECTION                              *)
(***************************************************************************)

(***************************************************************************)
(* Gargabge collection marks a vertex as "orphaned", either if it is not    *)
(* and never will be in the causal history of a leader vertex or if the     *)
(* distance from its commiting leader vertex is too long where the          *)
(* _commiting leader vertex_ of a vertex b is the leader vertex with the      *)
(* least round number whose causal history contains the vertex b. *)
(***************************************************************************)

\* coming soon ™
====
