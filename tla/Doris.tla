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

EXTENDS Functions, Integers, FiniteSets

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

Worker == WorkerIndex \X ByzValidator

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

\* "SomeHashes" is an arbitrary finite set of batch-hashes
SomeHashes == { X \in SUBSET BatchHash : IsFiniteSet(X) }



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
AckType == UNION {[Q -> Ack] : Q \in ByzQuorum} 

AckByzQuorum ==
    { ax \in AckType : /\ (\A v,w \in DOMAIN ax :               
                            /\ ax[v].digest = ax[w].digest       
                            /\ ax[v].rnd = ax[w].rnd             
                            /\ ax[v].creator = ax[w].creator)    
                        /\ \A v \in DOMAIN ax : ax[v].sig = v
    }

\* The second conjunct, 
\* i.e., "\A v \in DOMAIN ax : ax[v].sig = v",
\* implies that we actually have distinct acknowledgments of the same digest,
\* thus making ax an injection. 


\* LEMMA \A ax \in AckByzQuorum : IsInjective(ax) \* TODO

(***************************************************************************)
(* An AckByzQuorum is essentially a Certificate of availability.  We thus  *)
(* define an alias and provide commodity functions for reading the fields  *)
(* of the contained acknowledgments, which must all agree on the digest,   *)
(* round, and creator.                                                      *)
(***************************************************************************)

Certificate == AckByzQuorum
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

\* The "type" of a Certificate of Availability (cf. AckType)
CertType == UNION {[Q -> Certificate] : Q \in ByzQuorum} 

CertQuorum ==
    { cq \in CertType : \A v,w \in DOMAIN cq :
          /\ cq[v].rnd = cq[w].rnd                   
          /\ (v /= w => cq[v].digest /= cq[w].digest)
    } 

WeakLinks == UNION {[Q -> Certificate] : Q \in SUBSET ByzValidator }

noCert == CHOOSE i \in [{} -> Certificate] : TRUE

BlockStructure ==
    { b \in [ creator : ByzValidator, \* the block proposer
              rnd :     Nat, \* the round of the block proposal
              bhxs :    SomeHashes, \* the batch hashes of the block
              cq :      CertQuorum \cup {noCert}, \* a CoA-quorum 
              wl :      WeakLinks, \* possibly weak links             
              sig :     ByzValidator \* creator signature
            ] :
      /\ b.creator = b.sig \* on redundancy: cf. note on signatures
      /\ \A l \in DOMAIN b.wl : getRnd(b.wl[l]) < b.rnd-1 \* weak (!) links 
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
(*   index)                                                                *)
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


\* All messages that can be send between workers/primaries/validators
Message ==
    \* broadcast a fresh "batch" from a "worker" (to mirror workes)
    [type : {"batch"}, batch : Batch, from : Worker]
    \cup
    \* acknowledge a received "batch" (of mirror workes)
    [type : {"batch-ack"}, hx : BatchHash, sig : Worker]
    \cup
    \* creator produces a block and broadcasts it 
    [type : {"block"}, block: Block, creator : Validator]
    \cup
    \* commmitment "by" a validator to have stored a block 
    [type : {"block-ack"}, ack : Ack, by : Validator]
    \cup
    \* creator aggregates acks into a cert and broadcasts it
    [type : {"cert"}, cert : Certificate, creator : Validator]

\* end of "MESSAGE STRUCTURE"

-----------------------------------------------------------------------------

(*-------------------------------------------------------------------------*)
(*                           LOCAL STATE                                   *)
(*-------------------------------------------------------------------------*)

(***************************************************************************)
(* The local state of validators and workers at validators is              *)
(*                                                                         *)
(* 1. a local round number (corresponding a layer of DAG mempool);          *)
(*                                                                         *)
(* 2. a worker specific pool of received client batches;                    *)
(*                                                                         *)
(* 3. a pool of batch hashes to be included in the next block;              *)
(*                                                                         *)
(* 4. a local storage for (hashes of) batches;                              *)
(*                                                                         *)
(* 5. a local storage for blocks.                                           *)
(***************************************************************************)


\* Each ByzValidator has a local round number (initially 0) 
VARIABLE RoundOf

\* The rough type for RoundOf
RoundOfTypeOK == RoundOf \in [ByzValidator -> Nat]

\* "assert" INIT => \A v \in ByzValidator : RoundOf[v] = 0
RoundOfINIT ==      \A v \in ByzValidator : RoundOf[v] = 0


\* Each Worker has a local pool of unprocessed batches (initially {})
VARIABLE BatchPool

\* The rough type for BatchPool
BatchPoolTypeOK == BatchPool \in [Worker -> SUBSET Batch]

\* "assert" INIT => \A w \in Worker : BatchPool[w] = {}
BatchPoolINIT == \A w \in Worker : BatchPool[w] = {}



\* Primaries have pools of hashes for the next block (initially {}) 
VARIABLE NextHashes

\* The rough type of NextHashes
NextHashesTypeOK == NextHashes \in [Primary -> SomeHashes]

\* "assert" INIT => \A p \in Primary : NextHashes[p] = {}
NextHashesINIT == \A p \in Primary : NextHashes[p] = {}


\* Each ByzValidator has storage for batch hashes (initially {})
VARIABLE StoredHashes

\* The rough type of StoredHashes
StoredHashesTypeOK == StoredHashes \in [ByzValidator -> SUBSET BatchHash]

\* "assert" INIT => \A v \in ByzValidator : StoredHashes[v] = {}
StoredHashesINIT == \A v \in ByzValidator : StoredHashes[v] = {}


\* Each ByzValidator has storage for blocks (initially {}) 
VARIABLE StoredBlocks
\* The rough type of StoredBlocks
StoredBlocksTypeOK == StoredBlocks \in [ByzValidator -> SUBSET Block]

\* "assert" INIT => \A v \in ByzValidator : StoredBlocks[v] = {}
StoredBlocksINIT == \A v \in ByzValidator : StoredBlocks[v] = {}

\* The combined INIT-predicate
LocalStateINIT ==
  /\ RoundOfINIT \* 1.
  /\ BatchPoolINIT \* 2. 
  /\ NextHashesINIT \* 3. 
  /\ StoredHashesINIT \* 4. 
  /\ StoredBlocksINIT  \* 5. 
\* end of "LOCAL STATE"

=============================================================================
