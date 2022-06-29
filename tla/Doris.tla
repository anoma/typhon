                        ---- MODULE Doris ----
(***************************************************************************)
(* This is the TLA-specification of the Doris mempool.  The Doris mempool  *)
(* is based on the Narwhal mempool with Tusk as consensus as described by  *)
(* Danezis,  Kokoris Kogias, Sonnino, and                                  *)
(*  Spiegelman in their                                                    *)
(* `^\href{https://arxiv.org/abs/2105.11827}{paper}^'.  Further            *)
(* inspiration is taken from                                               *)
(* `^\href{https://arxiv.org/abs/2102.08325}{DAG-rider}^', which in turn   *)
(* is a precursor to Narwhal.                                              *)
(*                                                                         *)
(* We shall refer to these papers as [N&T] and [DAG-R].                    *) 
(***************************************************************************)

EXTENDS Functions, Integers

\* For the module "Functions", we rely on the
\* `^\href{https://tinyurl.com/2ybvzsrc}{Community Module.}^'

-----------------------------------------------------------------------------

(***************************************************************************)
(*                             GENERAL SETUP                               *)
(***************************************************************************)

(***************************************************************************)
(* We make the usual assumption about Byzantine failures.  That is,        *)
(* besides a partially synchronous network, we have                        *)
(*                                                                         *)
(* - a total number of validators N = 3f+1                                 *)
(*                                                                         *)
(* - of which less than one third exhibit Byzantine behaviour.             *)
(*                                                                         *)
(* In this setting,                                                        *)
(*                                                                         *)
(* - a "quorum" is any set that contains more than two thirds of all       *)
(* nodes;                                                                  *)
(*                                                                         *)
(* - a "weak quorum" is a set of nodes whose intersection with any quorum  *)
(*   is non-empty.                                                         *)
(***************************************************************************)

\* Following Lamport's 
\* `^\href{https://tinyurl.com/2dyuzs6y}{formalization of Paxos}^' and 
\* `^\href{https://tinyurl.com/7punrbs2}{Byzantine Paxos}^',
\* we consider a more general formalization that
\* even can take care of infinite sets.

CONSTANTS Validator,     \* The set of non-faulty (aka good) validators.
          FakeValidator, \* The set of possibly faulty (aka bad) validators.
          ByzQuorum,
            (***************************************************************)
            (* A Byzantine quorum is set of validators that includes a     *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* validators and f bad ones, a Byzantine quorum is any set of *)
            (* 2f+1 validators.                                            *)
            (***************************************************************)
          WeakQuorum
            (***************************************************************)
            (* A weak quorum is a set of validators that includes at least *)
            (* one good one.  If there are f bad validators, then a weak   *)
            (* quorum is any set of f+1 validators.                        *)
            (***************************************************************)

(***************************************************************************)
(*  ByzValidator is the (disjoint) union of real or fake validators        *)
(*  (See BQA below)                                                        *)
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
(* Based on Lamport's assumption for liveness.                             *)
(***************************************************************************)
ASSUME BQLA ==
          /\ \E Q \in ByzQuorum : Q \subseteq Validator
          /\ \E W \in WeakQuorum : W \subseteq Validator

-----------------------------------------------------------------------------

(***************************************************************************)
(* One idea of Narwhal is explicit parallelism via a number of workers.    *)
(* This set is a public parameter, typically finite.  There is no point of *)
(* using invalid indices by bad validators as these would be ignored.      *)
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

Primary == ByzValidator \* co-extensional sets 

\* END of "GENERAL SETUP"

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

\* The following is a definition of a set of several BatchHashes
SomeHashes == BatchHash

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

AckBunch == UNION {[Q -> Ack] : Q \in ByzQuorum} \* a "bunch" of acks

AckByzQuorum ==
    { ax \in AckBunch : /\ (\A v,w \in DOMAIN ax :               
                            /\ ax[v].digest = ax[w].digest       
                            /\ ax[v].rnd = ax[w].rnd             
                            /\ ax[v].creator = ax[w].creator)    
                            /\ \A v \in DOMAIN ax : ax[v].sig = v
    }

\* The last conjuct "\A v \in DOMAIN ax : ax[v].sig = v" implies that 
\* we actually have distinct acknowledgments of the same digest,
\* making ax an injection


\* LEMMA \A ax \in AckByzQuorum : IsInjective(ax) \* TODO

(***************************************************************************)
(* An AckByzQuorum is essentially a Certificate of availability.  We thus  *)
(* define an alias and provide commodity functions for reading the fields  *)
(* of the contained acknowledgments, which must all agree on the digest,   *)
(* round, and creator.                                                      *)
(***************************************************************************)

Certificate == AckByzQuorum

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

EmptySet == {}
CertBuch == UNION {[Q -> Certificate] : Q \in ByzQuorum \cup {EmptySet}}

CertQuorum ==
    { cq \in CertBuch : \A v,w \in DOMAIN cq :
          /\ cq[v].rnd = cq[w].rnd                   
          /\ (v /= w => cq[v].digest /= cq[w].digest)
    }

WeakLinks == UNION {[Q -> Certificate] : Q \in SUBSET ByzValidator }



BlockStructure ==
    { b \in [ creator : ByzValidator, \* the block proposer
              rnd :     Nat, \* the round of the block proposal
              bxh :     SomeHashes, \* the batch hashes of the block
              cq :      CertQuorum, \* a CoA-quorum
              wl :      WeakLinks, \* possibly weak links             
              sig :     ByzValidator \* criators signature
            ] :
      /\ b.creator = b.sig \* on redundancy: cf. note on signatures
      /\ \A l \in DOMAIN b.wl : getRnd(b.wl[l]) < b.rnd-1 \* weak (!) links 
      /\ \/ /\ b.rnd = 0 \* either round zero and
            /\ DOMAIN b.cq = EmptySet \* empty domain allowed
         \/ /\ b.rnd > 0 \* or round non-zero and
            /\ DOMAIN b.cq \in ByzQuorum \* a proper domain
            /\ \A Q \in DOMAIN b.cq : b.cq[Q].rnd = (b.rnd - 1)
    }

ASSUMPTION BSA == (Block = BlockStructure)
=============================================================================
