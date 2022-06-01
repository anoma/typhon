------------------------------ MODULE Narwhal -------------------------------
EXTENDS Naturals, FiniteSets, Functions, Sequences

-----------------------------------------------------------------------------

(* This is the specification of the Narwhal mempool *)
(* as described by *)
(* George Danezis, Eleftherios Kokoris Kogias, *)
(* Alberto Sonnino, and Alexander Spiegelman *)
(* in their paper [https://arxiv.org/abs/2105.11827]*)


-----------------------------------------------------------------------------

(* BEGIN of `General Setup` *)


(* -----------------------------------------------------------------------------*)
(*			    GENERAL SETUP                                   *)
(* -----------------------------------------------------------------------------*)


(* For the purposes of the formal verification, *)
(* hash functions need to be treated in a peculiar manner, *)
(* for the simple reason that collisions are not strictly impossible. *)
(* (After all, we are interested in qualitative properties, *)
(* as opposed to probabilitstic ones.) *)

(* The set of batches. *)
CONSTANT Batch
ASSUME Batch # {}

(* This is one specifically simple way to represent hash functions *)

hash == [
	 b \in Batch
	 |->
	 ["hash" |-> b]
	 ]

--------------------------------------------------------------------------------

(* Narwhal makes the usual assumption about Byzantine failures. *)
(* That is, besides a partially synchronous network, we have *)
(* - a total number of validators of the form N >= 3f+1 where *)
(* - at most f validators are erroneous *)
(* Moreoer,
(* - a _quorum_ is any set that contains more than 2/3-rds of all nodes *)
(* - a _weak quorum_ is a set of nodes s.t. it intersection with any quorum is non-empty *)

(* In fact, we can generalize this to infinite sets of validators *)

CONSTANT Validator

CONSTANTS Quorum, WQuorum

ASSUME QuorumAssumptions ==
        /\ Quorum \subseteq (SUBSET Validator)
        /\ WQuorum \subseteq (SUBSET Validator)
        /\ Quorum \subseteq WQuorum
        /\ \A W \in WQuorum :		                     
             /\ (Validator \ W) \notin Quorum
             /\ \E V \in WQuorum : (V \cup W) \in Quorum
        /\ \A X \in SUBSET Validator :
           \/ X \in WQuorum
	   \/ (Validator \ X) \in WQuorum

\* LEMMA \A Q \in Quorum \A W \in WQuorum : Q \cap W \neq {} 

CONSTANTS CorrectValidator, ByzValidator

ASSUME ValidatorAssumption ==
        /\ CorrectValidator \cap ByzValidator = {}
        /\ CorrectValidator \cup ByzValidator = Validator
        /\ CorrectValidator \in Quorum

\* LEMMA ByzValidator \notin WQuorum

--------------------------------------------------------------------------------

(* One idea of Narwhal is explicit parallelism via a number of workers *)

CONSTANT WorkerIndex

ASSUME IsFiniteSet(WorkerIndex)

(* A specific worker has a worker index and a validator *)

Worker == WorkerIndex \X Validator

(* To avoid silly bugs (swaping first and second component of Worker *)

ASSUME WorkerIndex \cap Validator = {} /\ Worker \cap Validator = {}

(* There is a bijection between Validators and Primaries *)
(* We can just identify them for the purpose of the specification *)

Primary == Validator

(* END of `General Setup` *)

--------------------------------------------------------------------------------

(* BEGIN of `Data Structures` *)

(* -------------------------------------------------------------------------------- *)
(*			  Data Structures                                           *)
(* -------------------------------------------------------------------------------- *)

(* The data structures for blocks, certificates and the like are essentially *)
(* the ones described in the Narwhal paper in *)
(* but with batches instead of transactions *)

(* Note: On signatures *)
(* The effect of signatures will have to be modelled by *
(* a set of constraints on the messages that Byzantine nodes can send *)
(* E.g., all messages will have a sender *)

(* The set of Hashes of blocks, called digest to avoid *)
(* accidental confusion *) 
CONSTANT BlockDigest

(* "If a block is valid, *)
(* the other validators store it and acknowledge it by *)
(* signing its _block digest_, _round number_, and _creator’s identity_." *)
(* (In most cases, the signature will not be the creator, but could be.) *)
Ack == [digest : BlockDigest,
	creator : Validator,
	rnd : Nat,
	sig : Validator]

(* "Once the creator gets 2𝑓 + 1 distinct acknowledgments for a block, *)
(* it combines them into a certificate of block availability, that includes *)
(* the block digest, current round, and creator identity." *)

(* We first make precise what >= "2𝑓 + 1 distinct acknowledgments" are *)
(* and we make explicit that they talk about the same block digest *)
AckQuorum == { ax \in UNION {[Q -> Ack] : Q \in Quorum} :
	       /\ \A v,w \in DOMAIN ax :
	          /\ ax[v].digest = ax[w].digest 
                  /\ ax[v].rnd = ax[w].rnd 	       
	          /\ ax[v].creator = ax[w].creator
	       /\ \A v \in DOMAIN ax : ax[v].sig = v
	       }
(* The second conjuct "\A v \in DOMAIN ax : ax[v].sig = v" implies that *)
(* we actually have distinct acknowledgments of the same digest *)

\*LEMMA DistinctAcknowledgments

(* Now, a Certificate is just an AckQuorum with the core info copied once, *)
(* viz. the digest, round number and the creator id *)
Certificate == { c \in [digest : BlockDigest,
			rnd : Nat,
			creator : Validator,
			aq : AckQuorum ] :
		 \A v \in DOMAIN aq :
		 /\ digest = aq[v].digest 
                 /\ rnd = aq[v].rnd 		 
                 /\ creator = aq[v].creator 		 
		 }		 

(* A valid block must *)
(* 1. contain a valid signature from its creator, *)
(* 2. be at the local round 𝑟 of the validator checking it, *)
(* 3. be at round 0 (genesis), or *)
(*    contain certificates for at least 2𝑓 + 1 blocks of round 𝑟 − 1, *)
(* 4. be the first one received from the creator for round 𝑟 . *)

(* We first mode  "certificates for at least 2𝑓 + 1 blocks" *)

CertQuorum == { cq \in UNION {[Q -> Certificate] : Q\in Quorum \cup {} } :
		\A v,w \in DOMAIN cq :
		/\ cq[v].rnd = cq[w].rnd
		/\ (v /= w => cq[v].digest /= cq[w].digest)
		}
(* It should follow that also the creators are different *)

\* LEMMA 

(* Blocks are now defined easily, *)
(* given the above representation of sets of certificates of availability. *)

Block == { b \in [ creator : Validator,
		   rnd : Nat,
		   bxh : Seq(BatchHash),
		   cq  : CertQuorum,
		   sig : Validator		   
		   ] :
	   /\ \/ (b.rnd = 0 /\ DOMAIN cq = {})
	      \/ (b.rnd > 0 /\ \A Q \in DOMAIN cq : Q \in Quorum /\ cq[Q].rnd = (b.rnd - 1))
           /\ b.creator = b.sig
	   }	   

(* For hashing blocks *)
ASSUME Injection(Block, BlockDigest) /= {}
blockHash == CHOOSE v : v \in Injection(Block, BlockDigest)
  
(* END of `Data Structures` *)    

--------------------------------------------------------------------------------
(* BEGIN of `Local State` *)

(*--------------------------------------------------------------------------------*)
(*			     Local State                                      *)
(*--------------------------------------------------------------------------------*)

(* Each Validator has a local round number (initially 0) *)

VARIABLE valRounds

RoundsTypeOK == valRounds \in [Validator -> Nat]

(* Each Worker has a batch queue (initially empty) *)
(* Each Primary has a queue of batchHashes (initially empty)*)

VARIABLES batchQueues, hashQueues

QueuesTypeOK == /\ batchQueues \in [Worker -> Seq(Batch)]
                /\ hashQueues \in [Primary -> Seq(BatchHash)]
    
(* END of `Local State` *)
  
--------------------------------------------------------------------------------


(* BEGIN of `Message Structure` *)  
(* -------------------------------------------------------------------------------- *)
(*			  Message Structure                                   *)
(* -------------------------------------------------------------------------------- *)


(* Following Lamport's specification of Paxos *)
(* [https://bit.ly/3a6ydfc], *)
(* we use a set of (broadcast) messages, that all nodes can access *)
(* *)       
(* There are the following types of message.
(* - "newB" a new batch arriving **at** a specific worker *)
(* - "bcB" broadcast a batch, **from** a worker (to workers of the same index) *)
(* - "hashB" a worker sends a (received) batch to its primary for block production *)
(* - "block" a block creator broadcasts a new block (and its batches) *)
(* - "ack" acknowledgment of a broadcast new block *by* a Validator  *)
(* - "cert" broadcasting a certificate from a validator  *)    


Message == 
       [type : {"newB"}, batch : Batch, at : Worker]
  \cup [type : {"bcB"}, batch : Batch, from : Worker] 
  \cup [type : {"hashB"}, h : Hash, worker : Worker] 
  \cup [type : {"block"}, block: Block, creator : Validator]
  \cup [type : {"ack"}, ack : Ack, by : Validator]
  \cup [type : {"cert"}, cert : Certificate, from : Validator]

(* END of `Message Structure` *)
  
--------------------------------------------------------------------------------
  

  (*			      Variables                                         *)

\* VARIABLES msgs

\* TypeOK == msg

(* -------------------------------------------------------------------------------- *)
(*			  Actions                                    *)
(* -------------------------------------------------------------------------------- *)





