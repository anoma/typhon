                        ---- MODULE Doris ----
(***************************************************************************)
(* This is the TLA-specification of the Doris mempool.  The Doris mempool  *)
(* is based on the Narwhal mempool with Tusk as consensus as described by  *)
(* George Danezis, Eleftherios Kokoris Kogias, Alberto Sonnino, and        *)
(* Alexander Spiegelman in their                                           *)
(* `^\href{https://arxiv.org/abs/2105.11827}{paper}^'.  Further            *)
(* inspiration is taken from                                               *)
(* `^\href{https://arxiv.org/abs/2102.08325}{DAG-rider}^', which in turn   *)
(* is a precursor to Narwhal.                                              *)
(***************************************************************************)
EXTENDS Functions 

\* For the module "Functions", we rely on the
\* `^\href{https://tinyurl.com/2ybvzsrc}{Community Module}^'

-----------------------------------------------------------------------------

(***************************************************************************)
(*                             GENERAL SETUP                               *)
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
         [h \in {"hash"} |-> b]
        ] 

\* The set of hashes of any possibly batch is the range of "hash".
BatchHash == Range(hash)


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

=============================================================================
