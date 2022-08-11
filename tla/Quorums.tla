----------------------------- MODULE Quorums --------------------------------

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

CONSTANTS
  \* The set of non-faulty (aka good) validators.
  \* @type: Set(BYZ_VAL);
  Validator,
  \* The set of possibly faulty (aka bad, malicious) validators.
  \* @type: Set(BYZ_VAL);
  FakeValidator, 
  \* @type: Set(Set(BYZ_VAL));
  ByzQuorum,
    (***************************************************************)
    (* A Byzantine quorum is set of validators that includes a     *)
    (* quorum of good ones.  In the case that there are 2f+1 good  *)
    (* validators and f bad ones, any set that contains at least   *)
    (* 2f+1 validators is a Byzantine quorum.                      *)
    (***************************************************************)
  \* @type: Set(Set(BYZ_VAL));
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

=============================================================================
