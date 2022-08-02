------------------------ MODULE AbstractMempoolSpec -------------------------

(***************************************************************************)
(* The module 'AbstractMempoolSpec' spec is the most abstract spec for the *)
(* mempool.  The main property is censorship resistance.                   *)
(***************************************************************************)

EXTENDS Integers, Functions, FiniteSets

\* We have a set, whose elements are making up the complete payload.
CONSTANT Payload

\* There are a countable number of requests to be served.
ASSUME AssumeCountablePayload == \E f \in Bijection(Payload, Nat) : TRUE


\* The single variable of the spec is the mempool set.
VARIABLE mempool 

\* Initially, the mempool is empty.
INIT == mempool = {}

\* In one step, we can add any finite set of requests.
NEXT(X) ==
  \* essentially always enabled for some choice of X
  /\ IsFiniteSet(X)
  /\ X # {}
  /\ X \cap mempool = {} \* this condition is debatable ! 
  \* postcondition
  /\ mempool' = mempool \cup X 
  
(***************************************************************************)
(* We make the following fairness assumption/requirement: every finite set *)
(* of requests that all have not been served will be eventually served, at *)
(* least partially.                                                        *)
(***************************************************************************)

FAIRNESS == \A X : IsFiniteSet(X) => WF_mempool(NEXT(X))

\* The spec is the conjuction of INIT, FAIRNESS, and always some next step.
SPEC == 
  /\ INIT
  /\ FAIRNESS
  /\ [][\E X : NEXT(X)]_mempool
  
=============================================================================
