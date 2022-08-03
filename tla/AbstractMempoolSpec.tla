------------------------ MODULE AbstractMempoolSpec -------------------------

(***************************************************************************)
(* The module "AbstractMempoolSpec" spec is the most abstract spec for the *)
(* mempool.  The main property is censorship resistance.                   *)
(***************************************************************************)

EXTENDS Integers, Functions, FiniteSets

\* All possible atomic payload items form the "Payload" set. 
CONSTANT Payload

\* There are a countable number of payload items to be served.
ASSUME CountablePayloadAssumption == Bijection(Payload, Nat) # {}

\* The single variable of the spec is the "mempool" set.
VARIABLE mempool 

\* Initially, the "mempool" is empty.
Init == mempool = {}

\* In one step, we can add exactly one finite set of requests.
\* Always enabled for one suitable choice of X.
Next(X) ==
  \* type check
  /\ IsFiniteSet(X)
  \* precondition
  /\ X # {} \* disregarding empty additions 
  /\ X \cap mempool = {} \* this condition is important !
  \* postcondition
  /\ mempool' = mempool \cup X 

(*
The condition "X \cap mempool = {}" makes sure that we
do not “accidentally” add a transaction twice to the mempool.
*)

\* The “postcondition” "mempool' = mempool \cup X" ensures that
\* there is exactly one instance of Next(X) leading to a state change. 
SomeNext ==  \E X \in SUBSET Payload : Next(X)

-----------------------------------------------------------------------------

(***************************************************************************)
(* We make the following fairness assumption/requirement: every finite set *)
(* of requests that all have not been served yet will be served.           *)
(***************************************************************************)

Fairness == \A X : WF_mempool(Next(X))

\* The spec is the conjuction of Init, Fairness, and SomeNext.
Spec == 
  /\ Init
  /\ Fairness
  /\ [][SomeNext]_mempool
  
=============================================================================
