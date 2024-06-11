------------------------ MODULE AbstractMempoolSpec -------------------------

(***************************************************************************)
(* The module "AbstractMempoolSpec" spec is the most abstract spec for the *)
(* mempool.  The main property is inclusion fairness, i.e., each request   *)
(* for inclusion in the mempool DAG will be served.                        *)
(***************************************************************************)

EXTENDS Integers, Functions, FiniteSets

\* The ephemeral mempool consists of transaction candidates,
\* sent to some worker.
\* The TLA spec does abstract away from the "enveloping" requests. 
CONSTANT TxCandidate

\* There are an an (at most) countable number of transaction candidates.
ASSUME CountableTxCandidateAssumption == Bijection(TxCandidate, Nat) # {}

\* The single variable of the spec is the "mempool" set,
\* containing the submitted transaction candidates.
VARIABLE mempool 

\* Initially, the "mempool" is empty.
Init == mempool = {}

\* In one step, we can add exactly one finite set of requests;
\* this ensures there _can_ be more request than can be
\* responded to "instantly".
\* This action will always be enabled for some suitable choice of X.
Next(X) ==
  \* type check
  /\ X \subseteq TxCandidate
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
SomeNext == \E X \in SUBSET TxCandidate : Next(X)

-----------------------------------------------------------------------------

(***************************************************************************)
(* We make the following fairness assumption/requirement: every finite set *)
(* of requests that all have not been served yet will be served.           *)
(***************************************************************************)

\* Eventual execution of Next(X) amounts to its eventual disabling
\* as we cannot add the same transaction candidate twice.
EventualInclusion == \A X \in SUBSET TxCandidate : <>~ENABLED(Next(X))

\* The spec is the conjuction of Init, EventualInclusion, and SomeNext.
Spec == 
  /\ Init
  /\ EventualInclusion
  /\ [][SomeNext]_mempool
  
=============================================================================
