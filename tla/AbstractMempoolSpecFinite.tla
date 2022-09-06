--------------------- MODULE AbstractMempoolSpecFinite ----------------------

(*
The module "AbstractMempoolSpecFinite" 
is a finite “prefix” of "AbstractMempoolSpec". 
*)

EXTENDS
  Integers
  ,
  Functions
  ,
  FiniteSets
  ,
   TLC

\* All possible atomic payload items form the "Payload" set. 
CONSTANT 
  \* @type: Set(PAYLOAD);
  Payload

\*\* There are a countable number of payload items to be served.
\*ASSUME CountablePayloadAssumption == Bijection(Payload, Nat) # {}
ASSUME FinitePayloadAssumption == IsFiniteSet(Payload)

\* The single variable of the spec is the "mempool" set.
VARIABLE
  \* @type: Set(PAYLOAD);
   mempool 

\* Initially, the "mempool" is empty.
Init ==
  mempool = {}

(*
\* 
Next(X) ==
  \* type check
  /\ X \subseteq Payload
  /\ IsFiniteSet(X)
  \* precondition
  /\ X # {} \* disregarding empty additions 
  /\ X \cap mempool = {} \* this condition is important !
  \* postcondition
  /\ mempool' = mempool \cup X 
  (*/\ PrintT(<<"added ",X,"in state",mempool,"reaching state",mempool'>>)*)
*)

(*
In one step, we can add exactly one finite set of requests.
Enabled for one suitable choice of X,
unless all Payload items have been processed. 
*)

NextPre(X) ==
  \* type check
  /\ X \subseteq Payload
  /\ IsFiniteSet(X)
  \* precondition
  /\ X # {} \* disregarding empty additions 
  /\ X \cap mempool = {} \* this condition is important !
  

  
PossibleNextPayloads == 
  { Z \in SUBSET Payload : NextPre(Z)}

\* the actual next action 
NextAct(X) == 
  /\ mempool' = mempool \cup X
  /\ NextPre(X) 


(*
The condition "X \cap mempool = {}" makes sure that we
do not “accidentally” add a transaction twice to the mempool.
*)

\* The “postcondition” "mempool' = mempool \cup X" ensures that
\* there is exactly one instance of NextAct(X) leading to a state change. 
Next == 
  \/ \E X \in PossibleNextPayloads : NextAct(X)
  \/ UNCHANGED mempool
  

DONE ==
  \* precondition
  mempool = Payload

-----------------------------------------------------------------------------

(***************************************************************************)
(* We make the following fairness assumption/requirement: every finite set *)
(* of requests that all have not been served yet will be served.           *)
(***************************************************************************)


\* Eventual execution of NextAct(X) amounts to its eventual disabling 
EventualInclusion == 
  \A X \in SUBSET Payload : WF_mempool(NextAct(X))

\* The spec is the conjuction of Init, EventualInclusion, and SomeNext.
Spec == 
  /\ Init
  /\ EventualInclusion
  /\ [][Next]_mempool

THEOREM <>(ENABLED DONE)
  
=============================================================================
