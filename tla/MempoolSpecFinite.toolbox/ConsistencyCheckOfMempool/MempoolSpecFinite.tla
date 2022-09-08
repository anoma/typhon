--------------------- MODULE MempoolSpecFinite ------------------------------

(*
This is a finite version of the "MempoolSpec". 
*)

EXTENDS
  FiniteSets
  ,
  Integers
  ,
  Functions
  , 
  TLC
  , 
  Quorums
  , 
  WorkersOfPrimaries

-----------------------------------------------------------------------------

(*
For the finite version of MempoolSpec.tla,
we assume a finite validator set.
*)
ASSUME FiniteValidators == IsFiniteSet(ByzValidator)

(*
We also work with in the usual 3f+1 setting,
i.e., f out of 3f+1 validators are faulty. 
*)

TheF == Cardinality(FakeValidator)

ASSUME ByzQuorumStandard ==
  ByzQuorum = { X \in  SUBSET ByzValidator : Cardinality(X) = 1 + 2 * TheF }
  
ASSUME WeakQuorumStandard == 
  WeakQuorum = { X \in  SUBSET ByzValidator : Cardinality(X) = 1 + TheF }


(***************************************************************************)
(*                           ON BATCHES                                    *)
(***************************************************************************)

(*
We phrase the specification in terms of batches.
Single transactions will be covered in a refined spec.
*)

\* The set of PAYLOAD is "inherited" from the top level spec
CONSTANT
  \* @type: Set(PAYLOAD);
  Payload

\* For the finite model, we assume that the Payload set is finite.
ASSUME AssumeFinitePayload == IsFiniteSet(Payload)

\* the alsways useful empty set
EmptySet == {}

\* We want to think of each payload as a batch (sometimes).
Batch == Payload

-----------------------------------------------------------------------------

(* ON REQUESTS *)

(*
We want to consider all possible requests at workers.
Requests are modelled as a function
that assigns to each worker a finite set of batches. 
*)
\* @typeAlias: request = $worker->Set(PAYLOAD);
\* @type: ($request) => Bool;
RequestConstr(r) == 
  /\ DOMAIN r = Worker
  /\ UNION Range(r) = Batch
  \* /\ EmptySet \notin Range(r) 
  /\ \A w1,w2 \in Worker : w1 # w2 => r[w1] \cap r[w2] = {}


\* @type: Set($worker->Set(PAYLOAD));
ValidRequests == 
  { r \in [Worker -> (SUBSET Batch)] : RequestConstr(r) }
  
\* compared to the top level spec, this is a refinement of the state space

-----------------------------------------------------------------------------

(***************************************************************************)
(*                             THE SPEC                                    *)
(***************************************************************************)

(***************************************************************************)
(* We use the very same idea of Lamport's consensus specification.  In     *)
(* particular, we do not yet require any DAG structure, but just a set of  *)
(* chosen batches, growing and eventually including all batches.           *)
(***************************************************************************)

\* @type: Int;
N == Cardinality(Batch)

\* @type: Set(Int);
NN == 1..N

\* The _sequence_ of all batches that are chosen (at points in time).
VARIABLE
  \* @type: Int -> Set(PAYLOAD);
  chosenSet
VARIABLE
  \* @type: $worker -> Set(PAYLOAD);
  requestFct

allvars == <<chosenSet, requestFct>>

\* A first approximation of chosenSet's type
TypeOK ==
  /\ chosenSet \in [NN -> SUBSET Batch]
  /\ \A n \in NN : IsFiniteSet(chosenSet[n])


(***************************************************************************)
(* The 'Init' predicate describes the unique initial state of 'chosenSet'. *)
(***************************************************************************)

InitialRequests == ValidRequests

Init == 
  /\ chosenSet = [n \in NN \cup {N + 1} |-> {}]
  /\ requestFct \in InitialRequests

(* DONE ≃ TERMINATE *)
DONE == UNION { chosenSet[n] : n \in NN } = Batch


(***************************************************************************)
(* The next-state relation 'Next' describes how the variable 'chosenSet'   *)
(* can change from one step to the next.  Note that 'Next' is enabled      *)
(* (equals true for some next value chosenSet' of chosenSet) if and only   *)
(* if chosenSet equals the empty set.                                      *)
(***************************************************************************)




\* the "Next" action of workers w \in ws injecting (range of) Xs

\* @type: ($request) => Set(Int);
NextPreWitnesses(Xs) == { n \in NN : 
  LET 
    ws == DOMAIN Xs
    newRequests == UNION Range(Xs)
  IN 
    \* type check                                                     
    /\ ws \subseteq Worker                                            
    /\ \A w \in ws : Xs[w] \subseteq requestFct[w]                    
    \* precondition                                                   
    /\ chosenSet[n] = {}                                              
    /\ \A m \in NN : m < n => /\ chosenSet[m] # {}                    
    /\ newRequests \cap UNION { chosenSet[k] : k \in 1..n } = EmptySet
  }



\* @type: ($request) => Bool;
Next(Xs) == 
  LET
    newRequests == UNION Range(Xs)
  IN
    /\ Cardinality(NextPreWitnesses(Xs)) = 1
    /\ \E n \in NextPreWitnesses(Xs):
          chosenSet' = [chosenSet EXCEPT ![n] = newRequests]
    /\ UNCHANGED requestFct


\* the infinite disjunction of all possible instances of the "Next" action
SomeNext == 
  \/ /\ \E ws \in SUBSET Worker : 
        \E Xs \in [ws -> (SUBSET Batch)]: 
           Next(Xs) 
     /\ UNCHANGED requestFct
  \/ /\ DONE
     /\ UNCHANGED allvars

(***************************************************************************)
(* The TLA+ temporal formula that specifies the system evolution.          *)
(***************************************************************************)


\* Weak fairness for Next actions
InclusionFairness ==
  \A ws \in SUBSET Worker :
  \A Xs \in [ws -> (SUBSET Batch) \ {EmptySet}] :
     WF_allvars(Next(Xs))

Spec == Init /\ [][SomeNext]_allvars /\ InclusionFairness

====


-----------------------------------------------------------------------------

(***************************************************************************)
(*                            Refinement                                   *)
(***************************************************************************)

MempoolProjection ==
  INSTANCE AbstractMempoolSpec WITH 
    mempool <- UNION { chosenSet[n] : n \in NN }

\* 
THEOREM Spec => MempoolProjection!Spec

=============================================================================
