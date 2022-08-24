------------------------------- MODULE DAGpool ------------------------------

(*
In short, DAGpool is the specification of
the properties
Narwhal and Tusk aims for, plus censorship resistance. 
However, questions of availability are not explicitly mentioned. 

A DAGpool “is” (more precisely, refines to) a mempool, consisting of a growing
(1) DAG---nodes of which are blocks / block headers---
(2) a sequence of _apex_ nodes
(3) a partial proposed-by map from nodes to validators
subject to the following conditions,
relative to a fixed set of Byzantinve validators and quorum data:
(a) every node has a time-independent _depth_, defined as the maximal length of all outgoing paths
(b) for any natural number $n$, the proposed-by map is injective when restricted to nodes of depth $n$
(c) every node of non-maximal depth (at any point in time) has a quorum of incoming edges, i.e., there is a quorum such that its proposed blocks at maximal depth 
*)

EXTENDS 
  FiniteSets 
  ,
  Integers
  ,
  Functions
  ,
  WorkersOfPrimaries

\* The set of payloads. 
 
CONSTANT 
  \* @type: Set(PAYLOAD);
  Payload


(*
A _block_ consists of
1. a payload
2. a quorum (indirectly referencing existing previous blocks)
3. a set of validtor-depth pairs (weak-links to orphaned blocks), possibly empty
*)

\* @typeAlias: weakLink = <<Int, BYZ_VAL>> ;


CONSTANT
  \* @type: BYZ_VAL;
  noValidator

ASSUME noValidatorAssumption == noValidator \notin ByzValidator


\* @type: Set(BYZ_VAL);
noQuorum == {noValidator}

\* @type: Set(Set(BYZ_VAL));
QuorumOption == ByzQuorum \cup {noQuorum}



\* @typeAlias: weakLink = <<Int, BYZ_VAL>> ; 
\* 
\* @typeAlias: block = { 
\*   txs : PAYLOAD, 
\*   links : Set(BYZ_VAL),
\*   winks : Set($weakLink),
\*   height : Int
\* };
\* 
\* @type: Set($block); 
Block == [
  txs : Payload,
  links : QuorumOption,
  winks : SUBSET (Nat \X ByzValidator),
  height : Nat
]

\* @type: Set(BYZ_VAL -> $block); 
DAGlayerZero == UNION  { 
  {
    f \in [X -> Block] : \A q \in X : 
                            /\ f[q].links = noQuorum 
                            /\ f[q].winks = {}     
                            /\ f[q].height = 0                 
  }
  : X \in SUBSET ByzValidator
} 

==== 
generateDAGlayer[n \in Nat] == 

VARIABLES
  \* @type: $block
  

(*
On the DAG:
the DAG will be layered such that each node as a unique natural number _depth_,
which can be defined as the longest outgoing path;
this is well-defined as the graph is moreover loop-free.
Moreover, each node has (at least) a quorum of outgoing edges,
references to previous blocks.
The final condition on the DAG structure is that

  1. each _layer_ of the DAG has at most one node per (Byzantine) validator 

  2. each node of a (correct) validator will reference
     a quorum of blocks in the previous round, 
     encoded by a subset of Byzantine validators, 
     such that all validators in the set actually have block in 
     the previous round
 
  3. finally, each block contains a (finite set of) payload items
*)



(*
Consensus is abstracted out by a weakly fair choice of leader blocks
with enough support
such that the hight of chosen leader blocks is strictly increasing.   

*)



(*

\* The _“sequence”_ of all batches that are chosen (at points in time).
VARIABLES
  dag 

====
