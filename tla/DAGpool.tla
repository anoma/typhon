------------------------------- MODULE DAGpool ------------------------------

(***************************************************************************)
(* In short, DAGpool is the specification of the properties Narwhal and    *)
(* Tusk aims for, plus censorship resistance.  However, questions of       *)
(* availability are not explicitly mentioned.                              *)
(*                                                                         *)
(* A DAGpool “is” (more precisely, refines to) a mempool, consisting of a  *)
(* growing                                                                 *)
(*                                                                         *)
(* (1) DAG---nodes of which are blocks / block headers---                  *)
(*                                                                         *)
(* (2) a sequence of _apex_ nodes, aka leader blocks                       *)
(*                                                                         *)
(* (3) a partial proposed-by map from nodes to validators                  *)
(*                                                                         *)
(* subject to the following conditions, relative to a fixed set of         *)
(* Byzantinve validators and quorum data:                                  *)
(*                                                                         *)
(* (a) every node has a time-independent _depth_, defined as the maximal   *)
(* length of all outgoing paths                                            *)
(*                                                                         *)
(* (b) for any natural number $n$, the proposed-by map is injective when   *)
(* restricted to nodes of depth $n$                                        *)
(*                                                                         *)
(* (c) every node of non-maximal depth (at any point in time) has a quorum *)
(* of incoming edges, i.e., there is a quorum such that its proposed       *)
(* blocks at maximal depth references the node.                            *)
(***************************************************************************)

EXTENDS 
  Sequences
  , 
  FiniteSets
  ,
  Integers
  ,
  Functions
  ,
  WorkersOfPrimaries
  ,
  TLC

\* The set of payloads. 
 
CONSTANT 
  \* @type: Set(PAYLOAD);
  Payload


\* @typeAlias: weakLink = <<Int, BYZ_VAL>> ;

CONSTANT
  \* @type: BYZ_VAL;
  noValidator

ASSUME noValidatorAssumption == noValidator \notin ByzValidator


\* @type: Set(BYZ_VAL);
noQuorum == {noValidator}

\* @type: Set(Set(BYZ_VAL));
QuorumOption == ByzQuorum \cup {noQuorum}


(***************************************************************************)
(* A _block_ consists of                                                   *)
(*                                                                         *)
(* 1.  a payload                                                           *)
(*                                                                         *)
(* 2.  a quorum (indirectly referencing existing previous blocks)          *)
(*                                                                         *)
(* 3.  a set of validtor-depth pairs (weak-links to orphaned blocks),      *)
(* possibly empty                                                          *)
(***************************************************************************)

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
  winks : {}, \* {{}} \cup {{x} : x \in (Nat \X ByzValidator)}, 
  \* was `SUBSET (Nat \X ByzValidator),`
  height : Nat
]

(*
\* @type: Set(BYZ_VAL -> $block); 
DAGlayersZero == UNION  { 
  {
    f \in [X -> Block] : \A x \in X : 
                            /\ f[x].links = noQuorum 
                            /\ f[x].winks = {}     
                            /\ f[x].height = 0
  }
  : X \in SUBSET ByzValidator
} 
*)

(*
\* @type: Int -> Set(BYZ_VAL -> $block); 
generateDAGlayers[n \in Nat] == 
  IF n = 0 
  THEN DAGlayersZero
  ELSE UNION {
  {
    f \in [X -> Block] : \A x \in X :
                               /\ f[x].links \in ByzQuorum
                               /\ \A w \in f[x].winks : 
                                        /\ w[1] \in Nat
                                        /\ n > 0 => w[1] < n-1 
                               /\ f[x].height = n
  }
  : X \in SUBSET ByzValidator
}
*)

(*    
\* @type: Int -> Set(Seq(BYZ_VAL -> $block));
generateDAGs[n \in Nat] == 
  IF n = 0 
  THEN {<< layer >> : layer \in generateDAGlayers[0]}
  ELSE LET 
    candidates == { short \o << layer >> : 
                     short \in generateDAGs[n-1], 
                     layer \in generateDAGlayers[n]
                 }
  IN { g \in candidates:
         \* all links present 
         /\ \A b \in Range(g[n]) : b.links \subseteq DOMAIN g[n-1]
         \* all winks present
         /\ FALSE \* TODO
  }
*)


VARIABLES
  \* @type: Seq(BYZ_VAL -> $block);
  dag 
  ,     
  \* @type: Seq(<<Int, BYZ_VAL>>);
  leaderBlocks

vars == <<dag, leaderBlocks>>


    

CONSTANT
  \* @type: BYZ_VAL -> $block;
  emptyLayer

ASSUME emptyLayerEmpty == DOMAIN emptyLayer = {}


\* emptyLayer == CHOOSE f \in [{} -> Block] : TRUE

\* @type: Bool;
Init == 
  /\ dag = << emptyLayer >>  
  /\ leaderBlocks = <<  >>
    

(* 
Adding a block in a new layer,
either in the last layer or in a new layer
- preconditions; no block proposed yet, references to previous blocks 
*)

\* @type: (BYZ_VAL -> $block,BYZ_VAL, $block) => BYZ_VAL -> $block;
UpdatedEntryInLayer(l, v, b) == 
  [ x \in {v} \cup DOMAIN l |-> 
       IF x = v
       THEN b
       ELSE l[x]
  ] 

\* @type: (BYZ_VAL, $block) => Bool;
AddBlockInGenesisLayer(v, b) == 
  LET
    dagLen == Len(dag)
    extendedLayer == UpdatedEntryInLayer(dag[1], v, b) 
  IN
  \* pre-condition
  /\ v \notin DOMAIN dag[1]  
  /\ b.links = noQuorum
  \* post-condition
  /\ dag' = [dag EXCEPT ![1] = extendedLayer]

\* @type: (BYZ_VAL, $block, Int) => Bool;
AddBlockInHigherLayer(v, b, n) == 
  LET
    dagLen == Len(dag)
    extendedLayer == UpdatedEntryInLayer(dag[n], v, b) 
  IN
  \* pre-condition
  /\ n > 1
  /\ n <= dagLen
  /\ v \notin DOMAIN dag[n]  
  /\ b.links # noQuorum
  /\ b.links \subseteq DOMAIN dag[n-1]
  \* post-condition
  /\ dag' = [dag EXCEPT ![n] = extendedLayer]
                         
\* @type: (BYZ_VAL, $block) => Bool;
AddBlockInNewLayer(v, b) == 
  LET
    dagLen == Len(dag)
    newLayer == [ x \in {v} |-> b ]
  IN 
    \* pre-condition 
    /\ b.links # noQuorum
    /\ b.links \subseteq DOMAIN dag[dagLen]
    \* weak links are purely 
    \* post-condition
    /\ dag' = dag \o << newLayer >> 
\* LeaderBlockSelection

  
\* @type: (BYZ_VAL, $block, Int) => Bool;
AddBlock(v, b, n) == 
  /\ n < 1 
     => FALSE \* we do not do anything for n < 1
  /\ n = 1 
     => AddBlockInGenesisLayer(v, b)
  /\ (n > 1 /\ n <= Len(dag))
     => AddBlockInHigherLayer(v, b, n) 
  /\ (n > 1 /\ n = Len(dag)) 
     => AddBlockInNewLayer(v, b) 
  /\ (n > 1 /\ n > Len(dag)) 
     => FALSE \* we do not do anything for n > Len(dag)
  /\ UNCHANGED leaderBlocks
     
\* @type: Bool;
NewBlock == 
  \E v \in ByzValidator : 
  \E b \in Block : 
  \E n \in 1..(Len(dag)+1) : AddBlock(v, b, n)
  
ChooseSupportedLeaderBlock == 
  LET
    dagLen == Len(dag)
    lastLeaderHeight == 
      IF Len(leaderBlocks) = 0
      THEN 0 
      ELSE leaderBlocks[Len(leaderBlocks)][1]
  IN         
  \* pre-condition
  \E n \in (lastLeaderHeight+1)..(dagLen-1) :
  \* the validator owning the candidate leader block 
  \E v \in DOMAIN dag[n] : \* v has proposed 
  \* we are looking for supporting validators in the next layer
  \E W \in WeakQuorum :
  /\ \A w \in W : v \in dag[n+1][w].links 
  \* post-condition
  /\ leaderBlocks' = leaderBlocks \o << << n, v >> >>  
  /\ UNCHANGED dag

Next == 
  \/ NewBlock
  \/ ChooseSupportedLeaderBlock

\* ChooseArbitraryLeaderBlock == 'soon ™'

CensorshipResistance == 
 \A v \in ByzValidator : \A b \in Block : \A n \in Nat :
   WF_vars( AddBlock(v, b, n) )

Spec == Init /\ /\ [][Next]_vars /\ CensorshipResistance
         
         
========
  

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


====
