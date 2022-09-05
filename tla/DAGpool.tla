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

\* a single non-validator node (for encoding of partial functions)
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
(*     possibly empty                                                      *)
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
  winks : {{}}, \* SUBSET (Nat \X ByzValidator),
  height : Nat
]


(***************************************************************************)
(* The DAG to be built is encoded as                                       *)
(*                                                                         *)
(* - a list of `layers` where                                              *)
(*                                                                         *)
(* - a layer is (partial) function from validators to blocks               *)
(***************************************************************************)

VARIABLE
  \* @type: Seq(BYZ_VAL -> $block);
  dag 
  
(***************************************************************************)
(* Within the dag, we have choices of leader block, reminiscent of Tusk.   *)
(* The leader block is encoded as a pair of the block height and the       *)
(* proposing validator.                                                    *)
(***************************************************************************)
VARIABLE    
  \* @type: Seq(<<Int, BYZ_VAL>>);
  leaderBlocks

vars == <<dag, leaderBlocks>>


    
(*
CONSTANT
  \* @type: BYZ_VAL -> $block;
  emptyLayer

ASSUME emptyLayerEmpty == DOMAIN emptyLayer = {}
*)

emptyLayer == CHOOSE f \in [{} -> Block] : TRUE


(***************************************************************************)
(* Initially,                                                              *)
(*                                                                         *)
(* - the DAG consists of an empty layer and                                *)
(*                                                                         *)
(* - no leader blocks are chosen                                           *)
(***************************************************************************)
\* @type: Bool;
Init == dag = << emptyLayer >>  /\ leaderBlocks = <<  >>
    

(***************************************************************************)
(* For block addition, we distinguish the following three scenarios:       *)
(*                                                                         *)
(* - adding a block at genesis layer                                       *)
(*                                                                         *)
(* - adding the first block of a new layer (not the genesis layer)         *)
(*                                                                         *)
(* - adding an additional block to an already existing layer (not the      *)
(* genesis layer                                                           *)
(***************************************************************************)

(***************************************************************************)
(* We use the following operator to add a layer; it could also be used to  *)
(* "overwrite" an existing binding.                                        *)
(***************************************************************************)
\* @type: (BYZ_VAL -> $block,BYZ_VAL, $block) => BYZ_VAL -> $block;
UpdatedEntryInLayer(l, v, b) == 
  [ x \in {v} \cup DOMAIN l |-> 
       IF x = v
       THEN b
       ELSE l[x]
  ] 



(***************************************************************************)
(* Adding blocks to the genesis layer.                                     *)
(***************************************************************************)

\* @type: (BYZ_VAL, $block) => Bool;
AddBlockInGenesisLayer(v, b) == 
  LET
    dagLen == Len(dag)
    extendedLayer == UpdatedEntryInLayer(dag[1], v, b) 
  IN
  \* pre-condition
  \* - no previous blocks, so no links
  /\ b.links = noQuorum
  \* - no block proposed yet
  /\ v \notin DOMAIN dag[1]  
  \* post-condition
  \* - add the layer at genesis (depth 1)
  /\ dag' = [dag EXCEPT ![1] = extendedLayer]

(***************************************************************************)
(* Adding a block in a new layer                                           *)
(***************************************************************************)

\* @type: (BYZ_VAL, $block) => Bool;
AddBlockInNewLayer(v, b) == 
  LET
    dagLen == Len(dag)
    newLayer == [ x \in {v} |-> b ]
  IN 
    \* pre-condition 
    /\ b.links # noQuorum
    /\ b.links \subseteq DOMAIN dag[dagLen]
    \* weak links are purely optional 
    \* post-condition
    /\ dag' = dag \o << newLayer >> 

(***************************************************************************)
(* Adding blocks in a higher layer                                         *)
(***************************************************************************)

\* @type: (BYZ_VAL, $block, Int) => Bool;
AddBlockInHigherLayer(v, b, n) == 
  LET
    dagLen == Len(dag)
    extendedLayer == UpdatedEntryInLayer(dag[n], v, b) 
  IN
  \* pre-condition
  /\ b.links # noQuorum
  /\ n \in DOMAIN dag
  /\ v \notin DOMAIN dag[n]  
  /\ b.links \subseteq DOMAIN dag[n-1]
  \* post-condition
  /\ dag' = [dag EXCEPT ![n] = extendedLayer]
                         
(***************************************************************************)
(* Combining the block addition into a single operator.                    *)
(***************************************************************************)
  
\* @type: (BYZ_VAL, $block, Int) => Bool;
AddBlock(v, b, n) == 
/\ \/ /\ n < 1 
      /\ FALSE \* we do not do anything for n < 1
   \/ /\ n = 1 
      /\ AddBlockInGenesisLayer(v, b)
   \/ /\ n \in 2..Len(dag)
      /\ AddBlockInHigherLayer(v, b, n) 
   \/ /\ n = Len(dag)+1 
      /\ AddBlockInNewLayer(v, b) 
   \/ /\ n > Len(dag)+1
      /\ FALSE \* we do not do anything for n > Len(dag)
/\ UNCHANGED leaderBlocks
     


(*
The following operator makes a narrow description of 
the possible blocks that a validator _v_ could propose 
at layer _n_
*)
CurrentBlockCandidates(n, v) == 
IF n = 1
THEN 
[
  txs : Payload,
  links : {noQuorum},
  winks : {{}}, \* SUBSET (Nat \X ByzValidator),
  height : {1}
]
ELSE
[
  txs : Payload,
  links : {Q \in ByzQuorum : Q \subseteq DOMAIN dag[n-1]},
  winks : {{}}, \* SUBSET (Nat \X ByzValidator),
  height : {n}
]
 
(*
Adding a block. 
*)

\* @type: Bool;
NewBlock == 
  \E n \in 1..(Len(dag)+1) :
  \E v \in IF n = (Len(dag)+1)
           THEN ByzValidator
           ELSE ByzValidator \ DOMAIN dag[n]:           
  \E b \in CurrentBlockCandidates(n,v) :  AddBlock(v, b, n)
  
(***************************************************************************)
(* Leader block selection: we allow for a sequence of leader blocks        *)
(*                                                                         *)
(* - at most one per layer                                                 *)
(*                                                                         *)
(* - and the depth of leader blocks has to increase.                       *)
(***************************************************************************)
  
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
    /\ W \subseteq DOMAIN dag[n+1]
    /\ \A w \in W : v \in dag[n+1][w].links 
  \* post-condition
    /\ leaderBlocks' = leaderBlocks \o << << n, v >> >>  
    /\ UNCHANGED dag

(***************************************************************************)
(* The Lamport-esque Next .                                                *)
(***************************************************************************)
Next == 
  \/ NewBlock
  \/ ChooseSupportedLeaderBlock


\* ChooseArbitraryLeaderBlock == 'soon ™' \* not really needed/wanted

\* 
CensorshipResistance == 
 \A v \in ByzValidator : \A b \in Block : \A n \in Nat :
   WF_vars( AddBlock(v, b, n) )

Spec == Init /\ [][Next]_vars /\ CensorshipResistance
         
         
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
