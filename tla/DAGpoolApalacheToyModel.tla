---- MODULE DAGpoolApalacheToyModel ----

EXTENDS Apalache

(* Quorums.tla specific *)

CONSTANT
  \* @type: Set(BYZ_VAL);
  MCValidator

CONSTANT
  \* @type: Set(BYZ_VAL);
  MCFakeValidator

CONSTANT
  \* @type: Set(Set(BYZ_VAL));
  MCByzQuorum

CONSTANT
  \* @type: Set(Set(BYZ_VAL));
  MCWeakQuorum

(* WorkersOfPrimaries.tla specific *)

CONSTANT
  \* @type: Set(WORKER_INDEX);
  MCWorkerIndex \* a publicy known set of indices

(* DAGpool.tla specific *)

CONSTANT 
  \* @type: Set(PAYLOAD);
  MCPayload

CONSTANT
  \* @type: BYZ_VAL;
  MCnoValidator


\* @typeAlias: weakLink = <<Int, BYZ_VAL>> ; 
\* 
\* @typeAlias: block = { 
\*   txs : PAYLOAD, 
\*   links : Set(BYZ_VAL),
\*   winks : Set($weakLink),
\*   height : Int
\* };

\* @type: $block; 
dummyBlock == [ 
  txs |-> "x_OF_PAYLOAD", 
  links |-> {MCnoValidator}, 
  winks |-> {},
  height |-> 1
]

CONSTANT
  \* @type: BYZ_VAL -> $block;
  MCemptyLayer

VARIABLE
  \* @type: Seq(BYZ_VAL -> $block);
  dag 

VARIABLE    
  \* @type: Seq(<<Int, BYZ_VAL>>);
  leaderBlocks

INSTANCE DAGpool WITH
  \* (* Quorums specific *)
  Validator <- MCValidator, 
  FakeValidator <- MCFakeValidator,
  ByzQuorum <- MCByzQuorum,
  WeakQuorum <- MCWeakQuorum,
  \* (* WorkersOfPrimaries specific *)
  WorkerIndex <- MCWorkerIndex,
  \* (* DAGpool specific *)
  Payload <- MCPayload,
  noValidator <- MCnoValidator, 
  emptyLayer <- MCemptyLayer 


ConstInit == 
  \* (* Quorums specific *)
  /\ MCValidator = { "1_OF_BYZ_VAL", "2_OF_BYZ_VAL", "3_OF_BYZ_VAL" }
  /\ MCFakeValidator = { "4_OF_BYZ_VAL" }
  /\ MCByzQuorum = {{"1_OF_BYZ_VAL", "2_OF_BYZ_VAL", "3_OF_BYZ_VAL"}, {"1_OF_BYZ_VAL", "2_OF_BYZ_VAL", "4_OF_BYZ_VAL"}, {"1_OF_BYZ_VAL", "3_OF_BYZ_VAL", "4_OF_BYZ_VAL"}, {"2_OF_BYZ_VAL", "3_OF_BYZ_VAL", "4_OF_BYZ_VAL"}}
  /\ MCWeakQuorum = {{"1_OF_BYZ_VAL", "2_OF_BYZ_VAL"}, {"1_OF_BYZ_VAL", "3_OF_BYZ_VAL"}, {"1_OF_BYZ_VAL", "4_OF_BYZ_VAL"}, {"2_OF_BYZ_VAL", "3_OF_BYZ_VAL"}, {"2_OF_BYZ_VAL", "4_OF_BYZ_VAL"}, {"3_OF_BYZ_VAL", "4_OF_BYZ_VAL"}}
  \* (* WorkersOfPrimaries specific *)
  /\ MCWorkerIndex = {"1_OF_WORKER_INDEX"}
  \* (* DAGpool specific *)
  /\ MCPayload = {"x_OF_PAYLOAD"}
  /\ MCnoValidator = "none_OF_BYZ_VAL"
  /\ MCemptyLayer = SetAsFun({})

====
