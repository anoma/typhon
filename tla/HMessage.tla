------------------------------ MODULE HMessage ------------------------------
EXTENDS Naturals, FiniteSets, Functions, HQuorum, HLearner


CONSTANT LastBallot
ASSUME LastBallot \in Nat

Ballot == Nat

CONSTANT Value
ASSUME ValueNotEmpty == Value # {}

-----------------------------------------------------------------------------
(* Messages *)

CONSTANT MaxRefCardinality
ASSUME MaxRefCardinalityAssumption ==
    /\ MaxRefCardinality \in Nat
    /\ MaxRefCardinality >= 1

\*RefCardinality == Nat
RefCardinality == 1..MaxRefCardinality

FINSUBSET(S, R) == { Range(seq) : seq \in [R -> S] }
\*FINSUBSET(S, K) == { Range(seq) : seq \in [1..K -> S] }
\*FINSUBSET(S, R) == UNION { {Range(seq) : seq \in [1..K -> S]} : K \in R }

-----------------------------------------------------------------------------
(* Non-message value *)
NoMessage == [ type |-> "null" ]

MessageRec0 ==
    [ type : {"1a"}, bal : Ballot, prev : {NoMessage}, ref : {{}} ]

MessageRec1(M, n) ==
    M \cup
    [ type : {"1b"},
      acc : Acceptor,
      prev : M \cup {NoMessage},
      ref : FINSUBSET(M, RefCardinality) ] \cup
    [ type : {"2a"},
      lrn : SUBSET Learner,
      acc : Acceptor,
      prev : M \cup {NoMessage},
      ref : FINSUBSET(M, RefCardinality) ]

MessageRec[n \in Nat] ==
    IF n = 0
    THEN MessageRec0
    ELSE MessageRec1(MessageRec[n-1], n)

CONSTANT MaxMessageDepth
ASSUME MaxMessageDepth \in Nat

MessageDepthRange == Nat

Message == UNION { MessageRec[n] : n \in MessageDepthRange }

-----------------------------------------------------------------------------
(* Transitive references *)

\* Bounded transitive references
TranBound0 == [m \in Message |-> {m}]
TranBound1(tr, n) ==
    [m \in Message |-> {m} \cup UNION {tr[r] : r \in m.ref}]

TranBound[n \in Nat] ==
    IF n = 0
    THEN TranBound0
    ELSE TranBound1(TranBound[n-1], n)

\* Countable transitive references
TranDepthRange == MessageDepthRange

Tran(m) == UNION {TranBound[n][m] : n \in TranDepthRange}

-----------------------------------------------------------------------------
(* Transitive references of prev *)

\* Bounded transitive references of prev
PrevTranBound0 == [m \in Message |-> {m}]
PrevTranBound1(tr, n) ==
    [m \in Message |-> {m} \cup IF m.prev = NoMessage THEN {} ELSE tr[m.prev]]

PrevTranBound[n \in Nat] ==
    IF n = 0
    THEN PrevTranBound0
    ELSE PrevTranBound1(PrevTranBound[n-1], n)

\* Countable transitive references of prev
PrevTranDepthRange == MessageDepthRange

PrevTran(m) == UNION {PrevTranBound[n][m] : n \in PrevTranDepthRange}

=============================================================================
\* Modification History
\* Last modified Tue May 14 16:44:16 CEST 2024 by karbyshev
\* Created Tue May 14 16:39:44 CEST 2024 by karbyshev
