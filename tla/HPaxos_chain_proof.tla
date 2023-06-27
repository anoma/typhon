------------------------- MODULE HPaxos_chain_proof -------------------------
EXTENDS HPaxos_chain, Sequences, NaturalsInduction, WellFoundedInduction, TLAPS

-----------------------------------------------------------------------------
LEMMA RefCardinalitySpec ==
    /\ RefCardinality \in SUBSET Nat
    /\ RefCardinality # {}
PROOF BY MaxRefCardinalityAssumption DEF RefCardinality

LEMMA FinSubset_sub ==
    ASSUME NEW S, NEW R \in SUBSET Nat, NEW F \in FINSUBSET(S, R)
    PROVE  F \subseteq S
PROOF BY DEF Range, FINSUBSET

LEMMA FinSubset_sub_nontriv ==
    ASSUME NEW S, S # {},
           NEW R \in SUBSET Nat, R # {}, NEW F \in FINSUBSET(S, R)
    PROVE  F # {}
PROOF BY Isa DEF Range, FINSUBSET

\*LEMMA FinSubset_sub ==
\*    ASSUME NEW S, NEW K \in Nat, NEW F \in FINSUBSET(S, K)
\*    PROVE  F \subseteq S
\*PROOF BY DEF Range, FINSUBSET

\*LEMMA FinSubset_finite ==
\*    ASSUME NEW S, NEW K \in Nat, NEW F \in FINSUBSET(S, K)
\*    PROVE  IsFiniteSet(F)
\*PROOF BY DEF FINSUBSET, IsFiniteSet, Range
\*
\*LEMMA IsFiniteSet_add ==
\*    ASSUME NEW S, IsFiniteSet(S), NEW x
\*    PROVE  IsFiniteSet(S \cup {x})
\*PROOF
\*<1> PICK seq \in Seq(S) : \A s \in S : \E n \in 1..Len(seq) : seq[n] = s
\*    BY DEF IsFiniteSet
\*<1> DEFINE f == [i \in 1..(Len(seq) + 1) |->
\*                    IF i < Len(seq) + 1 THEN seq[i] ELSE x]
\*<1> f \in Seq(S \cup {x}) OBVIOUS
\*<1> Len(f) = Len(seq) + 1 OBVIOUS
\*<1>1. SUFFICES ASSUME NEW s \in S \cup {x} PROVE \E i \in 1..Len(f) : f[i] = s
\*      BY Zenon DEF IsFiniteSet
\*<1>9. QED BY <1>1

-----------------------------------------------------------------------------
LEMMA TrustSafeSelfAgreement ==
    ASSUME NEW E \in TrustSafe
    PROVE  [from |-> E.from, to |-> E.from, q |-> E.q] \in TrustSafe
BY LearnerGraphAssumptionSymmetry, LearnerGraphAssumptionTransitivity, Zenon

LEMMA EntanglementSym ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent
    PROVE  <<L2, L1>> \in Ent
PROOF BY LearnerGraphAssumptionSymmetry DEF Ent

LEMMA EntanglementSelf ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent
    PROVE  <<L1, L1>> \in Ent
PROOF BY LearnerGraphAssumptionSymmetry,
         LearnerGraphAssumptionTransitivity, Zenon DEF Ent

LEMMA EntanglementTrustLive ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW Q1 \in ByzQuorum, NEW Q2 \in ByzQuorum,
           <<L1, L2>> \in Ent,
           [lr |-> L1, q |-> Q1] \in TrustLive,
           [lr |-> L2, q |-> Q2] \in TrustLive
    PROVE  \E N \in SafeAcceptor : N \in Q1 /\ N \in Q2
PROOF BY LearnerGraphAssumptionValidity DEF Ent

LEMMA EntaglementTrustLiveNonEmpty ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW Q \in ByzQuorum,
           <<L1, L2>> \in Ent,
           [lr |-> L1, q |-> Q] \in TrustLive
    PROVE  \E N \in SafeAcceptor : N \in Q
PROOF BY EntanglementTrustLive, EntanglementSelf, Zenon

LEMMA EntanglementTransitive ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, NEW L3 \in Learner,
           <<L1, L2>> \in Ent, <<L2, L3>> \in Ent
    PROVE  <<L1, L3>> \in Ent
PROOF BY LearnerGraphAssumptionTransitivity DEF Ent

-----------------------------------------------------------------------------
(* Messages *)

LEMMA MessageRec_def ==
    MessageRec = [n \in Nat |->
                    IF n = 0
                    THEN MessageRec0
                    ELSE MessageRec1(MessageRec[n-1], n)]
PROOF BY NatInductiveDef
      DEF NatInductiveDefHypothesis, NatInductiveDefConclusion, MessageRec

LEMMA Message_spec ==
    /\ \A n \in Nat : MessageRec[n] \subseteq Message
    /\ \A m \in Message : \E n \in Nat : m \in MessageRec[n]
PROOF BY DEF Message, MessageDepthRange

LEMMA MessageRec_eq0 == MessageRec[0] = MessageRec0
PROOF BY MessageRec_def

LEMMA MessageRec_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  MessageRec[n] = MessageRec1(MessageRec[n-1], n)
PROOF BY MessageRec_def DEF MessageRec1

LEMMA MessageRec_monotone_1 ==
    ASSUME NEW n \in Nat
    PROVE  MessageRec[n] \subseteq MessageRec[n+1]
PROOF BY MessageRec_eq1 DEF MessageRec1

LEMMA MessageRec_monotone ==
    \A n, m \in Nat : n <= m => MessageRec[n] \subseteq MessageRec[m]
PROOF
<1> DEFINE P(m) == \A n \in Nat : n < m => MessageRec[n] \subseteq MessageRec[m]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
      BY <1>1, MessageRec_monotone_1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA MessageRec_nontriv ==
    \A n \in Nat : MessageRec[n] # {}
PROOF
<1> DEFINE P(m) == MessageRec[m] # {}
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0)
  <2> [type |-> "1a", bal |-> 0, prev |-> NoMessage, ref |-> {}] \in MessageRec[0]
      BY MessageRec_eq0 DEF MessageRec0, Ballot
  <2> QED OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> QED BY <1>1, MessageRec_eq1 DEF MessageRec1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA MessageRec_ref0 ==
    ASSUME NEW m \in MessageRec[0]
    PROVE  m.ref = {}
PROOF BY MessageRec_eq0 DEF MessageRec0

LEMMA MessageRec_ref1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  \A m \in MessageRec[n] : m.ref \subseteq MessageRec[n-1]
PROOF
<1> DEFINE P(j) == j # 0 =>
                \A mm \in MessageRec[j] : mm.ref \subseteq MessageRec[j-1]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> SUFFICES ASSUME NEW mm \in MessageRec[m+1]
               PROVE  mm.ref \subseteq MessageRec[m]
      OBVIOUS
  <2>1. CASE m = 0
        BY <2>1, MessageRec_eq1, MessageRec_ref0, FinSubset_sub,
           MaxRefCardinalityAssumption
           DEF MessageRec1, RefCardinality
  <2>2. CASE m # 0
        BY <1>1, <2>2, MessageRec_eq1, MessageRec_monotone, FinSubset_sub,
           MaxRefCardinalityAssumption
           DEF MessageRec1, RefCardinality
  <2>3. QED BY <2>1, <2>2
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_nontriv == Message # {}
PROOF BY MessageRec_nontriv DEF Message, MessageDepthRange

LEMMA Message_1a_ref ==
    \A m \in Message : m.type = "1a" <=> m.ref = {}
PROOF
<1> DEFINE P(j) == \A mm \in MessageRec[j] : mm.type = "1a" <=> mm.ref = {}
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF Message, MessageDepthRange
<1>0. P(0) BY MessageRec_eq0 DEF MessageRec0
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> SUFFICES ASSUME NEW mm \in MessageRec[m+1]
               PROVE  mm.type = "1a" <=> mm.ref = {}
      BY DEF Message
  <2>3. QED BY <1>1, MessageRec_eq1, MessageRec_nontriv, FinSubset_sub_nontriv,
               RefCardinalitySpec DEF MessageRec1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_ref ==
    ASSUME NEW m \in Message
    PROVE  m.ref \subseteq Message
PROOF BY MessageRec_ref0, MessageRec_ref1, Message_spec DEF MessageDepthRange

LEMMA MessageRec_min ==
    ASSUME NEW m \in Message
    PROVE  \E n \in Nat :
            /\ m \in MessageRec[n]
            /\ \A k \in 0 .. n - 1 : m \notin MessageRec[k]
PROOF
<1>1. DEFINE P(k) == m \in MessageRec[k]
<1>2. SUFFICES \E n \in Nat :
                /\ P(n)
                /\ \A k \in 0 .. n - 1 : ~P(k)
      OBVIOUS
<1>3. PICK n1 \in Nat : P(n1) BY Message_spec
<1>4. HIDE DEF P
<1>5. QED BY <1>3, SmallestNatural, Isa

LEMMA Message_ref_acyclic ==
    ASSUME NEW m \in Message
    PROVE  m \notin m.ref
PROOF
<1>0. PICK n \in Nat :
        /\ m \in MessageRec[n]
        /\ \A k \in 0 .. n-1 : m \notin MessageRec[k]
      BY MessageRec_min
<1>1. CASE n = 0 BY <1>0, <1>1, MessageRec_eq0 DEF MessageRec0
<1>2. CASE n # 0 /\ m \in m.ref
  <2>1. m.ref \in SUBSET MessageRec[n-1]
        BY <1>0, <1>2, MessageRec_eq1, FinSubset_sub, MaxRefCardinalityAssumption
        DEF MessageRec1, RefCardinality
  <2>10. QED BY <2>1, <1>0, <1>2
<1>10. QED BY <1>1, <1>2

\*LEMMA Message_ref_acyclic_2 ==
\*    ASSUME NEW m1 \in Message, NEW m2 \in m1.ref
\*    PROVE  m1 \notin m2.ref
\*PROOF
\*<1> SUFFICES ASSUME NEW x \in Message,
\*                    NEW y \in x.ref,
\*                    x \in y.ref
\*             PROVE  FALSE
\*    OBVIOUS
\*<1>0. PICK n \in Nat :
\*        /\ x \in MessageRec[n]
\*        /\ \A k \in 0 .. n-1 : x \notin MessageRec[k]
\*      BY MessageRec_min
\*<1>1. n # 0 BY <1>0, MessageRec_eq0 DEF MessageRec0
\*<1>2. y \in MessageRec[n - 1] BY MessageRec_ref1, <1>0, <1>1
\*<1>3. n - 1 # 0 BY <1>2, MessageRec_eq0 DEF MessageRec0
\*<1>4. n - 1 \in Nat BY <1>1, <1>3
\*<1>5. x \in MessageRec[n - 1 - 1] BY <1>2, <1>3, <1>4, MessageRec_ref1
\*<1>6. QED BY <1>5, <1>0, <1>3, <1>4

\*LEMMA XXX1 ==
\*    ASSUME NEW M \in SUBSET Message, IsFiniteSet(M),
\*           NEW A \in Acceptor 
\*    PROVE  [type |-> "1b", acc |-> A, ref |-> M] \in Message
\*PROOF
\*<1> PICK n \in Nat : \A m \in M : m \in MessageRec[n] BY Message_finite_1
\*<1> [type |-> "1b", acc |-> A, ref |-> M] \in MessageRec[n + 1]
\*    BY MessageRec_eq1 DEF MessageRec1
\*<1>10. QED

-----------------------------------------------------------------------------
LEMMA NoMessageIsNotAMessage ==
    NoMessage \notin Message
PROOF
<1> DEFINE P(n) == NoMessage \notin MessageRec[n]
<1> SUFFICES \A n \in Nat : P(n)
    BY DEF Message, MessageDepthRange
<1>0. P(0)
      BY MessageRec_eq0 DEF MessageRec0, NoMessage
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
      BY <1>1, MessageRec_eq1 DEF MessageRec1, NoMessage
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA MessageTypeSpec ==
    ASSUME NEW m \in Message
    PROVE \/ /\ m.type = "1a"
             /\ m.bal \in Ballot
             /\ m.prev = NoMessage
             /\ m.ref = {}
          \/ /\ m.type = "1b"
             /\ m.acc \in Acceptor
             /\ m.prev \in Message \cup {NoMessage}
             /\ m.ref # {}
             /\ m.ref \in SUBSET Message
          \/ /\ m.type = "2a"
             /\ m.lrn \in Learner
             /\ m.acc \in Acceptor
             /\ m.prev \in Message \cup {NoMessage}
             /\ m.ref # {}
             /\ m.ref \in SUBSET Message
PROOF
<1> DEFINE P(n) ==
        \A x \in MessageRec[n] :
            \/ /\ x.type = "1a"
               /\ x.bal \in Ballot
               /\ x.prev = NoMessage
               /\ x.ref = {}
            \/ /\ x.type = "1b"
               /\ x.acc \in Acceptor
               /\ x.prev \in Message \cup {NoMessage}
               /\ x.ref # {}
               /\ x.ref \in SUBSET Message
            \/ /\ x.type = "2a"
               /\ x.lrn \in Learner
               /\ x.acc \in Acceptor
               /\ x.prev \in Message \cup {NoMessage}
               /\ x.ref # {}
               /\ x.ref \in SUBSET Message
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY Message_spec
<1>0. P(0) BY MessageRec_eq0 DEF MessageRec0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  <2> SUFFICES ASSUME NEW x \in MessageRec[k + 1]
               PROVE  \/ /\ x.type = "1a"
                         /\ x.bal \in Ballot
                         /\ x.prev = NoMessage
                         /\ x.ref = {}
                      \/ /\ x.type = "1b"
                         /\ x.acc \in Acceptor
                         /\ x.prev \in Message \cup {NoMessage}
                         /\ x.ref # {}
                         /\ x.ref \in SUBSET Message
                      \/ /\ x.type = "2a"
                         /\ x.lrn \in Learner
                         /\ x.acc \in Acceptor
                         /\ x.prev \in Message \cup {NoMessage}
                         /\ x.ref # {}
                         /\ x.ref \in SUBSET Message
      OBVIOUS
  <2>1. CASE x \in MessageRec[k]
        BY <1>1, <2>1
  <2>2. CASE x \in [ type : {"1b"},
                     acc : Acceptor,
                     prev : MessageRec[k] \cup {NoMessage},
                     ref : FINSUBSET(MessageRec[k], RefCardinality) ]
        BY <2>2, Message_spec, MessageRec_nontriv, FinSubset_sub,
           FinSubset_sub_nontriv, RefCardinalitySpec
  <2>3. CASE x \in [ type : {"2a"},
                     lrn : Learner,
                     acc : Acceptor,
                     prev : MessageRec[k] \cup {NoMessage},
                     ref : FINSUBSET(MessageRec[k], RefCardinality) ]
        BY <2>3, Message_spec, MessageRec_nontriv, FinSubset_sub,
           FinSubset_sub_nontriv, RefCardinalitySpec
  <2> QED BY <1>1, <2>1, <2>2, <2>3, MessageRec_eq1 DEF MessageRec1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

-----------------------------------------------------------------------------
(* Transitive references *)

LEMMA TranBound_def ==
    TranBound = [n \in Nat |->
                    IF n = 0
                    THEN TranBound0
                    ELSE TranBound1(TranBound[n-1], n)]
PROOF BY NatInductiveDef
DEF NatInductiveDefHypothesis, NatInductiveDefConclusion, TranBound

LEMMA Tran_spec ==
    ASSUME NEW m \in Message
    PROVE  /\ \A n \in Nat : TranBound[n][m] \subseteq Tran(m)
           /\ \A r \in Tran(m) : \E n \in Nat : r \in TranBound[n][m]
PROOF BY DEF Tran, TranDepthRange, MessageDepthRange

LEMMA TranBound_eq0 ==
    TranBound[0] = [m \in Message |-> {m}]
PROOF BY TranBound_def DEF TranBound0

LEMMA TranBound_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  TranBound[n] =
            [m \in Message |-> {m} \cup UNION {TranBound[n-1][r] : r \in m.ref}]
PROOF BY TranBound_def, Zenon DEF TranBound1

LEMMA Tran_refl ==
    ASSUME NEW m \in Message PROVE m \in Tran(m)
PROOF BY TranBound_eq0 DEF Tran, TranDepthRange, MessageDepthRange

LEMMA Tran_eq ==
    ASSUME NEW m \in Message
    PROVE  Tran(m) = {m} \cup UNION { Tran(r) : r \in m.ref }
PROOF
<1>1. Tran(m) \subseteq {m} \cup UNION {Tran(r) : r \in m.ref}
  <2> SUFFICES ASSUME NEW x \in Tran(m)
               PROVE  x \in {m} \cup UNION {Tran(r) : r \in m.ref}
      OBVIOUS
  <2> PICK n \in Nat : x \in TranBound[n][m]
      BY Tran_spec
  <2> CASE n = 0
      BY TranBound_eq0
  <2> CASE n # 0
    <3> CASE x # m
      <4> PICK r \in m.ref : x \in TranBound[n-1][r]
          BY TranBound_eq1, Isa
      <4> QED BY Tran_spec, MessageTypeSpec
    <3> QED OBVIOUS
  <2> QED OBVIOUS
<1>2. {m} \cup UNION {Tran(r) : r \in m.ref} \subseteq Tran(m)
  <2> SUFFICES ASSUME NEW x \in {m} \cup UNION {Tran(r) : r \in m.ref}
               PROVE  x \in Tran(m)
      OBVIOUS
  <2> CASE x # m
    <3> PICK r \in m.ref : x \in Tran(r)
        OBVIOUS
    <3> PICK n \in Nat : x \in TranBound[n][r]
        BY Tran_spec, MessageTypeSpec
    <3> (n + 1) - 1 = n OBVIOUS
    <3> x \in TranBound[n+1][m]
        BY TranBound_eq1, Isa
    <3> QED BY Tran_spec
  <2> QED BY Tran_refl
<1> QED BY <1>1, <1>2

LEMMA Tran_1a ==
    ASSUME NEW m \in Message, m.type = "1a"
    PROVE  Tran(m) = {m}
PROOF BY Tran_eq, MessageTypeSpec

LEMMA TranBound_Message ==
    ASSUME NEW m1 \in Message,
           NEW n \in Nat
    PROVE  TranBound[n][m1] \in SUBSET Message
PROOF
<1> DEFINE P(j) == \A x \in Message : TranBound[j][x] \in SUBSET Message
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF Tran
<1>0. P(0) BY TranBound_eq0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
  <2> SUFFICES ASSUME NEW x \in Message
               PROVE TranBound[k + 1][x] \in SUBSET Message
      OBVIOUS
  <2> SUFFICES ASSUME NEW r \in x.ref
               PROVE TranBound[k][r] \in SUBSET Message
      BY TranBound_eq1, Isa
  <2>2. r \in Message BY Message_ref
  <2>3. QED BY <1>1, <2>2
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Tran_Message ==
    ASSUME NEW m1 \in Message
    PROVE  Tran(m1) \in SUBSET Message
PROOF BY Tran_spec, TranBound_Message

LEMMA TranBound_monotone_1 ==
    ASSUME NEW n \in Nat, NEW m \in Message
    PROVE  TranBound[n][m] \subseteq TranBound[n+1][m]
PROOF
<1> DEFINE P(j) == \A mm \in Message :
                    TranBound[j][mm] \subseteq TranBound[j+1][mm]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) BY TranBound_eq0, TranBound_eq1, Isa
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
  <2> SUFFICES ASSUME NEW mm \in Message
               PROVE TranBound[k+1][mm] \subseteq TranBound[(k+1)+1][mm]
      OBVIOUS
  <2>1. SUFFICES
        UNION {TranBound[k][r] : r \in mm.ref} \subseteq
        UNION {TranBound[k+1][r] : r \in mm.ref}
        BY TranBound_eq1, Isa
  <2>6. QED BY <1>1, Message_ref
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA TranBound_monotone ==
    \A n, m \in Nat : n <= m =>
        \A mm \in Message :
            TranBound[n][mm] \subseteq TranBound[m][mm]
PROOF
<1> DEFINE P(m) == \A n \in Nat : n < m =>
                    \A mm \in Message : TranBound[n][mm] \subseteq TranBound[m][mm]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1) BY <1>1, TranBound_monotone_1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_ref_TranBound1 ==
    ASSUME NEW m1 \in Message
    PROVE  m1.ref \in SUBSET TranBound[1][m1]
PROOF
<1> SUFFICES ASSUME NEW x \in m1.ref PROVE x \in TranBound[1][m1]
    OBVIOUS
<1> x \in Message BY Message_ref
<1> QED BY TranBound_eq1, TranBound_eq0, Isa

LEMMA TranBound_trans ==
    ASSUME NEW n1 \in Nat, NEW n2 \in Nat,
           NEW m1 \in Message,
           NEW m2 \in TranBound[n1][m1],
           NEW m3 \in TranBound[n2][m2]
    PROVE  m3 \in TranBound[n1 + n2][m1]
PROOF
<1>0. DEFINE P(n) ==
        \A k \in Nat :
        \A x \in Message :
        \A y \in TranBound[n][x] :
        \A z \in TranBound[k][y] :
            z \in TranBound[n + k][x]
<1>1. SUFFICES \A n \in Nat : P(n) OBVIOUS
<1>2. P(0) BY TranBound_eq0
<1>3. ASSUME NEW n \in Nat, P(n) PROVE P(n+1)
  <2>1. SUFFICES ASSUME NEW k \in Nat, NEW x \in Message,
                            NEW y \in TranBound[n + 1][x], NEW z \in TranBound[k][y]
                 PROVE  z \in TranBound[n + 1 + k][x]
        OBVIOUS
  <2>2. CASE y = x BY <2>2, TranBound_monotone
  <2>3. CASE y \in UNION {TranBound[n][r] : r \in x.ref}
    <3>0. PICK r \in x.ref : y \in TranBound[n][r] BY <2>3
    <3>1. r \in Message BY Message_ref
    <3>2. z \in TranBound[n + k][r] BY <3>0, <3>1, <1>3
    <3>5. QED BY <3>0, <3>2, TranBound_eq1, Isa
  <2>10. QED BY <2>2, <2>3, TranBound_eq1, Isa
<1>4. HIDE DEF P
<1>5. QED BY <1>2, <1>3, NatInduction, Isa

LEMMA Tran_trans ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1), NEW m3 \in Tran(m2)
    PROVE  m3 \in Tran(m1)
PROOF
<1>0. PICK n1 \in Nat : m2 \in TranBound[n1][m1] BY Tran_spec
<1>1. PICK n2 \in Nat : m3 \in TranBound[n2][m2] BY TranBound_Message, Tran_spec
<1>2. m3 \in TranBound[n2 + n1][m1] BY TranBound_trans, <1>0, <1>1
<1>3. QED BY <1>2, Tran_spec

LEMMA Message_ref_Tran ==
    ASSUME NEW m \in Message
    PROVE  m.ref \subseteq Tran(m)
PROOF BY Message_ref_TranBound1, Zenon
      DEF Tran, TranDepthRange, MessageDepthRange

LEMMA MessageRec0_Tran ==
    ASSUME NEW m1 \in MessageRec[0], NEW m2 \in Tran(m1)
    PROVE  m1 = m2
PROOF
<1> m1 \in Message BY Message_spec DEF MessageDepthRange
<1> PICK k \in Nat : m2 \in TranBound[k][m1] BY Tran_spec
<1> m2 \in Message BY Tran_Message
<1>1. CASE k = 0 BY TranBound_eq0, <1>1
<1>2. CASE k # 0
  <2>1. CASE m2 \in UNION { TranBound[k - 1][r] : r \in m1.ref }
        BY <2>1, MessageRec_eq0 DEF MessageRec0
  <2>2. QED BY Isa, TranBound_eq1, <1>2, <2>1
<1>3. QED BY <1>1, <1>2

LEMMA MessageRec_Tran_bound ==
    ASSUME NEW n \in Nat, NEW m1 \in MessageRec[n], NEW m2 \in Tran(m1)
    PROVE  m2 \in MessageRec[n]
PROOF
<1> DEFINE P(l) == \A k \in Nat :
                   \A x \in MessageRec[k] :
                   \A y \in TranBound[l][x] :
                        y \in MessageRec[k]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j)
    BY Tran_spec, Message_spec DEF MessageDepthRange
<1>0. P(0) BY TranBound_eq0, Message_spec
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> SUFFICES ASSUME NEW k \in Nat,
                      NEW x \in MessageRec[k],
                      NEW y \in TranBound[m + 1][x]
               PROVE  y \in MessageRec[k]
      OBVIOUS
  <2> SUFFICES ASSUME k # 0 PROVE y \in MessageRec[k]
      BY MessageRec0_Tran DEF Tran, TranDepthRange, MessageDepthRange
  <2> x \in Message BY Message_spec
  <2>1. CASE y = x BY <2>1
  <2>2. CASE y \in UNION { TranBound[m][r] : r \in x.ref }
    <3>1. PICK r \in x.ref : y \in TranBound[m][r] BY <2>2
    <3>3. r \in MessageRec[k - 1] BY MessageRec_ref1
    <3>4. y \in MessageRec[k - 1] BY <3>3, <3>1, <1>1
    <3>5. QED BY <3>4, MessageRec_monotone
  <2>3. QED BY <2>1, <2>2, TranBound_eq1, Isa
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

\*LEMMA MessageRec_TranBound ==
\*    ASSUME NEW n \in Nat, NEW m1 \in MessageRec[n], NEW m2 \in Tran(m1)
\*    PROVE \E k \in Nat : k <= n /\ m2 \in TranBound[k][m1]
\*PROOF
\*<1> DEFINE P(l) == \A k \in Nat :
\*                   \A x \in MessageRec[k] :
\*                   \A y \in TranBound[l][x] :
\*                    \E k1 \in Nat : k1 <= k /\ y \in TranBound[k1][x]
\*<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF Tran
\*<1>0. P(0) BY TranBound_eq1, TranBound_eq1, MessageRec_eq0 DEF MessageRec0
\*<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
\*  <2> DEFINE E(k, x, y) == \E k1 \in Nat : k1 <= k /\ y \in TranBound[k1][x]
\*  <2> SUFFICES ASSUME NEW k \in Nat,
\*                      NEW x \in MessageRec[k],
\*                      NEW y \in TranBound[m + 1][x]
\*               PROVE E(k, x, y)
\*      BY MessageRec0_Tran DEF Tran
\*  <2> x \in Message BY Tran_Message DEF Message, Tran
\*  <2> y \in Tran(x) BY DEF Tran
\*  <2> SUFFICES ASSUME k # 0 PROVE E(k, x, y)
\*    <3>1. CASE k = 0
\*      <4>1. x = y BY <3>1, MessageRec0_Tran
\*      <4>2. WITNESS 0 \in Nat
\*      <4>3. QED BY TranBound_eq0, <4>1
\*    <3>2. QED BY <3>1
\*  <2>1. CASE y = x BY <2>1, TranBound_eq0
\*  <2>2. CASE y \in UNION { TranBound[m][r] : r \in x.ref }
\*    <3>1. PICK r \in x.ref : y \in TranBound[m][r] BY <2>2
\*    <3>3. r \in MessageRec[k - 1] BY MessageRec_ref1
\*    <3>4. PICK k2 \in Nat : k2 <= k - 1 /\ y \in TranBound[k2][r]
\*          BY <1>1, <3>1, <3>3
\*    <3>5. WITNESS k2 + 1 \in Nat
\*    <3>6. r \in TranBound[1][x] BY Message_ref_TranBound1, <3>1
\*    <3>10. QED BY <3>4, <3>6, TranBound_trans
\*  <2>4. HIDE DEF E
\*  <2>5. QED BY <2>1, <2>2, TranBound_eq1, Isa
\*<1>2. HIDE DEF P
\*<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Tran_ref_acyclic ==
    ASSUME NEW m \in Message, NEW r \in m.ref
    PROVE  m \notin Tran(r)
PROOF
<1> r \in Message BY Message_ref
<1> SUFFICES ASSUME NEW n \in Nat,
                    NEW x \in Message,
                    NEW y \in x.ref, x \in Tran(y)
             PROVE  x \in MessageRec[n] => FALSE
    BY DEF Message, MessageDepthRange
<1>0. PICK k \in Nat : /\ x \in MessageRec[k]
                       /\ \A k1 \in 0 .. k - 1 : x \notin MessageRec[k1]
      BY MessageRec_min
<1> SUFFICES ASSUME k # 0 PROVE FALSE
  <2>1. CASE k = 0 BY <1>0, <2>1, MessageRec_eq0 DEF MessageRec0
  <2>2. QED BY <2>1
<1>2. y \in MessageRec[k - 1] BY <1>0, MessageRec_ref1
<1>3. x \in MessageRec[k - 1] BY <1>2, MessageRec_Tran_bound
<1>4. QED BY <1>0, <1>3

LEMMA Tran_acyclic ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           m1 \in Tran(m2)
    PROVE  m1 = m2
PROOF
<1> PICK n \in Nat : m2 \in TranBound[n][m1] BY Tran_spec
<1> SUFFICES ASSUME n # 0 PROVE m1 = m2 BY TranBound_eq0
<1>1. CASE m1 = m2 BY <1>1
<1>2. CASE m2 \in UNION { TranBound[n - 1][r] : r \in m1.ref }
  <2> PICK r \in m1.ref : m2 \in TranBound[n - 1][r] BY <1>2
  <2> r \in Message BY Message_ref
  <2> m2 \in Tran(r) BY Tran_spec
  <2>1. m1 \in Tran(r) BY Tran_trans
  <2>2. QED BY <2>1, Tran_ref_acyclic
<1>3. QED BY <1>1, <1>2, TranBound_eq1, Isa

-----------------------------------------------------------------------------
LEMMA CaughtMsgSpec ==
    ASSUME NEW M \in Message
    PROVE  /\ CaughtMsg(M) \in SUBSET Message
           /\ \A X \in CaughtMsg(M) : X.type # "1a"
BY Tran_Message DEF CaughtMsg

-----------------------------------------------------------------------------
(* Facts about Get1a, B and V relations *)

LEMMA Get1a_TypeOK ==
    ASSUME NEW m \in Message
    PROVE  /\ Get1a(m) \subseteq Message
           /\ \A x \in Get1a(m) : x.bal \in Ballot
PROOF BY Tran_Message, MessageTypeSpec DEF Get1a

LEMMA Get1a_correct ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m), NEW y \in Get1a(m)
    PROVE  x.bal = y.bal
PROOF BY Tran_Message, MessageTypeSpec DEF Get1a, Ballot

LEMMA B_func ==
    ASSUME NEW m \in Message,
           NEW b1 \in Ballot, B(m, b1),
           NEW b2 \in Ballot, B(m, b2)
    PROVE  b1 = b2
PROOF BY DEF B, Get1a, Ballot

LEMMA B_def ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m)
    PROVE  \E b \in Ballot : B(m, b)
PROOF BY Get1a_correct, Get1a_TypeOK DEF B

LEMMA B_1a ==
    ASSUME NEW m \in Message, m.type = "1a"
    PROVE  B(m, m.bal)
PROOF BY MessageTypeSpec, Tran_1a DEF B, Get1a, Ballot

LEMMA V_func ==
    ASSUME NEW m \in Message,
           NEW v1 \in Value, V(m, v1),
           NEW v2 \in Value, V(m, v2)
    PROVE  v1 = v2
PROOF BY Get1a_correct DEF V

\*LEMMA V_def_1a ==
\*    ASSUME BVal \in [Ballot -> Value],
\*           NEW m \in Message, NEW x \in Get1a(m)
\*    PROVE V(m, BVal[x.bal])
\*PROOF BY Get1a_TypeOK DEF V

LEMMA V_def ==
    ASSUME BVal \in [Ballot -> Value],
           NEW m \in Message,
           NEW b \in Ballot, B(m, b)
    PROVE V(m, BVal[b])
PROOF BY Get1a_TypeOK DEF V, B

\*LEMMA B_V_inj ==
\*    ASSUME NEW m1 \in Message, NEW m2 \in Message,
\*           NEW b \in Ballot, B(m1, b), B(m2, b),
\*           NEW v \in Value
\*    PROVE V(m1, v) <=> V(m2, v)
\*PROOF BY Get1a_correct, Zenon DEF B, V

LEMMA TranBallot ==
    ASSUME NEW m1 \in Message, NEW m2 \in Tran(m1),
           NEW b1 \in Ballot, NEW b2 \in Ballot,
           B(m1, b1), B(m2, b2)
    PROVE  b2 <= b1
PROOF BY Tran_trans DEF B, Get1a

-----------------------------------------------------------------------------
\* Check equivalence of two well-formedness conditions

LEMMA WellFormedCondition1 ==
    ASSUME NEW m \in Message, m.type = "1b",
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a"
    PROVE  \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m)
PROOF
<1> SUFFICES ASSUME NEW y \in Tran(m), m # y, SameBallot(m, y)
             PROVE  y \in Get1a(m)
    OBVIOUS
<1> y.type = "1a" OBVIOUS
<1> y \in Message BY Tran_Message
<1> y.bal \in Ballot BY MessageTypeSpec
<1> B(y, y.bal) BY B_1a
<1> SUFFICES ASSUME NEW z \in Tran(m), z.type = "1a"
             PROVE  z.bal =< y.bal
    BY DEF Get1a
<1> z \in Message BY Tran_Message
<1> z.bal \in Ballot BY MessageTypeSpec
<1> B(z, z.bal) BY B_1a
<1> QED BY TranBallot DEF SameBallot

\* Equivalence of two well-formedness conditions
LEMMA WellFormedConditionEquiv ==
    ASSUME NEW m \in Message, m.type = "1b"
    PROVE  (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y \in Get1a(m))
           <=>
           (\A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a")
PROOF BY WellFormedCondition1 DEF Get1a

LEMMA WellFormedCondition2 ==
    ASSUME NEW m \in Message, m.type = "1b",
           \A y \in Tran(m) :
            m # y /\ SameBallot(m, y) => y.type = "1a"
    PROVE  \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm
PROOF BY Tran_Message, B_func DEF SameBallot

LEMMA WellFormedCondition3 ==
    ASSUME NEW m \in Message, m.type = "1b",
           \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm
    PROVE  \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
PROOF BY TranBallot DEF Ballot

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \in SUBSET Message
    /\ known_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ recent_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ prev_msg \in [Acceptor -> Message \cup {NoMessage}]
    /\ queued_msg \in [Acceptor -> Message \cup {NoMessage}]
    /\ 2a_lrn_loop \in [Acceptor -> BOOLEAN]
    /\ processed_lrns \in [Acceptor -> SUBSET Learner]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]
    /\ BVal \in [Ballot -> Value]

-----------------------------------------------------------------------------
SentBy(acc) == { mm \in msgs : mm.type # "1a" /\ mm.acc = acc }

Sent1bBy(acc) == { mm \in msgs : mm.type = "1b" /\ mm.acc = acc }

RecentMsgsSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        recent_msgs[AL] \in SUBSET known_msgs[AL]

KnownMsgsSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ known_msgs[AL] \in SUBSET msgs
        /\ \A M \in known_msgs[AL] :
            /\ Proper(AL, M)
            /\ WellFormed(M)
            /\ Tran(M) \in SUBSET known_msgs[AL]
            /\ \E b \in Ballot : B(M, b)

CaughtSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        \A M \in known_msgs[AL] :
            Caught(M) \cap SafeAcceptor = {}

DecisionSpec ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \in decision[L, BB] => ChosenIn(L, BB, VV)

SafeAcceptorPrevSpec1 ==
    \A A \in SafeAcceptor :
        SentBy(A) = {} <=> prev_msg[A] = NoMessage

SafeAcceptorPrevSpec2 ==
    \A A \in SafeAcceptor :
        prev_msg[A] # NoMessage =>
            /\ prev_msg[A] \in SentBy(A)
            /\ \A m \in SentBy(A) : m \in Tran(prev_msg[A])

SafeAcceptorQueuedMsgPrevMsgSpec ==
    \A A \in SafeAcceptor :
        /\ SentBy(A) # {} /\ queued_msg[A] = NoMessage =>
            prev_msg[A] \in recent_msgs[A]
        /\ queued_msg[A] # NoMessage => queued_msg[A] = prev_msg[A]

RecentMsgsUniquePreviousMessageSpec ==
    \A A \in SafeAcceptor :
        \A x, y \in recent_msgs[A] :
            x.type # "1a" /\ y.type # "1a" /\
            x.acc = A /\ y.acc = A =>
            x = y

MsgsSafeAcceptorSpec1 ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1 \in Tran(m2) \/ m2 \in Tran(m1)

MsgsSafeAcceptorSpec3 ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1.prev = m2.prev => m1 = m2

MsgsSafeAcceptorPrevRefSpec ==
    \A A \in SafeAcceptor :
        \A m \in SentBy(A) :
            m.prev # NoMessage => m.prev \in m.ref

QueuedMsgSpec1 ==
    \A A \in SafeAcceptor :
        queued_msg[A] # NoMessage =>
        /\ queued_msg[A].type = "1b"
        /\ recent_msgs[A] = {}

QueuedMsgSpec2 ==
    \A A \in SafeAcceptor :
        \A m \in Sent1bBy(A) :
            m \notin known_msgs[A] =>
            queued_msg[A] = m

2aLearnerLoopSpec ==
    \A A \in SafeAcceptor :
        2a_lrn_loop[A] = TRUE =>
        queued_msg[A] = NoMessage
-----------------------------------------------------------------------------

LEMMA WellFormedMessage ==
    ASSUME NEW M, WellFormed(M) PROVE M \in Message
BY DEF WellFormed

LEMMA TypeOKInvariant ==
    TypeOK /\ Next => TypeOK'
PROOF
<1> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' OBVIOUS
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> [type |-> "1a", bal |-> bal, prev |-> NoMessage, ref |-> {}] \in Message
      BY Message_spec, MessageRec_eq0 DEF MessageRec0
  <2> QED BY Zenon DEF Send1a, Send, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1a(acc, msg)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> msg \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Store, TypeOK
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {msg}]
  <2> recent_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
    <3>1. CASE WellFormed(new1b)
          BY <3>1, WellFormedMessage, Isa DEF TypeOK
    <3>2. CASE ~WellFormed(new1b)
          BY <3>2 DEF TypeOK
    <3> QED BY <3>1, <3>2
  <2> queued_msg' \in [Acceptor -> Message \cup {NoMessage}]
    <3>1. CASE WellFormed(new1b)
          BY <3>1, WellFormedMessage, Isa DEF TypeOK
    <3>2. CASE ~WellFormed(new1b)
          BY <3>2, Isa DEF TypeOK
    <3> QED BY <3>1, <3>2
  <2> QED BY DEF Process1a, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> USE DEF Process1b
  <2> acc \in Acceptor BY DEF Acceptor
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Store, TypeOK
  <2> QED BY Zenon DEF TypeOK
<1>4. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            /\ queued_msg[acc] # NoMessage
            /\ Process1b(acc, queued_msg[acc])
      BY <1>4
  <2> acc \in Acceptor
      BY DEF Acceptor
  <2> queued_msg[acc] \in Message
      BY DEF TypeOK
  <2> USE DEF Process1b
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF WellFormed, Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Store, WellFormed, TypeOK
  <2> prev_msg' \in [Acceptor -> Message \cup {NoMessage}]
      BY DEF TypeOK
  <2> QED BY Zenon DEF TypeOK
<1>5. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>5
  <2> USE DEF Process1bLearnerLoopStep
  <2> acc \in Acceptor BY DEF Acceptor
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage DEF WellFormed, Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Store, WellFormed, TypeOK
  <2> recent_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY CVC4, WellFormedMessage DEF TypeOK
  <2> prev_msg' \in [Acceptor -> Message \cup {NoMessage}]
      BY DEF TypeOK
  <2> queued_msg' \in [Acceptor -> Message \cup {NoMessage}]
      BY DEF TypeOK
  <2> 2a_lrn_loop' \in [Acceptor -> BOOLEAN]
      BY Zenon DEF TypeOK
  <2> processed_lrns' \in [Acceptor -> SUBSET Learner]
      BY Isa DEF TypeOK
  <2>1. QED BY DEF TypeOK
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>6, Zenon DEF Process1bLearnerLoopDone, TypeOK
<1>7. CASE LearnerAction
      BY <1>7, Isa DEF LearnerAction, LearnerRecv, LearnerDecide, Store, TypeOK
<1>8. CASE FakeAcceptorAction
      BY <1>8, WellFormedMessage, Zenon
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Send, TypeOK
<1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop

LEMMA RecentMsgsSpecInvariant ==
    TypeOK /\ RecentMsgsSpec /\ Next => RecentMsgsSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, RecentMsgsSpec, Next,
                    NEW AL \in SafeAcceptor \cup Learner,
                    NEW M \in recent_msgs[AL]'
             PROVE  M \in known_msgs[AL]'
    BY Zenon DEF RecentMsgsSpec
<1> TypeOK' BY TypeOKInvariant
<1> SafeAcceptor \in SUBSET Acceptor
    BY DEF Acceptor
<1> USE DEF RecentMsgsSpec
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY Zenon DEF Send1a, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> known_msgs'
             = [known_msgs EXCEPT ![acc] = known_msgs[acc] \cup {m1a}]
      BY DEF Store, TypeOK
  <2> CASE WellFormed(new1b)
    <3> QED BY Zenon DEF TypeOK
  <2> CASE ~WellFormed(new1b)
    <3> recent_msgs' = [recent_msgs EXCEPT ![acc] =
                            recent_msgs[acc] \cup {m1a}]
        BY DEF TypeOK
    <3> QED BY Zenon DEF TypeOK
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor :
            Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            Process1b(acc, queued_msg[acc])
      BY <1>3
  <2> QED BY Zenon DEF Process1b, Store, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>4
  <2> QED BY Zenon DEF Process1b, Store, TypeOK
<1>5. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>5
  <2> USE DEF Process1bLearnerLoopStep
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc]]
  <2> CASE WellFormed(new2a)
    <3> known_msgs'
            = [known_msgs EXCEPT ![acc] = known_msgs[acc] \cup {new2a}]
        BY DEF Store, TypeOK
    <3> recent_msgs'
            = [recent_msgs EXCEPT ![acc] = {new2a}]
        BY DEF TypeOK
    <3> QED BY Zenon DEF TypeOK
  <2> QED BY Zenon
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY Zenon, <1>6 DEF Process1bLearnerLoopDone, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, msg \in msgs : LearnerRecv(lrn, msg)
      BY <1>7
  <2> QED BY Zenon DEF LearnerRecv, Store, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY Zenon, <1>8 DEF LearnerDecide, TypeOK
<1>9. CASE FakeAcceptorAction
      BY Zenon, <1>9
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
           DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA QueuedMsgSpec1Invariant ==
    TypeOK /\ Next /\ 2aLearnerLoopSpec /\
    QueuedMsgSpec1 => QueuedMsgSpec1'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, 2aLearnerLoopSpec,
                    QueuedMsgSpec1,
                    NEW A \in SafeAcceptor,
                    queued_msg[A]' # NoMessage
             PROVE  /\ queued_msg[A]'.type = "1b"
                    /\ recent_msgs[A]' = {}
    BY DEF QueuedMsgSpec1
<1> TypeOK' BY TypeOKInvariant
<1> USE DEF QueuedMsgSpec1
<1> A \in Acceptor BY DEF Acceptor
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a, Send, TypeOK
<1>2. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> CASE acc # A
      BY DEF Send, TypeOK
  <2> CASE ~WellFormed(new1b)
      BY DEF Send, TypeOK
  <2> CASE acc = A /\ WellFormed(new1b)
      BY DEF TypeOK, Send
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor :
            Process1b(a, queued_msg[a])
      BY <1>3 DEF Process1b, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
      BY <1>4 DEF Process1b, TypeOK
<1>5. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            /\ 2a_lrn_loop[acc] = TRUE
            /\ Process1bLearnerLoopStep(acc, lrn)
      BY <1>5
  <2> USE DEF Process1bLearnerLoopStep
  <2> QED BY DEF TypeOK, Send, 2aLearnerLoopSpec
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>6 DEF Process1bLearnerLoopDone, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7 DEF LearnerRecv, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF LearnerDecide, TypeOK
<1>9. CASE FakeAcceptorAction
      BY Zenon, <1>9
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Send
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
           DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA QueuedMsgSpec2Invariant ==
    TypeOK /\ Next /\
    QueuedMsgSpec2 => QueuedMsgSpec2'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    QueuedMsgSpec2,
                    NEW A \in SafeAcceptor,
                    NEW M \in msgs', M.type = "1b", M.acc = A,
                    M \notin known_msgs[A]'
             PROVE  queued_msg[A]' = M
    BY DEF QueuedMsgSpec2, Sent1bBy
<1> TypeOK' BY TypeOKInvariant
<1> USE DEF QueuedMsgSpec2
<1> A \in Acceptor BY DEF Acceptor
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a, Send, Sent1bBy, TypeOK
<1>2. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
      BY <1>2 DEF Process1b, Sent1bBy, Store, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1a(acc, m1a)
      BY <1>3
  <2> USE DEF Process1a
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> CASE WellFormed(new1b)
    <3> queued_msg' = [queued_msg EXCEPT ![acc] = new1b]
        OBVIOUS
    <3> QED BY NoMessageIsNotAMessage DEF TypeOK, Send, Sent1bBy, Store, Recv
  <2> QED BY NoMessageIsNotAMessage DEF TypeOK, Send, Sent1bBy, Store, Recv
<1>4. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1b(a, m)
      BY <1>4 DEF Process1b, Sent1bBy, Store, TypeOK
<1>5. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
      BY <1>5 DEF Process1bLearnerLoopStep, Store, Send, Sent1bBy, TypeOK
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>6 DEF Process1bLearnerLoopDone, Sent1bBy, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7 DEF LearnerRecv, Sent1bBy, Store, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF LearnerDecide, Sent1bBy, TypeOK
<1>9a. CASE \E a \in FakeAcceptor : FakeSend1b(a)
       BY <1>9a, AcceptorAssumption
       DEF FakeAcceptorAction, FakeSend1b, Send, Sent1bBy, TypeOK
<1>9b. CASE \E a \in FakeAcceptor : FakeSend2a(a)
       BY <1>9b, AcceptorAssumption
       DEF FakeSend2a, Send, Sent1bBy, TypeOK
<1>10. QED BY Zenon, <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9a, <1>9b
           DEF Next, AcceptorProcessAction, Process1bLearnerLoop,
               LearnerAction, FakeAcceptorAction

LEMMA 2aLearnerLoopSpecInvariant ==
    TypeOK /\ Next /\ 2aLearnerLoopSpec =>
    2aLearnerLoopSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, 2aLearnerLoopSpec, Next,
                    NEW A \in SafeAcceptor,
                    2a_lrn_loop[A]' = TRUE
             PROVE  queued_msg[A]' = NoMessage
    BY Zenon DEF 2aLearnerLoopSpec
<1> TypeOK' BY TypeOKInvariant
<1> USE DEF 2aLearnerLoopSpec
<1> A \in Acceptor BY DEF Acceptor
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a
<1>2. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = FALSE
            /\ \E m \in msgs : Process1a(a, m)
      BY <1>2 DEF Process1a, TypeOK
<1>q. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = FALSE
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
      BY <1>q DEF Process1b, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            /\ \E m \in msgs : Process1b(a, m)
      BY <1>3 DEF Process1b, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
      BY <1>4 DEF Process1bLearnerLoopStep
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7 DEF LearnerDecide
<1>8. CASE FakeAcceptorAction
      BY <1>8 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a
<1>10. QED BY Zenon, <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
           DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA WellFormed_monotone ==
    ASSUME NEW m \in Message, WellFormed(m), BVal' = BVal
    PROVE WellFormed(m)'
PROOF BY DEF WellFormed, q, Fresh, Con2as, Buried, V

LEMMA KnownMsgMonotone ==
    TypeOK /\ Next =>
    \A AL \in SafeAcceptor \cup Learner :
        known_msgs[AL] \subseteq known_msgs[AL]'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    NEW AL \in SafeAcceptor \cup Learner,
                    NEW M \in known_msgs[AL]
             PROVE  M \in known_msgs[AL]'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY DEF Process1a, Store, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            Process1b(acc, queued_msg[acc])
      BY <1>3
  <2> QED BY DEF Process1b, Store, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>4
  <2> QED BY DEF Process1b, Store, TypeOK
<1>5. CASE \E a \in SafeAcceptor : \E l \in Learner :
            Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            Process1bLearnerLoopStep(acc, lrn)
      BY <1>5
  <2> QED BY DEF Process1bLearnerLoopStep, Acceptor, Store, TypeOK
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>6 DEF Process1bLearnerLoopDone, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7 DEF LearnerRecv, Store, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF LearnerDecide, TypeOK
<1>9. CASE FakeAcceptorAction
      BY <1>9 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
           DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA Known2aMonotone ==
    TypeOK /\ Next =>
    \A L \in Learner, bal \in Ballot, val \in Value :
        Known2a(L, bal, val) \subseteq Known2a(L, bal, val)'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    NEW L \in Learner, NEW BB \in Ballot, NEW VV \in Value,
                    NEW S \in Known2a(L, BB, VV)
             PROVE  S \in Known2a(L, BB, VV)'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> USE DEF Known2a
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY KnownMsgMonotone DEF Send1a, V, TypeOK
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY KnownMsgMonotone DEF Process1a, V, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            Process1b(acc, queued_msg[acc])
      BY <1>3
  <2> QED BY KnownMsgMonotone DEF Process1b, V, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>4
  <2> QED BY KnownMsgMonotone DEF Process1b, V, TypeOK
<1>5. CASE \E a \in SafeAcceptor : \E l \in Learner :
            Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            Process1bLearnerLoopStep(acc, lrn)
      BY <1>5
  <2> QED BY KnownMsgMonotone DEF Process1bLearnerLoopStep, V, TypeOK
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>6, KnownMsgMonotone DEF Process1bLearnerLoopDone, V, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, KnownMsgMonotone DEF LearnerRecv, V, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8, KnownMsgMonotone, Zenon DEF LearnerDecide, V, TypeOK
<1>9. CASE FakeAcceptorAction
      BY <1>9, KnownMsgMonotone
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, V, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA DecisionSpecInvariant ==
    TypeOK /\ Next /\
    DecisionSpec => DecisionSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, DecisionSpec,
                    NEW L \in Learner, NEW BB \in Ballot, NEW VV \in Value,
                    VV \in decision[L, BB]'
             PROVE  ChosenIn(L, BB, VV)'
    BY DEF DecisionSpec
<1> TypeOK' BY TypeOKInvariant
<1> USE DEF DecisionSpec
<1> USE DEF ChosenIn
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY Known2aMonotone DEF Send1a
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY Known2aMonotone DEF Process1a
<1>3. CASE \E a \in SafeAcceptor :
            Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            Process1b(acc, queued_msg[acc])
      BY <1>3
  <2> QED BY Known2aMonotone DEF Process1b
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>4
  <2> QED BY Known2aMonotone DEF Process1b
<1>5. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>5
  <2> QED BY Known2aMonotone DEF Process1bLearnerLoopStep
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>6, Known2aMonotone DEF Process1bLearnerLoopDone
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, Known2aMonotone DEF LearnerRecv
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, BVal >>
      BY <1>8, Zenon DEF LearnerDecide
  <2>0. QED BY Known2aMonotone DEF TypeOK
<1>9. CASE FakeAcceptorAction
      BY <1>9, Known2aMonotone DEF FakeAcceptorAction, FakeSend1b, FakeSend2a
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA SafeAcceptorPrevSpec1Invariant ==
    TypeOK /\ Next /\
    SafeAcceptorPrevSpec1 =>
    SafeAcceptorPrevSpec1'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    SafeAcceptorPrevSpec1
             PROVE  SafeAcceptorPrevSpec1'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor
             PROVE  SentBy(A)' = {} <=> prev_msg[A]' = NoMessage
    BY DEF SafeAcceptorPrevSpec1
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF SafeAcceptorPrevSpec1
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2>1. CASE acc = A
        BY <2>1, NoMessageIsNotAMessage DEF Process1a, SentBy, Send, TypeOK
  <2>2. CASE acc # A
        BY <2>2 DEF Process1a, SentBy, Send, TypeOK
  <2> QED BY <2>1, <2>2
<1>q. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            /\ queued_msg[acc] # NoMessage
            /\ Process1b(acc, queued_msg[acc])
      BY <1>q
  <2> QED BY DEF Process1b, Send, SentBy, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1b(acc, msg)
      BY <1>3
  <2> QED BY DEF Process1b, Send, SentBy
<1>4. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            /\ 2a_lrn_loop[acc] = TRUE
            /\ Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc]]
  <2>1. CASE WellFormed(new2a)
    <3> new2a \in Message BY <2>1 DEF Send, TypeOK
    <3> new2a \in msgs' BY <2>1 DEF Send
    <3>1. CASE acc = A
        BY <3>1, NoMessageIsNotAMessage DEF Process1a, SentBy, Send, TypeOK
    <3>2. CASE acc # A
        BY <3>2 DEF Process1a, SentBy, Send, TypeOK
    <3> QED BY <3>1, <3>2
  <2>2. CASE ~WellFormed(new2a)
        BY <2>2 DEF SentBy
  <2> QED BY <2>1, <2>2
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send, SentBy
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY Zenon, <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
        DEF Next, AcceptorProcessAction, Process1bLearnerLoop, FakeAcceptorAction

LEMMA SafeAcceptorPrevSpec2Invariant ==
    TypeOK /\ Next /\
    2aLearnerLoopSpec /\
    SafeAcceptorQueuedMsgPrevMsgSpec /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 =>
    SafeAcceptorPrevSpec2'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    2aLearnerLoopSpec,
                    SafeAcceptorQueuedMsgPrevMsgSpec,
                    SafeAcceptorPrevSpec1,
                    SafeAcceptorPrevSpec2
             PROVE  SafeAcceptorPrevSpec2'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    prev_msg[A]' # NoMessage
             PROVE  /\ prev_msg[A]' \in SentBy(A)'
                    /\ \A m \in SentBy(A)' : m \in Tran(prev_msg[A]')
    BY DEF SafeAcceptorPrevSpec2
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF SafeAcceptorPrevSpec2
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> CASE acc # A
      BY DEF Process1a, SentBy, Send, TypeOK
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> CASE ~WellFormed(new1b)
      BY DEF Send, SentBy
  <2> CASE acc = A /\ WellFormed(new1b)
    <3> msgs' = msgs \cup {new1b}
        BY DEF Send
    <3> new1b \in Message
        BY DEF TypeOK
    <3> new1b # NoMessage
        BY Zenon, NoMessageIsNotAMessage
    <3> SentBy(A)' = SentBy(A) \cup {new1b}
        BY DEF Send, SentBy
    <3> prev_msg[A]' = new1b
        BY DEF Send, TypeOK
    <3> ASSUME SentBy(A) # {} PROVE prev_msg[A] \in Tran(new1b)
        BY Message_ref_Tran DEF SafeAcceptorQueuedMsgPrevMsgSpec
    <3> HIDE DEF new1b
    <3> QED BY Tran_trans, Tran_refl DEF SafeAcceptorPrevSpec1
  <2> QED OBVIOUS
<1>q. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            /\ queued_msg[acc] # NoMessage
            /\ Process1b(acc, queued_msg[acc])
      BY <1>q
  <2> QED BY DEF Process1b, Send, SentBy, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1b(acc, msg)
      BY <1>3
  <2> QED BY DEF Process1b, Send, SentBy
<1>4. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            /\ 2a_lrn_loop[acc] = TRUE
            /\ Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc]]
  <2> CASE acc # A
      BY DEF SentBy, Send, TypeOK
  <2> CASE ~WellFormed(new2a)
      BY DEF SentBy
  <2> CASE acc = A /\ WellFormed(new2a)
    <3> new2a \in Message BY DEF Send, TypeOK
    <3> SentBy(A)' = SentBy(A) \cup {new2a}
        BY DEF Send, SentBy
    <3> prev_msg[A]' = new2a
        BY DEF Send, TypeOK
    <3> ASSUME SentBy(A) # {} PROVE prev_msg[A] \in Tran(new2a)
        BY Message_ref_Tran DEF 2aLearnerLoopSpec, SafeAcceptorQueuedMsgPrevMsgSpec
    <3> HIDE DEF new2a
    <3> QED BY Tran_trans, Tran_refl DEF SafeAcceptorPrevSpec1
  <2>2. CASE ~WellFormed(new2a)
        BY <2>2 DEF SentBy
  <2> QED BY <2>2
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send, SentBy
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY Zenon, <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
        DEF Next, AcceptorProcessAction, Process1bLearnerLoop, FakeAcceptorAction

LEMMA SafeAcceptorQueuedMsgPrevMsgSpecInvariant ==
    TypeOK /\ Next /\
    2aLearnerLoopSpec /\
    SafeAcceptorQueuedMsgPrevMsgSpec =>
    SafeAcceptorQueuedMsgPrevMsgSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    2aLearnerLoopSpec,
                    SafeAcceptorQueuedMsgPrevMsgSpec
             PROVE  SafeAcceptorQueuedMsgPrevMsgSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor
             PROVE  /\ SentBy(A)' # {} /\ queued_msg[A]' = NoMessage => prev_msg[A]' \in recent_msgs[A]'
                    /\ queued_msg[A]' # NoMessage => queued_msg[A]' = prev_msg[A]'
    BY DEF SafeAcceptorQueuedMsgPrevMsgSpec
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF SafeAcceptorQueuedMsgPrevMsgSpec
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> CASE acc # A
    <3> SentBy(A)' = SentBy(A)
        BY DEF SentBy, Send, TypeOK
    <3> QED BY DEF SentBy, Send, TypeOK
  <2> CASE ~WellFormed(new1b)
      BY DEF SentBy, Send, TypeOK
  <2> CASE acc = A /\ WellFormed(new1b)
    <3> new1b \in Message
        BY DEF Send, TypeOK
    <3> new1b # NoMessage
        BY Zenon, NoMessageIsNotAMessage
    <3> prev_msg[A]' = new1b
        BY DEF TypeOK
    <3> queued_msg[A]' = new1b
        BY DEF TypeOK
    <3> QED BY DEF TypeOK
  <2> QED OBVIOUS
<1>q. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            /\ queued_msg[acc] # NoMessage
            /\ Process1b(acc, queued_msg[acc])
      BY <1>q
  <2> QED BY DEF Process1b, Send, SentBy, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1b(acc, msg)
      BY <1>3
  <2> QED BY DEF Process1b, Send, SentBy
<1>4. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            /\ 2a_lrn_loop[acc] = TRUE
            /\ Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc]]
  <2> CASE acc # A
      BY DEF SentBy, Send, TypeOK
  <2> CASE ~WellFormed(new2a)
      BY DEF SentBy
  <2> CASE acc = A /\ WellFormed(new2a)
    <3> new2a \in Message BY DEF Send, TypeOK
    <3> new2a \in msgs' BY DEF Send
    <3> QED BY DEF 2aLearnerLoopSpec, TypeOK
  <2> QED OBVIOUS
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send, SentBy
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY Zenon, <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
        DEF Next, AcceptorProcessAction, Process1bLearnerLoop, FakeAcceptorAction

LEMMA RecentMsgsSafeAcceptorSpec1Invariant ==
    TypeOK /\ Next /\ QueuedMsgSpec1 /\ QueuedMsgSpec2 /\
    RecentMsgsUniquePreviousMessageSpec =>
    RecentMsgsUniquePreviousMessageSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, QueuedMsgSpec1, QueuedMsgSpec2,
                    RecentMsgsUniquePreviousMessageSpec
             PROVE  RecentMsgsUniquePreviousMessageSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW x \in recent_msgs[A]',
                    NEW y \in recent_msgs[A]',
                    x.type # "1a",
                    y.type # "1a",
                    x.acc = A,
                    y.acc = A
             PROVE  x = y
    BY DEF RecentMsgsUniquePreviousMessageSpec
<1> A \in Acceptor BY DEF Acceptor
<1> x \in Message BY DEF TypeOK
<1> y \in Message BY DEF TypeOK
<1> USE DEF RecentMsgsUniquePreviousMessageSpec
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, Send, SentBy
<1>2. CASE \E a \in SafeAcceptor :
            \E m \in msgs : Process1a(a, m)
      BY <1>2 DEF Process1a, Acceptor, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
      BY <1>3 DEF Process1b, QueuedMsgSpec1, TypeOK
<1>4. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1b(a, m)
      BY <1>4, NoMessageIsNotAMessage DEF Process1b, QueuedMsgSpec2, Sent1bBy, Recv, TypeOK
<1>5. CASE \E a \in SafeAcceptor :
            \E l \in Learner : Process1bLearnerLoopStep(a, l)
      BY <1>5 DEF Process1bLearnerLoopStep, TypeOK
<1>6. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>6 DEF Process1bLearnerLoopDone
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7 DEF LearnerRecv
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF LearnerDecide
<1>9. CASE FakeAcceptorAction
      BY <1>9 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Send
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
           DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA UniqueMessageSent ==
    TypeOK /\ Next =>
    \A m1 \in msgs' : \A m2 \in msgs' :
        m1 \notin msgs /\ m2 \notin msgs =>
        m1 = m2
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    NEW M1 \in msgs', NEW M2 \in msgs',
                    M1 \notin msgs, M2 \notin msgs
             PROVE  M1 = M2
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY Zenon DEF Send1a, Send
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> QED BY Isa DEF Process1a, Send
<1>q. CASE \E a \in SafeAcceptor : Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor : Process1b(acc, queued_msg[acc])
      BY <1>q
  <2> QED BY DEF Process1b
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> QED BY DEF Process1b
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> QED BY DEF Process1bLearnerLoopStep, Send
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7 DEF LearnerDecide
<1>8. CASE FakeAcceptorAction
      BY <1>8 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Send
<1>9. QED BY <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

LEMMA KnownMsgsSpecInvariant ==
    TypeOK /\ Next /\ RecentMsgsSpec /\
    QueuedMsgSpec1 /\ SafeAcceptorPrevSpec2 /\
    SafeAcceptorQueuedMsgPrevMsgSpec /\
    KnownMsgsSpec =>
    KnownMsgsSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, RecentMsgsSpec,
                    QueuedMsgSpec1, SafeAcceptorPrevSpec2,
                    SafeAcceptorQueuedMsgPrevMsgSpec,
                    KnownMsgsSpec
             PROVE  KnownMsgsSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW AL \in SafeAcceptor \cup Learner,
                    NEW M \in known_msgs[AL]'
             PROVE  /\ known_msgs[AL]' \in SUBSET msgs'
                    /\ Proper(AL, M)'
                    /\ WellFormed(M)'
                    /\ Tran(M) \in SUBSET known_msgs[AL]'
                    /\ \E b \in Ballot : B(M, b)
    BY DEF KnownMsgsSpec
<1> USE DEF KnownMsgsSpec
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> USE DEF Send1a
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send
  <2> Proper(AL, M)'
      BY DEF Proper
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Send, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      OBVIOUS
  <2> QED OBVIOUS
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send, Store
  <2> Proper(AL, M)'
      BY DEF Proper, Recv, Store
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Recv, Store, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      BY Tran_1a DEF Store, TypeOK
  <2> \E b \in Ballot : B(M, b)
    <3> CASE M \notin known_msgs[AL]
      <4> M = m1a BY DEF Store
      <4> QED BY B_1a, MessageTypeSpec DEF Recv, TypeOK
    <3> QED OBVIOUS
  <2> QED OBVIOUS
<1>q. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            /\ queued_msg[acc] # NoMessage
            /\ Process1b(acc, queued_msg[acc])
      BY <1>q
  <2> USE DEF Process1b
  <2> queued_msg[acc] \in Message
      BY DEF Recv, WellFormed
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Store, SentBy, QueuedMsgSpec1,
             SafeAcceptorPrevSpec2,
             SafeAcceptorQueuedMsgPrevMsgSpec
  <2> Proper(AL, M)'
      BY KnownMsgMonotone DEF Recv, Proper, Store, QueuedMsgSpec1
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Recv, Store, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \notin known_msgs[AL]
      <4> QED BY Tran_eq DEF Recv, Store, Proper, TypeOK
    <3> QED BY DEF Store
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> USE DEF Process1b
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send, Store
  <2> Proper(AL, M)'
      BY DEF Proper, Recv, Store
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF Recv, Store, TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \notin known_msgs[AL]
      <4> M = msg BY DEF Store
      <4> AL = acc BY DEF Store
      <4> M \in Message BY DEF WellFormed
      <4> QED BY Tran_eq, KnownMsgMonotone DEF Recv, Proper
    <3> QED BY DEF Store
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner :
            Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> acc \in Acceptor
      BY DEF Acceptor
  <2> USE DEF Process1bLearnerLoopStep
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc]]
  <2> CASE WellFormed(new2a)
    <3> new2a \in Message
        BY DEF WellFormed
    <3> CASE acc = AL
      <4> known_msgs[AL]' \in SUBSET msgs'
          BY DEF Send, Store, TypeOK
      <4> Proper(AL, M)'
        <5> CASE M \in known_msgs[acc]
            BY KnownMsgMonotone DEF Proper
        <5> CASE M \notin known_msgs[acc]
          <6> M = new2a
              BY DEF Store, TypeOK
          <6> QED BY Zenon, KnownMsgMonotone
                  DEF Proper, Store, RecentMsgsSpec
        <5> QED OBVIOUS
      <4> WellFormed(M)'
          BY WellFormed_monotone DEF Store, TypeOK
      <4> Tran(M) \in SUBSET known_msgs[AL]'
        <5> CASE M \in known_msgs[acc]
            BY KnownMsgMonotone DEF Proper
        <5> CASE M \notin known_msgs[acc]
          <6> M = new2a
              BY DEF Store, TypeOK
          <6> M.ref \in SUBSET known_msgs[AL]'
              BY DEF Proper
          <6> \A r \in M.ref : Tran(r) \in SUBSET known_msgs[AL]'
              BY Zenon, KnownMsgMonotone DEF RecentMsgsSpec
          <6> QED BY Tran_eq
        <5> QED OBVIOUS
      <4> \E b \in Ballot : B(M, b)
          BY DEF WellFormed
      <4> QED OBVIOUS
    <3> CASE acc # AL
      <4> known_msgs' = [known_msgs EXCEPT ![acc] =
                            known_msgs[acc] \cup {new2a}]
          BY DEF Store
      <4> M \in known_msgs[AL]
          BY DEF TypeOK
      <4> known_msgs[AL]' \in SUBSET msgs'
          BY DEF Send, TypeOK
      <4> Proper(AL, M)'
          BY DEF Proper
      <4> WellFormed(M)'
          BY WellFormed_monotone DEF TypeOK
      <4> QED OBVIOUS
    <3> QED OBVIOUS
  <2> CASE ~WellFormed(new2a)
    <3> Proper(AL, M)'
        BY DEF Proper
    <3> WellFormed(M)'
        BY WellFormed_monotone DEF TypeOK
    <3> QED OBVIOUS
  <2> QED OBVIOUS
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
  <2> PICK acc \in SafeAcceptor : Process1bLearnerLoopDone(acc)
      BY <1>5
  <2> USE DEF Process1bLearnerLoopDone
  <2> known_msgs[AL]' \in SUBSET msgs'
      OBVIOUS
  <2> Proper(AL, M)'
      BY DEF Proper
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, m \in msgs : LearnerRecv(lrn, m)
      BY <1>6
  <2> USE DEF LearnerRecv
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Store
  <2> Proper(AL, M)'
      BY DEF Proper, Recv, Store
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK, Recv, Store
  <2> Tran(M) \in SUBSET known_msgs[AL]'
    <3> CASE M \notin known_msgs[AL]
      <4> QED BY Tran_eq DEF Recv, Store, Proper, TypeOK
    <3> QED BY DEF Store
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>7
  <2> USE DEF LearnerDecide
  <2> known_msgs[AL]' \in SUBSET msgs'
      OBVIOUS
  <2> Proper(AL, M)'
      BY DEF Proper
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      BY DEF WellFormed
  <2> QED OBVIOUS
<1>8. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>8
  <2> USE DEF FakeSend1b
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send
  <2> Proper(AL, M)'
      BY DEF Proper
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      OBVIOUS
  <2> QED OBVIOUS
<1>9. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>9
  <2> USE DEF FakeSend2a
  <2> known_msgs[AL]' \in SUBSET msgs'
      BY DEF Send
  <2> Proper(AL, M)'
      BY DEF Proper
  <2> WellFormed(M)'
      BY WellFormed_monotone DEF TypeOK
  <2> Tran(M) \in SUBSET known_msgs[AL]'
      OBVIOUS
  <2> \E b \in Ballot : B(M, b)
      OBVIOUS
  <2> QED OBVIOUS
<1> QED BY <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9
        DEF Next, AcceptorProcessAction, Process1bLearnerLoop,
            LearnerAction, FakeAcceptorAction

LEMMA MsgsSafeAcceptorSpec1Invariant ==
    TypeOK /\ Next /\
    2aLearnerLoopSpec /\
    SafeAcceptorPrevSpec2 /\
    SafeAcceptorQueuedMsgPrevMsgSpec /\
    MsgsSafeAcceptorSpec1 => MsgsSafeAcceptorSpec1'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    2aLearnerLoopSpec,
                    SafeAcceptorPrevSpec2,
                    SafeAcceptorQueuedMsgPrevMsgSpec,
                    MsgsSafeAcceptorSpec1
             PROVE  MsgsSafeAcceptorSpec1'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW m1 \in msgs, NEW m2 \in msgs' \ msgs,
                    m1.type # "1a", m2.type # "1a",
                    m1.acc = A, m2.acc = A
             PROVE  m1 \in Tran(m2)
  <2> USE DEF MsgsSafeAcceptorSpec1
\*  <2> SUFFICES ASSUME NEW A \in SafeAcceptor,
\*                      NEW x \in msgs', NEW y \in msgs',
\*                      x.type # "1a", y.type # "1a",
\*                      x.acc = A, y.acc = A
\*               PROVE  x \in Tran(y) \/ y \in Tran(x)
\*      BY DEF SentBy, TypeOK
  <2> QED BY UniqueMessageSent, Tran_refl DEF SentBy, TypeOK
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a, Send
<1>2. CASE \E a \in SafeAcceptor :
        /\ queued_msg[a] = NoMessage
        /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
        /\ queued_msg[acc] = NoMessage
        /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> acc = A BY DEF Send
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> m2 = new1b BY DEF Send
  <2> m2 \in Message BY DEF TypeOK
  <2> prev_msg[A] \in recent_msgs[A]
      BY DEF SafeAcceptorQueuedMsgPrevMsgSpec, SentBy
  <2> prev_msg[A] # NoMessage
      BY NoMessageIsNotAMessage DEF TypeOK
  <2> \A m \in SentBy(A) : m \in Tran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2
  <2> prev_msg[A] \in Tran(m2)
      BY Message_ref_Tran
  <2> QED BY Tran_trans DEF SentBy
<1>q. CASE \E a \in SafeAcceptor : Process1b(a, queued_msg[a])
      BY <1>q DEF Process1b, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
      BY <1>3 DEF Process1b, Send
<1>4. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            /\ 2a_lrn_loop[acc] = TRUE
            /\ Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> queued_msg[acc] = NoMessage
      BY DEF 2aLearnerLoopSpec
  <2> USE DEF Process1bLearnerLoopStep
  <2> acc \in Acceptor BY DEF Acceptor
  <2> acc = A BY DEF Send
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc]]
  <2> m2 = new2a BY DEF Send
  <2> m2 \in Message BY DEF TypeOK
  <2> prev_msg[A] \in recent_msgs[A]
      BY DEF SafeAcceptorQueuedMsgPrevMsgSpec, SentBy
  <2> prev_msg[A] # NoMessage
      BY NoMessageIsNotAMessage DEF TypeOK
  <2> \A m \in SentBy(A) : m \in Tran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2
  <2> prev_msg[A] \in Tran(m2)
      BY Message_ref_Tran
  <2> QED BY Tran_trans DEF SentBy
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send
<1>7. CASE \E acc \in FakeAcceptor : FakeSend1b(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send
<1>8. CASE \E acc \in FakeAcceptor : FakeSend2a(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send
<1> QED BY <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
        DEF Next, AcceptorProcessAction, Process1bLearnerLoop,
            FakeAcceptorAction

LEMMA MsgsSafeAcceptorSpec3Invariant ==
    TypeOK /\ Next /\
    KnownMsgsSpec /\
    RecentMsgsSpec /\
    MsgsSafeAcceptorPrevRefSpec /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorPrevSpec2 /\
    SafeAcceptorQueuedMsgPrevMsgSpec /\
    MsgsSafeAcceptorSpec3 => MsgsSafeAcceptorSpec3'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    KnownMsgsSpec,
                    RecentMsgsSpec,
                    SafeAcceptorQueuedMsgPrevMsgSpec,
                    MsgsSafeAcceptorPrevRefSpec,
                    SafeAcceptorPrevSpec1,
                    SafeAcceptorPrevSpec2,
                    MsgsSafeAcceptorSpec3
             PROVE  MsgsSafeAcceptorSpec3'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW m1 \in msgs, NEW m2 \in msgs' \ msgs,
                    m1.acc = A, m2.acc = A,
                    m1.type # "1a", m2.type # "1a",
                    m1.prev = m2.prev
             PROVE  m1 = m2
  <2> USE DEF MsgsSafeAcceptorSpec3
  <2> QED BY UniqueMessageSent DEF SentBy, TypeOK
<1> m1 \in Message
    BY DEF TypeOK
<1> SentBy(A) # {}
    BY DEF SentBy, Send, TypeOK
<1> prev_msg[A] # NoMessage
    BY DEF SafeAcceptorPrevSpec1
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a, Send
<1>2. CASE \E a \in SafeAcceptor :
        /\ queued_msg[a] = NoMessage
        /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
        /\ queued_msg[acc] = NoMessage
        /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> m2 = new1b
      BY DEF Send
  <2> acc = A
      BY DEF TypeOK
  <2> WellFormed(new1b)
      BY DEF TypeOK
  <2> prev_msg[A] \in Message
      BY DEF SafeAcceptorQueuedMsgPrevMsgSpec, RecentMsgsSpec, KnownMsgsSpec, TypeOK
  <2> prev_msg[A] \in m1.ref
      BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy
  <2> m1 \notin Tran(prev_msg[A])
      BY Tran_ref_acyclic
  <2> m1 \in Tran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2, SentBy
  <2> QED OBVIOUS
<1>q. CASE \E a \in SafeAcceptor : Process1b(a, queued_msg[a])
      BY <1>q DEF Process1b, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
      BY <1>3 DEF Process1b, Send
<1>4. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            /\ 2a_lrn_loop[acc] = TRUE
            /\ Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc]]
  <2> m2 = new2a
      BY DEF Send, TypeOK
  <2> acc = A
      BY DEF Send, SentBy, TypeOK
  <2> WellFormed(new2a)
      BY DEF TypeOK
  <2> prev_msg[A] \in Message
      BY DEF SafeAcceptorQueuedMsgPrevMsgSpec, RecentMsgsSpec, KnownMsgsSpec, TypeOK
  <2> prev_msg[A] \in m1.ref
      BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy
  <2> m1 \notin Tran(prev_msg[A])
      BY Tran_ref_acyclic
  <2> m1 \in Tran(prev_msg[A])
      BY DEF SafeAcceptorPrevSpec2, SentBy
  <2> QED OBVIOUS
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send
<1>7. CASE \E acc \in FakeAcceptor : FakeSend1b(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send
<1>8. CASE \E acc \in FakeAcceptor : FakeSend2a(acc)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send
<1> QED BY <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
        DEF Next, AcceptorProcessAction, Process1bLearnerLoop,
            FakeAcceptorAction

LEMMA MsgsSafeAcceptorPrevRefSpecInvariant ==
    TypeOK /\ Next /\
    2aLearnerLoopSpec /\
    SafeAcceptorPrevSpec1 /\
    SafeAcceptorQueuedMsgPrevMsgSpec /\
    MsgsSafeAcceptorPrevRefSpec =>
    MsgsSafeAcceptorPrevRefSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    2aLearnerLoopSpec,
                    SafeAcceptorPrevSpec1,
                    SafeAcceptorQueuedMsgPrevMsgSpec,
                    MsgsSafeAcceptorPrevRefSpec
             PROVE  MsgsSafeAcceptorPrevRefSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW mm \in msgs', mm \notin msgs,
                    mm.acc = A, mm.type # "1a",
                    mm.prev # NoMessage
             PROVE  mm.prev \in mm.ref
    BY DEF MsgsSafeAcceptorPrevRefSpec, SentBy, Send
<1> A \in Acceptor BY DEF Acceptor
<1> USE DEF MsgsSafeAcceptorPrevRefSpec
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot : Send1a(bal)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, SentBy, Send
<1>2. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       prev |-> prev_msg[acc],
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> QED BY DEF SafeAcceptorQueuedMsgPrevMsgSpec,
                 SafeAcceptorPrevSpec1,
                 SentBy, Send, TypeOK
<1>q. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] # NoMessage
            /\ Process1b(a, queued_msg[a])
  <2> PICK acc \in SafeAcceptor :
            /\ queued_msg[acc] # NoMessage
            /\ Process1b(acc, queued_msg[acc])
      BY <1>q
  <2> QED BY DEF Process1b, Send, SentBy, TypeOK
<1>3. CASE \E a \in SafeAcceptor :
            /\ queued_msg[a] = NoMessage
            /\ \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs :
            /\ queued_msg[acc] = NoMessage
            /\ Process1b(acc, msg)
      BY <1>3
  <2> QED BY DEF Process1b, Send, SentBy
<1>4. CASE \E a \in SafeAcceptor :
            /\ 2a_lrn_loop[a] = TRUE
            /\ \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner :
            /\ 2a_lrn_loop[acc] = TRUE
            /\ Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> QED BY DEF SafeAcceptorQueuedMsgPrevMsgSpec,
                 SafeAcceptorPrevSpec1, 2aLearnerLoopSpec,
                 Send, SentBy, TypeOK
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send, SentBy
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE \E a \in FakeAcceptor : FakeSend1b(a)
  <2> PICK acc \in FakeAcceptor : FakeSend1b(acc)
      BY <1>7
  <2> QED BY AcceptorAssumption DEF FakeSend1b, Send, SentBy
<1>8. CASE \E a \in FakeAcceptor : FakeSend2a(a)
  <2> PICK acc \in FakeAcceptor : FakeSend2a(acc)
      BY <1>8
  <2> QED BY AcceptorAssumption DEF FakeSend2a, Send, SentBy
<1> QED BY Zenon, <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
        DEF Next, AcceptorProcessAction, Process1bLearnerLoop, FakeAcceptorAction

LEMMA MsgsSafeAcceptorSpecImpliesCaughtSpec ==
    ASSUME TypeOK, KnownMsgsSpec, MsgsSafeAcceptorSpec3
    PROVE  CaughtSpec
PROOF BY MessageTypeSpec
      DEF MsgsSafeAcceptorSpec3, CaughtSpec, Caught, CaughtMsg, KnownMsgsSpec, SentBy, TypeOK

LEMMA QuorumIntersection ==
    ASSUME TypeOK,
           NEW a \in Learner, NEW b \in Learner,
           NEW M \in Message,
           NEW Qa \in SUBSET Message, NEW Qb \in SUBSET Message,
           NEW S \in ByzQuorum,
           [lr |-> a, q |-> { mm.acc : mm \in Qa }] \in TrustLive,
           [lr |-> b, q |-> { mm.acc : mm \in Qb }] \in TrustLive,
           ConByQuorum(a, b, M, S)
    PROVE  \E p \in S, ma \in Qa, mb \in Qb :
            /\ p \notin Caught(M)
            /\ ma.acc = p
            /\ mb.acc = p
PROOF
<1> /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
    /\ S \cap Caught(M) = {}
    BY DEF ConByQuorum
<1> PICK acc \in S : /\ acc \in { mm.acc : mm \in Qa }
                     /\ acc \in { mm.acc : mm \in Qb }
    BY TrustLiveAssumption, LearnerGraphAssumptionValidity, Zenon
<1> QED BY BQAssumption

LEMMA EntConnected ==
    ASSUME CaughtSpec,
           NEW a \in Learner, NEW b \in Learner,
           <<a, b>> \in Ent,
           NEW AL \in SafeAcceptor \cup Learner,
           NEW m \in known_msgs[AL]
    PROVE  ConByQuorum(a, b, m, SafeAcceptor)
PROOF BY BQAssumption DEF ConByQuorum, Ent, CaughtSpec

-----------------------------------------------------------------------------
HeterogeneousSpec(bal) ==
    \A L0, L1, L2 \in Learner :
        <<L1, L2>> \in Ent =>
        \A V1, V2 \in Value :
        \A B1 \in Ballot :
            ChosenIn(L1, B1, V1) =>
            \A M \in known_msgs[L0] :
                M.type = "2a" /\
                M.lrn = L2 /\
                B(M, bal) /\
                B1 < bal /\
                V(M, V2) =>
                V1 = V2

-----------------------------------------------------------------------------

THEOREM GeneralBallotInduction ==
    ASSUME NEW P(_),
           \A bal \in Ballot : (\A b \in Ballot : b < bal => P(b)) => P(bal)
    PROVE  \A bal \in Ballot : P(bal)
PROOF
<1> USE DEF Ballot
<1> SUFFICES \A n \in Nat : (\A m \in 0..n - 1 : P(m)) => P(n)
    BY GeneralNatInduction, IsaM("blast")
<1> QED OBVIOUS

LEMMA HeterogeneousLemma ==
    TypeOK /\ KnownMsgsSpec /\ CaughtSpec /\ MsgsSafeAcceptorSpec1 =>
    \A bal \in Ballot : HeterogeneousSpec(bal)
PROOF
<1> ASSUME TypeOK, KnownMsgsSpec, CaughtSpec, MsgsSafeAcceptorSpec1,
           NEW bal \in Ballot,
           (\A b \in Ballot : b < bal => HeterogeneousSpec(b))
    PROVE  HeterogeneousSpec(bal)
  <2> SUFFICES ASSUME NEW L0 \in Learner,
                      NEW L1 \in Learner, NEW L2 \in Learner,
                      NEW V1 \in Value, NEW V2 \in Value,
                      NEW B1 \in Ballot,
                      NEW M \in known_msgs[L0],
                      <<L1, L2>> \in Ent,
                      ChosenIn(L1, B1, V1),
                      M.type = "2a",
                      M.lrn = L2,
                      B(M, bal),
                      B1 < bal,
                      V(M, V2)
               PROVE  V1 = V2
      BY DEF HeterogeneousSpec
  <2>1. M \in msgs /\ Proper(L0, M) /\ WellFormed(M)
      BY DEF KnownMsgsSpec
  <2> M \in Message
      BY <2>1 DEF TypeOK
  <2>3. [lr |-> L2, q |-> q(M)] \in TrustLive
      BY <2>1 DEF WellFormed
  <2> DEFINE Q2 == { m \in Tran(M) :
                        /\ m.type = "1b"
                        /\ Fresh(M.lrn, m)
                        /\ \A b \in Ballot : B(m, b) <=> B(M, b) }
  <2> Q2 \in SUBSET Message
      BY Tran_Message
  <2>5. q(M) = { mm.acc : mm \in Q2 }
      BY DEF q
  <2> [lr |-> L2, q |-> { mm.acc : mm \in Q2 }] \in TrustLive
      BY <2>5, <2>3
  <2> ConByQuorum(L2, L1, M, SafeAcceptor)
      BY EntConnected, EntanglementSym, Zenon
  <2> ConByQuorum(L1, L2, M, SafeAcceptor)
      BY EntConnected, Zenon
  <2>8. PICK Q1 \in SUBSET Known2a(L1, B1, V1) :
                [lr |-> L1, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
      BY Zenon DEF ChosenIn
  <2> Q1 \in SUBSET msgs
      BY DEF Known2a, KnownMsgsSpec
  <2> Q1 \in SUBSET Message
      BY DEF TypeOK
  <2> [lr |-> L1, q |-> { mm.acc : mm \in Q1 }] \in TrustLive
      BY <2>8
  <2> PICK p \in SafeAcceptor, m1b \in Q2, m2a \in Q1 :
            /\ p \notin Caught(M)
            /\ m1b.acc = p
            /\ m2a.acc = p
    <3> HIDE DEF Q2
    <3> QED BY QuorumIntersection, BQAssumption, Isa
  <2> m2a.type = "2a"
      BY <2>8 DEF Known2a
  <2> m2a.lrn = L1
      BY <2>8 DEF Known2a
  <2> m2a \in msgs
      OBVIOUS
  <2> B(m2a, B1)
      BY <2>8 DEF Known2a
  <2> V(m2a, V1)
      BY <2>8 DEF Known2a
  <2> m1b.type = "1b"
      OBVIOUS
  <2> m1b \in known_msgs[L0]
      BY DEF KnownMsgsSpec
  <2> m1b \in msgs
      BY DEF KnownMsgsSpec
  <2> WellFormed(m1b)
      BY DEF KnownMsgsSpec
  <2> B(m1b, bal)
      OBVIOUS
  <2> Fresh(L2, m1b) BY DEF q
  <2>13. \A r \in Tran(m1b) :
            r # m1b /\ r.type # "1a" =>
            \A b1, b2 \in Ballot : B(r, b1) /\ B(m1b, b2) => b1 < b2
    <3> QED BY WellFormedCondition2, WellFormedCondition3 DEF WellFormed
  <2>14. m2a \in Tran(m1b)
    <3> ASSUME m1b \in Tran(m2a) PROVE FALSE
        BY TranBallot DEF Ballot
    <3> QED BY DEF MsgsSafeAcceptorSpec1, SentBy
  <2>15. CASE ~Buried(m2a, m1b)
    <3> L1 \in Con(L2, m1b)
        BY EntConnected, EntanglementSym, BQAssumption DEF Con
    <3> m2a \in Con2as(L2, m1b)
        BY <2>14, <2>15 DEF Con2as
    <3> \A v \in Value : V(m2a, v) <=> V(m1b, v)
        BY DEF Fresh
    <3> V(m1b, V1)
        BY DEF Fresh
    <3> V(m1b, V2)
        BY V_def, V_func DEF TypeOK
    <3> QED BY V_func
  <2>16. CASE Buried(m2a, m1b)
    <3> DEFINE Q == { m \in Tran(m1b) :
                        \E z \in Tran(m) :
                            /\ z.type = "2a"
                            /\ z.lrn = L1
                            /\ \A bx, bz \in Ballot :
                                B(m2a, bx) /\ B(z, bz) => bx < bz
                            /\ \A vx, vz \in Value :
                                V(m2a, vx) /\ V(z, vz) => vx # vz }
    <3> [lr |-> L1, q |-> { m.acc : m \in Q }] \in TrustLive
        BY <2>16 DEF Buried
    <3> { m.acc : m \in Q } \in ByzQuorum
        BY TrustLiveAssumption, Zenon
    <3>3. PICK m0 \in { m.acc : m \in Q } : TRUE
        BY EntaglementTrustLiveNonEmpty, Zenon
    <3> PICK r \in Tran(m1b) :
            /\ r.type = "2a"
            /\ r.lrn = L1
            /\ \A b2a, br \in Ballot :
                B(m2a, b2a) /\ B(r, br) => b2a < br
            /\ \A v2a, vr \in Value :
                V(m2a, v2a) /\ V(r, vr) => v2a # vr
        BY <3>3, Tran_trans, BQAssumption
    <3> <<L1, L1>> \in Ent
        BY EntanglementSelf
    <3> r \in known_msgs[L0]
        BY DEF KnownMsgsSpec
    <3> r \in Message
        BY DEF TypeOK
    <3> PICK br \in Ballot : B(r, br)
        BY DEF KnownMsgsSpec
    <3> PICK vr \in Value : V(r, vr)
        BY V_def DEF TypeOK
    <3> B1 < br
        OBVIOUS
    <3> V1 # vr
        OBVIOUS
    <3> br < bal
        BY <2>13
    <3> QED BY DEF HeterogeneousSpec
  <2>17. QED BY <2>15, <2>16
<1> QED BY GeneralBallotInduction, IsaM("blast")

LEMMA ChosenSafeCaseEq ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW BB \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK,
           <<L1, L2>> \in Ent,
           ChosenIn(L1, BB, V1), ChosenIn(L2, BB, V2)
    PROVE V1 = V2
PROOF
<1> PICK S1 \in SUBSET Known2a(L1, BB, V1) :
        [lr |-> L1, q |-> { m.acc : m \in S1 }] \in TrustLive
    BY DEF ChosenIn, Zenon
<1> DEFINE Q1 == { m.acc : m \in S1 }
<1> Q1 \in ByzQuorum
    BY TrustLiveAssumption, Zenon
<1> PICK S2 \in SUBSET Known2a(L2, BB, V2) :
        [lr |-> L2, q |-> { m.acc : m \in S2 }] \in TrustLive
    BY DEF ChosenIn, Zenon
<1> DEFINE Q2 == { m.acc : m \in S2 }
<1> Q2 \in ByzQuorum
    BY TrustLiveAssumption, Zenon
<1> PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2
    BY EntanglementTrustLive
<1>4. PICK m1 \in known_msgs[L1] :
        /\ B(m1, BB)
        /\ V(m1, V1)
      BY DEF ChosenIn, Known2a
<1>5. PICK m2 \in known_msgs[L2] :
        /\ B(m2, BB)
        /\ V(m2, V2)
      BY DEF ChosenIn, Known2a
<1>6. QED BY <1>4, <1>5, V_def, V_func DEF TypeOK

LEMMA ChosenSafeCaseLt ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK, KnownMsgsSpec, CaughtSpec, MsgsSafeAcceptorSpec1,
           <<L1, L2>> \in Ent,
           B1 < B2,
           ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1> PICK S1 \in SUBSET Known2a(L1, B1, V1) :
        [lr |-> L1, q |-> { m.acc : m \in S1 }] \in TrustLive
    BY Zenon DEF ChosenIn
<1> DEFINE Q1 == { m.acc : m \in S1 }
<1> Q1 \in ByzQuorum BY TrustLiveAssumption
<1> PICK S2 \in SUBSET Known2a(L2, B2, V2) :
        [lr |-> L2, q |-> { m.acc : m \in S2 }] \in TrustLive
    BY Zenon DEF ChosenIn
<1> DEFINE Q2 == { m.acc : m \in S2 }
<1> Q2 \in ByzQuorum
    BY TrustLiveAssumption, Zenon
<1> <<L2, L2>> \in Ent
    BY EntanglementSelf, EntanglementSym, Zenon
<1> PICK A \in Q2 : TRUE
    BY EntaglementTrustLiveNonEmpty
<1> PICK M \in known_msgs[L2] :
        /\ M.type = "2a"
        /\ M.lrn = L2
        /\ B(M, B2)
        /\ V(M, V2)
    BY DEF Known2a
<1> QED BY HeterogeneousLemma DEF HeterogeneousSpec

LEMMA ChosenSafe ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK, KnownMsgsSpec, CaughtSpec, MsgsSafeAcceptorSpec1,
           <<L1, L2>> \in Ent,
           ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1>0. CASE B1 < B2 BY <1>0, ChosenSafeCaseLt
<1>1. CASE B2 < B1 BY <1>1, ChosenSafeCaseLt, EntanglementSym
<1>2. CASE B1 = B2 BY <1>2, ChosenSafeCaseEq
<1>3. QED BY <1>0, <1>1, <1>2 DEF Ballot

LEMMA SafetyStep ==
    TypeOK /\ Next /\
    KnownMsgsSpec /\ CaughtSpec /\ MsgsSafeAcceptorSpec1 /\ DecisionSpec /\
    Safety => Safety'
PROOF
<1> SUFFICES
        ASSUME TypeOK, Next,
               KnownMsgsSpec, CaughtSpec, MsgsSafeAcceptorSpec1, DecisionSpec,
               Safety,
               NEW L1 \in Learner, NEW L2 \in Learner,
               NEW B1 \in Ballot, NEW B2 \in Ballot,
               NEW V1 \in Value, NEW V2 \in Value,
               <<L1, L2>> \in Ent,
               V1 \in decision'[L1, B1], V2 \in decision'[L2, B2]
        PROVE V1 = V2
    BY DEF Safety
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a, Safety
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
      BY <1>2 DEF Process1a, Safety
<1>q. CASE \E a \in SafeAcceptor : Process1b(a, queued_msg[a])
      BY <1>q DEF Process1b, Safety
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
      BY <1>3 DEF Process1b, Safety
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
      BY <1>4 DEF Process1bLearnerLoopStep, Safety
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Safety
<1>6. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>6 DEF LearnerRecv, Safety
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, BVal >>
      BY <1>7, Zenon DEF LearnerDecide
  <2> CASE V1 # V2
    <3>1. CASE val # V1 /\ val # V2 BY <3>1 DEF Safety, TypeOK
    <3>2. CASE val = V1
      <4> V2 \in decision[L2, B2] BY <3>2 DEF TypeOK
      <4> ChosenIn(L2, B2, V2) BY DEF DecisionSpec
      <4>2. CASE V1 \in decision[L1, B1] BY <4>2 DEF Safety
      <4>3. CASE V1 \notin decision[L1, B1]
        <5> lrn = L1 /\ bal = B1 BY <4>3, <3>2 DEF TypeOK
        <5> ChosenIn(L1, B1, V1) BY <3>2
        <5> QED BY ChosenSafe, AllProvers
      <4> QED BY <4>2, <4>3
    <3>3. CASE val = V2
      <4> V1 \in decision[L1, B1] BY <3>3 DEF TypeOK
      <4> ChosenIn(L1, B1, V1) BY DEF DecisionSpec
      <4>2. CASE V2 \in decision[L2, B2] BY <4>2 DEF Safety
      <4>3. CASE V2 \notin decision[L2, B2]
        <5> lrn = L2 /\ bal = B2 BY <4>3, <3>2 DEF TypeOK
        <5> ChosenIn(L2, B2, V2) BY <3>3
        <5> QED BY ChosenSafe
      <4> QED BY <4>2, <4>3
    <3> QED BY <3>1, <3>2, <3>3
  <2>10. QED OBVIOUS
<1>8. CASE FakeAcceptorAction
      BY <1>8 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Safety
<1>9. QED BY <1>1, <1>2, <1>q, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction

FullSafetyInvariant ==
    /\ TypeOK
    /\ RecentMsgsSpec
    /\ KnownMsgsSpec
    /\ QueuedMsgSpec1
    /\ 2aLearnerLoopSpec
    /\ SafeAcceptorPrevSpec1
    /\ SafeAcceptorPrevSpec2
    /\ SafeAcceptorQueuedMsgPrevMsgSpec
    /\ MsgsSafeAcceptorSpec1
    /\ MsgsSafeAcceptorSpec3
    /\ MsgsSafeAcceptorPrevRefSpec
    /\ DecisionSpec
    /\ Safety

LEMMA TypeOKInit == Init => TypeOK
PROOF BY DEF Init, TypeOK

LEMMA RecentMsgsSpecInit == Init => RecentMsgsSpec
PROOF BY DEF Init, RecentMsgsSpec, Acceptor

LEMMA KnownMsgsSpecInit == Init => KnownMsgsSpec
PROOF BY DEF Init, KnownMsgsSpec, Acceptor

LEMMA QueuedMsgSpec1Init == Init => QueuedMsgSpec1
PROOF BY DEF Init, QueuedMsgSpec1, Acceptor

LEMMA 2aLearnerLoopSpecInit == Init => 2aLearnerLoopSpec
PROOF BY DEF Init, 2aLearnerLoopSpec, Acceptor

LEMMA SafeAcceptorPrevSpec1Init == Init => SafeAcceptorPrevSpec1
PROOF BY DEF Init, SafeAcceptorPrevSpec1, Acceptor, SentBy

LEMMA SafeAcceptorPrevSpec2Init == Init => SafeAcceptorPrevSpec2
PROOF BY DEF Init, SafeAcceptorPrevSpec2, Acceptor

LEMMA SafeAcceptorQueuedMsgPrevMsgSpecInit == Init => SafeAcceptorQueuedMsgPrevMsgSpec
PROOF BY DEF Init, SafeAcceptorQueuedMsgPrevMsgSpec, Acceptor, SentBy

LEMMA MsgsSafeAcceptorSpec1Init == Init => MsgsSafeAcceptorSpec1
PROOF BY DEF Init, MsgsSafeAcceptorSpec1, SentBy

LEMMA MsgsSafeAcceptorSpec3Init == Init => MsgsSafeAcceptorSpec3
PROOF BY DEF Init, MsgsSafeAcceptorSpec3, SentBy

LEMMA MsgsSafeAcceptorPrevRefSpecInit == Init => MsgsSafeAcceptorPrevRefSpec
PROOF BY DEF Init, MsgsSafeAcceptorPrevRefSpec, SentBy

LEMMA DecisionSpecInit == Init => DecisionSpec
PROOF BY DEF Init, DecisionSpec

LEMMA SafetyInit == Init => Safety
PROOF BY DEF Init, Safety

LEMMA FullSafetyInvariantInit == Init => FullSafetyInvariant
PROOF BY TypeOKInit,
         RecentMsgsSpecInit,
         KnownMsgsSpecInit,
         QueuedMsgSpec1Init,
         2aLearnerLoopSpecInit,
         SafeAcceptorPrevSpec1Init,
         SafeAcceptorPrevSpec2Init,
         SafeAcceptorQueuedMsgPrevMsgSpecInit,
         MsgsSafeAcceptorSpec1Init,
         MsgsSafeAcceptorSpec3Init,
         MsgsSafeAcceptorPrevRefSpecInit,
         DecisionSpecInit,
         SafetyInit
      DEF FullSafetyInvariant

LEMMA TypeOKStutter ==
    TypeOK /\ vars = vars' => TypeOK'
PROOF BY DEF TypeOK, vars

LEMMA RecentMsgsSpecStutter ==
    RecentMsgsSpec /\ vars = vars' => RecentMsgsSpec'
PROOF BY DEF RecentMsgsSpec, vars

LEMMA KnownMsgsSpecStutter ==
    KnownMsgsSpec /\ vars = vars' => KnownMsgsSpec'
PROOF BY Isa DEF KnownMsgsSpec, vars, Proper, WellFormed,
                 SameBallot, q, Fresh, Con, ConByQuorum, Con2as, Buried,
                 V, B, Get1a, SameBallot, ChainRef,
                 Caught, CaughtMsg

LEMMA QueuedMsgSpec1Stutter ==
    QueuedMsgSpec1 /\ vars = vars' => QueuedMsgSpec1' 
PROOF BY DEF QueuedMsgSpec1, vars

LEMMA 2aLearnerLoopSpecStutter ==
    2aLearnerLoopSpec /\ vars = vars' => 2aLearnerLoopSpec'
PROOF BY DEF 2aLearnerLoopSpec, vars

LEMMA SafeAcceptorPrevSpec1Stutter ==
    SafeAcceptorPrevSpec1 /\ vars = vars' => SafeAcceptorPrevSpec1'
PROOF BY DEF SafeAcceptorPrevSpec1, vars, SentBy

LEMMA SafeAcceptorPrevSpec2Stutter ==
    SafeAcceptorPrevSpec2 /\ vars = vars' => SafeAcceptorPrevSpec2'
PROOF BY DEF SafeAcceptorPrevSpec2, vars, SentBy

LEMMA SafeAcceptorQueuedMsgPrevMsgSpecStutter ==
    SafeAcceptorQueuedMsgPrevMsgSpec /\ vars = vars' => SafeAcceptorQueuedMsgPrevMsgSpec'
PROOF BY DEF SafeAcceptorQueuedMsgPrevMsgSpec, vars, SentBy

LEMMA MsgsSafeAcceptorSpec1Stutter ==
    MsgsSafeAcceptorSpec1 /\ vars = vars' => MsgsSafeAcceptorSpec1'
PROOF BY DEF MsgsSafeAcceptorSpec1, vars, SentBy

LEMMA MsgsSafeAcceptorSpec3Stutter ==
    MsgsSafeAcceptorSpec3 /\ vars = vars' => MsgsSafeAcceptorSpec3'
PROOF BY DEF MsgsSafeAcceptorSpec3, vars, SentBy

LEMMA MsgsSafeAcceptorPrevRefSpecStutter ==
    MsgsSafeAcceptorPrevRefSpec /\ vars = vars' => MsgsSafeAcceptorPrevRefSpec'
PROOF BY DEF MsgsSafeAcceptorPrevRefSpec, vars, SentBy

LEMMA DecisionSpecStutter ==
    DecisionSpec /\ vars = vars' => DecisionSpec'
PROOF BY Isa DEF DecisionSpec, vars, ChosenIn, Known2a, B, V, Get1a

LEMMA SafetyStutter ==
    Safety /\ vars = vars' => Safety'
PROOF BY DEF Safety, vars

LEMMA FullSafetyInvariantNext ==
    FullSafetyInvariant /\ [Next]_vars => FullSafetyInvariant'
PROOF
<1> SUFFICES ASSUME FullSafetyInvariant, [Next]_vars PROVE FullSafetyInvariant' OBVIOUS
<1>1. CASE Next
      BY <1>1,
         TypeOKInvariant,
         RecentMsgsSpecInvariant,
         KnownMsgsSpecInvariant,
         QueuedMsgSpec1Invariant,
         2aLearnerLoopSpecInvariant,
         MsgsSafeAcceptorSpecImpliesCaughtSpec,
         SafeAcceptorPrevSpec1Invariant,
         SafeAcceptorPrevSpec2Invariant,
         SafeAcceptorQueuedMsgPrevMsgSpecInvariant,
         MsgsSafeAcceptorSpec1Invariant,
         MsgsSafeAcceptorSpec3Invariant,
         MsgsSafeAcceptorPrevRefSpecInvariant,
         DecisionSpecInvariant,
         SafetyStep
      DEF FullSafetyInvariant
<1>2. CASE vars = vars'
      BY <1>2,
         TypeOKStutter,
         RecentMsgsSpecStutter,
         KnownMsgsSpecStutter,
         QueuedMsgSpec1Stutter,
         2aLearnerLoopSpecStutter,
         SafeAcceptorPrevSpec1Stutter,
         SafeAcceptorPrevSpec2Stutter,
         SafeAcceptorQueuedMsgPrevMsgSpecStutter,
         MsgsSafeAcceptorSpec1Stutter,
         MsgsSafeAcceptorSpec3Stutter,
         MsgsSafeAcceptorPrevRefSpecStutter,
         DecisionSpecStutter,
         SafetyStutter
      DEF FullSafetyInvariant
<1>3. QED BY <1>1, <1>2

THEOREM SafetyResult == Spec => []Safety
PROOF BY PTL, FullSafetyInvariantInit, FullSafetyInvariantNext
      DEF Spec, FullSafetyInvariant

=============================================================================
\* Modification History
\* Last modified Tue Jun 27 15:40:37 CEST 2023 by karbyshev
\* Created Tue Jun 20 00:28:26 CEST 2023 by karbyshev
