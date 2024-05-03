----------------------- MODULE HPaxos_chain_2a_proof ------------------------
EXTENDS HPaxos_chain_2a, Sequences, NaturalsInduction, WellFoundedInduction, TLAPS

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

LEMMA Message_prev ==
    ASSUME NEW m \in Message
    PROVE  m.prev \in Message \cup {NoMessage}
PROOF
<1> DEFINE P(j) ==  \A mm \in MessageRec[j] : mm.prev \in Message \cup {NoMessage}
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j)
    BY RefCardinalitySpec DEF Message, MessageDepthRange
<1>0. P(0)
      BY MessageRec_eq0 DEF MessageRec0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
  <2> SUFFICES ASSUME NEW mm \in MessageRec[k+1],
                      mm.prev # NoMessage
               PROVE  mm.prev \in Message
      OBVIOUS
  <2> CASE mm \in MessageRec[k]
      BY <1>1
  <2> CASE mm \notin MessageRec[k]
     <3> mm.prev \in MessageRec[k] \cup {NoMessage}
         BY MessageRec_eq1, Isa DEF MessageRec1
     <3> QED BY RefCardinalitySpec DEF MessageDepthRange, Message
  <2> QED BY MessageRec_eq1 DEF MessageRec1
<1>2. HIDE DEF P 
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

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
        BY <1>0, <1>2, MessageRec_eq1, MessageRec_ref1, FinSubset_sub, MaxRefCardinalityAssumption
        DEF MessageRec1, RefCardinality
  <2>10. QED BY <2>1, <1>0, <1>2
<1>10. QED BY <1>1, <1>2

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
             /\ m.lrn \in SUBSET Learner
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
               /\ x.lrn \in SUBSET Learner
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
                         /\ x.lrn \in SUBSET Learner
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
                     lrn : SUBSET Learner,
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
(* Transitive references of prev *)

LEMMA PrevTranBound_def ==
    PrevTranBound = [n \in Nat |->
                    IF n = 0
                    THEN PrevTranBound0
                    ELSE PrevTranBound1(PrevTranBound[n-1], n)]
PROOF BY NatInductiveDef
DEF NatInductiveDefHypothesis, NatInductiveDefConclusion, PrevTranBound

LEMMA PrevTran_spec ==
    ASSUME NEW m \in Message
    PROVE  /\ \A n \in Nat : PrevTranBound[n][m] \subseteq PrevTran(m)
           /\ \A r \in PrevTran(m) : \E n \in Nat : r \in PrevTranBound[n][m]
PROOF BY DEF PrevTran, PrevTranDepthRange, MessageDepthRange

LEMMA PrevTranBound_eq0 ==
    PrevTranBound[0] = [m \in Message |-> {m}]
PROOF BY PrevTranBound_def DEF PrevTranBound0

LEMMA PrevTranBound_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE  PrevTranBound[n] =
            [m \in Message |-> {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTranBound[n-1][m.prev]]
PROOF BY PrevTranBound_def, Zenon DEF PrevTranBound1

LEMMA PrevTranBound_eq1_prev ==
    ASSUME NEW n \in Nat, n # 0,
           NEW m \in Message, m.prev # NoMessage
    PROVE  PrevTranBound[n][m] = {m} \cup PrevTranBound[n-1][m.prev]
PROOF BY PrevTranBound_eq1, Zenon

LEMMA PrevTranBound_refl ==
    ASSUME NEW n \in Nat,
           NEW m \in Message 
    PROVE  m \in PrevTranBound[n][m]
<1> CASE n = 0
    BY PrevTranBound_eq0
<1> CASE n # 0
    BY PrevTranBound_eq1, Isa
<1> QED OBVIOUS

LEMMA PrevTran_refl ==
    ASSUME NEW m \in Message PROVE m \in PrevTran(m)
PROOF BY PrevTranBound_eq0 DEF PrevTran, PrevTranDepthRange, MessageDepthRange

LEMMA PrevTran_eq ==
    ASSUME NEW m \in Message
    PROVE  PrevTran(m) = {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTran(m.prev)
PROOF
<1>1. PrevTran(m) \subseteq {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTran(m.prev)
  <2> SUFFICES ASSUME NEW x \in PrevTran(m)
               PROVE  x \in {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTran(m.prev)
      OBVIOUS
  <2> PICK n \in Nat : x \in PrevTranBound[n][m]
      BY PrevTran_spec
  <2> CASE n = 0
      BY PrevTranBound_eq0
  <2> CASE n # 0
    <3> CASE x # m
      <4> m.prev # NoMessage
          BY PrevTranBound_eq1, Isa
      <4> x \in PrevTranBound[n-1][m.prev]
          BY PrevTranBound_eq1, Isa
      <4> QED BY PrevTran_spec, MessageTypeSpec
    <3> QED OBVIOUS
  <2> QED OBVIOUS
<1>2. ({m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTran(m.prev)) \subseteq PrevTran(m)
  <2> SUFFICES ASSUME NEW x \in {m} \cup IF m.prev = NoMessage THEN {} ELSE PrevTran(m.prev)
               PROVE  x \in PrevTran(m)
      OBVIOUS
  <2> CASE x # m
    <3> m.prev # NoMessage
        OBVIOUS
    <3> x \in PrevTran(m.prev)
        OBVIOUS
    <3> PICK n \in Nat : x \in PrevTranBound[n][m.prev]
        BY PrevTran_spec, MessageTypeSpec
    <3> (n + 1) - 1 = n OBVIOUS
    <3> x \in PrevTranBound[n+1][m]
        BY PrevTranBound_eq1, Isa
    <3> QED BY PrevTran_spec
  <2> QED BY PrevTran_refl
<1> QED BY <1>1, <1>2

LEMMA PrevTran_1a ==
    ASSUME NEW m \in Message, m.type = "1a"
    PROVE  PrevTran(m) = {m}
PROOF BY PrevTran_eq, MessageTypeSpec

LEMMA PrevTranBound_Message ==
    ASSUME NEW m1 \in Message,
           NEW n \in Nat
    PROVE  PrevTranBound[n][m1] \in SUBSET Message
PROOF
<1> DEFINE P(j) == \A x \in Message : PrevTranBound[j][x] \in SUBSET Message
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY DEF PrevTran
<1>0. P(0) BY PrevTranBound_eq0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
  <2> SUFFICES ASSUME NEW x \in Message
               PROVE PrevTranBound[k + 1][x] \in SUBSET Message
      OBVIOUS
  <2> SUFFICES ASSUME x.prev # NoMessage
               PROVE PrevTranBound[k][x.prev] \in SUBSET Message
      BY PrevTranBound_eq1, Isa
  <2>3. QED BY <1>1, Message_prev
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA PrevTran_Message ==
    ASSUME NEW m1 \in Message
    PROVE  PrevTran(m1) \in SUBSET Message
PROOF BY PrevTran_spec, PrevTranBound_Message

LEMMA PrevTranBound_monotone_1 ==
    ASSUME NEW n \in Nat, NEW m \in Message
    PROVE  PrevTranBound[n][m] \subseteq PrevTranBound[n+1][m]
PROOF
<1> DEFINE P(j) == \A mm \in Message :
                    PrevTranBound[j][mm] \subseteq PrevTranBound[j+1][mm]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) BY PrevTranBound_eq0, PrevTranBound_eq1, Isa
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k+1)
  <2> SUFFICES ASSUME NEW mm \in Message
               PROVE PrevTranBound[k+1][mm] \subseteq PrevTranBound[(k+1)+1][mm]
      OBVIOUS
   <2> CASE mm.prev = NoMessage
       BY PrevTranBound_eq1, Isa
   <2> CASE mm.prev # NoMessage
     <3> mm.prev \in Message
         BY Message_prev
     <3>1. SUFFICES
        PrevTranBound[k][mm.prev] \subseteq PrevTranBound[k+1][mm.prev] 
        BY PrevTranBound_eq1_prev, PrevTranBound_Message, Isa
     <3> QED BY <1>1
  <2> QED OBVIOUS
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA PrevTranBound_monotone ==
    \A n, m \in Nat : n <= m =>
        \A mm \in Message :
            PrevTranBound[n][mm] \subseteq PrevTranBound[m][mm]
PROOF
<1> DEFINE P(m) == \A n \in Nat : n < m =>
                    \A mm \in Message : PrevTranBound[n][mm] \subseteq PrevTranBound[m][mm]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1) BY <1>1, PrevTranBound_monotone_1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_prev_PrevTranBound1 ==
    ASSUME NEW m \in Message, m.prev # NoMessage
    PROVE  m.prev \in PrevTranBound[1][m]
PROOF
<1> m.prev \in Message BY Message_prev
<1> QED BY PrevTranBound_eq1, PrevTranBound_eq0, Isa

LEMMA PrevTranBound_trans ==
    ASSUME NEW n1 \in Nat, NEW n2 \in Nat,
           NEW m1 \in Message,
           NEW m2 \in PrevTranBound[n1][m1],
           NEW m3 \in PrevTranBound[n2][m2]
    PROVE  m3 \in PrevTranBound[n1 + n2][m1]
PROOF
<1>0. DEFINE P(n) ==
        \A k \in Nat :
        \A x \in Message :
        \A y \in PrevTranBound[n][x] :
        \A z \in PrevTranBound[k][y] :
            z \in PrevTranBound[n + k][x]
<1>1. SUFFICES \A n \in Nat : P(n) OBVIOUS
<1>2. P(0) BY PrevTranBound_eq0
<1>3. ASSUME NEW n \in Nat, P(n) PROVE P(n+1)
  <2> SUFFICES ASSUME NEW k \in Nat, NEW x \in Message,
                            NEW y \in PrevTranBound[n + 1][x], NEW z \in PrevTranBound[k][y]
                 PROVE  z \in PrevTranBound[n + 1 + k][x]
      OBVIOUS
  <2>1. CASE y = x
        BY <2>1, PrevTranBound_monotone
  <2>2. CASE y # x
     <3> x.prev # NoMessage
         BY <2>2, PrevTranBound_eq1, Isa
     <3> x.prev \in Message
         BY Message_prev
     <3> y \in PrevTranBound[n][x.prev]
         BY <2>2, PrevTranBound_eq1_prev
     <3> z \in PrevTranBound[n + k][x.prev]
         BY <1>3
     <3> QED BY PrevTranBound_eq1_prev
  <2> QED BY <2>1, <2>2
<1>4. HIDE DEF P
<1>5. QED BY <1>2, <1>3, NatInduction, Isa

LEMMA PrevTran_trans ==
    ASSUME NEW m1 \in Message, NEW m2 \in PrevTran(m1), NEW m3 \in PrevTran(m2)
    PROVE  m3 \in PrevTran(m1)
PROOF
<1>0. PICK n1 \in Nat : m2 \in PrevTranBound[n1][m1]
      BY PrevTran_spec
<1>1. PICK n2 \in Nat : m3 \in PrevTranBound[n2][m2]
      BY PrevTranBound_Message, PrevTran_spec
<1>2. m3 \in PrevTranBound[n2 + n1][m1]
      BY PrevTranBound_trans, <1>0, <1>1
<1>3. QED BY <1>2, PrevTran_spec

LEMMA Message_prev_PrevTran ==
    ASSUME NEW m \in Message, m.prev # NoMessage
    PROVE  m.prev \in PrevTran(m)
PROOF BY Message_prev_PrevTranBound1, Zenon
      DEF PrevTran, PrevTranDepthRange, MessageDepthRange

\*LEMMA MessageRec0_PrevTran ==
\*    ASSUME NEW m1 \in MessageRec[0], NEW m2 \in PrevTran(m1)
\*    PROVE  m1 = m2
\*PROOF
\*<1> m1 \in Message
\*    BY Message_spec DEF MessageDepthRange
\*<1> PICK k \in Nat : m2 \in PrevTranBound[k][m1]
\*    BY PrevTran_spec
\*<1> m2 \in Message
\*    BY PrevTran_Message
\*<1>1. CASE k = 0
\*      BY PrevTranBound_eq0, <1>1
\*<1>2. CASE k # 0 /\ m1 # m2
\*  <2> m1.prev # NoMessage
\*      BY <1>2, PrevTranBound_eq1, Isa
\*  <2> QED
\*      BY MessageRec_eq0 DEF MessageRec0
\*<1>3. QED BY <1>1, <1>2

-----------------------------------------------------------------------------
LEMMA CaughtMsgSpec ==
    ASSUME NEW M \in Message
    PROVE  /\ CaughtMsg(M) \in SUBSET Message
           /\ \A X \in CaughtMsg(M) : X.type # "1a"
BY Tran_Message DEF CaughtMsg

LEMMA CaughtMsgEffSpec ==
    ASSUME NEW M \in Message
    PROVE  /\ CaughtMsg0(M) \in SUBSET Message
           /\ \A X \in CaughtMsg0(M) : X.type # "1a"
BY Tran_Message DEF CaughtMsg0

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

LEMMA V_def ==
    ASSUME BVal \in [Ballot -> Value],
           NEW m \in Message,
           NEW b \in Ballot, B(m, b)
    PROVE V(m, BVal[b])
PROOF BY Get1a_TypeOK DEF V, B

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
LEMMA WellFormedConditionEquiv1 ==
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

LEMMA WellFormedConditionEquiv2 ==
    ASSUME NEW m \in Message, m.type = "1b"
    PROVE (\A y \in Tran(m) :
            m # y /\
            (\E bm \in Ballot : B(m, bm)) /\
            (\E by \in Ballot : B(y, by)) /\
            SameBallot(m, y) => y.type = "1a")
          <=>
          (\A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm)
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

LEMMA WellFormedConditionEquiv3 ==
    ASSUME NEW m \in Message, m.type = "1b"
    PROVE (\A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by # bm)
          <=>
          (\A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm)
PROOF BY TranBallot DEF Ballot

LEMMA WellFormedCondition4 ==
    ASSUME NEW m \in Message,
           \A y \in m.ref :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
    PROVE \A y \in Tran(m) :
            m # y /\ y.type # "1a" =>
            \A bm, by \in Ballot :
                B(m, bm) /\ B(y, by) => by < bm
\*PROOF BY Message_ref, Tran_Message, Tran_eq, TranBallot DEF Ballot
OMITTED

-----------------------------------------------------------------------------
TypeOK ==
    /\ msgs \in SUBSET Message
    /\ known_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ recent_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ prev_msg \in [Acceptor -> Message \cup {NoMessage}]
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

CaughtEffSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        \A M \in known_msgs[AL] :
            Caught0(M) \cap SafeAcceptor = {}

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
            /\ \A m \in SentBy(A) : m \in PrevTran(prev_msg[A])

\*SafeAcceptorQueuedMsgPrevMsgSpec ==
\*    \A A \in SafeAcceptor :
\*        /\ SentBy(A) # {} /\ queued_msg[A] = NoMessage =>
\*            prev_msg[A] \in recent_msgs[A]
\*        /\ queued_msg[A] # NoMessage => queued_msg[A] = prev_msg[A]

RecentMsgsUniquePreviousMessageSpec ==
    \A A \in SafeAcceptor :
        \A x, y \in recent_msgs[A] :
            x.type # "1a" /\ y.type # "1a" /\
            x.acc = A /\ y.acc = A =>
            x = y

MsgsSafeAcceptorSpec3 ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1.prev = m2.prev => m1 = m2

MsgsSafeAcceptorPrevRefSpec ==
    \A A \in SafeAcceptor :
        \A m \in SentBy(A) :
            m.prev # NoMessage => m.prev \in m.ref

MsgsSafeAcceptorPrevTranSpec ==
    \A A \in SafeAcceptor :
        \A m1 \in SentBy(A) :
            \A m2 \in PrevTran(m1) :
                m2 \in Tran(m1)

MsgsSafeAcceptorPrevTranLinearSpec ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in SentBy(A) :
            m1 \in PrevTran(m2) \/ m2 \in PrevTran(m1)

\*QueuedMsgSpec1 ==
\*    \A A \in SafeAcceptor :
\*        queued_msg[A] # NoMessage =>
\*        /\ queued_msg[A].type = "1b"
\*        /\ recent_msgs[A] = {}

\*QueuedMsgSpec2 ==
\*    \A A \in SafeAcceptor :
\*        \A m \in Sent1bBy(A) :
\*            m \notin known_msgs[A] =>
\*            queued_msg[A] = m

\*2aLearnerLoopSpec ==
\*    \A A \in SafeAcceptor :
\*        2a_lrn_loop[A] = TRUE =>
\*        queued_msg[A] = NoMessage

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
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> m1a \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Recv, TypeOK
  <2> recent_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
    <3> QED BY WellFormedMessage DEF TypeOK
  <2> QED BY DEF TypeOK, Send
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> USE DEF Process1b
  <2> acc \in Acceptor BY DEF Acceptor
  <2> msg \in Message BY DEF TypeOK
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF Send, TypeOK
  <2> known_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY DEF Recv, TypeOK
  <2> recent_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
    <3>1. CASE (\A mb, b \in Ballot : MaxBal(acc, mb) /\ B(msg, b) => mb =< b)
      <4> PICK ll \in SUBSET Learner :
          LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                        prev |-> prev_msg[acc],
                        ref |-> recent_msgs[acc] \cup {msg, prev_msg[acc]}] IN
            /\ WellFormed(new2a)
            /\ Send(new2a)
            /\ recent_msgs' = [recent_msgs EXCEPT ![acc] = {}]
            /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
          BY <3>1
      <4> QED BY DEF TypeOK
    <3>2. CASE ~(\A mb, b \in Ballot : MaxBal(acc, mb) /\ B(msg, b) => mb =< b)
        BY <3>2 DEF TypeOK
    <3> QED BY <3>1, <3>2
  <2> QED BY DEF TypeOK, Send
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> USE DEF Process2a
  <2> QED BY DEF TypeOK, Recv
<1>7. CASE LearnerAction
      BY <1>7, Isa DEF LearnerAction, LearnerRecv, LearnerDecide, Recv, TypeOK
<1>8. CASE FakeAcceptorAction
      BY <1>8, WellFormedMessage, Zenon
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, Send, TypeOK
<1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8
          DEF Next, AcceptorProcessAction

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
                       ref |-> recent_msgs[acc] \cup {m1a, prev_msg[acc]}]
  <2> CASE WellFormed(new1b)
    <3> QED BY Zenon DEF Recv, TypeOK
  <2> CASE ~WellFormed(new1b)
    <3> recent_msgs' = [recent_msgs EXCEPT ![acc] =
                            recent_msgs[acc] \cup {m1a}]
        BY DEF TypeOK
    <3> QED BY Zenon DEF Recv, TypeOK
  <2> QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> USE DEF Process1b
\*  <2> acc \in Acceptor BY DEF Acceptor
  <2> m1b \in Message BY DEF TypeOK
  <2> CASE ~(\A mb, b \in Ballot : MaxBal(acc, mb) /\ B(m1b, b) => mb =< b)
    <3> recent_msgs' = [recent_msgs EXCEPT ![acc] =
                            recent_msgs[acc] \cup {m1b}]
        BY DEF TypeOK
    <3> QED BY Zenon DEF Recv, TypeOK
  <2> CASE (\A mb, b \in Ballot : MaxBal(acc, mb) /\ B(m1b, b) => mb =< b)
    <3> PICK ll \in SUBSET Learner :
        recent_msgs' = [recent_msgs EXCEPT ![acc] = {}]
      <4> QED BY Zenon
    <3> QED BY Zenon DEF Recv, TypeOK
  <2> QED OBVIOUS
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, m2a \in msgs : Process2a(acc, m2a)
      BY <1>4
  <2> USE DEF Process2a
  <2> QED BY Zenon DEF Recv, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
  <2> PICK lrn \in Learner, msg \in msgs : LearnerRecv(lrn, msg)
      BY <1>7
  <2> QED BY Zenon DEF LearnerRecv, Recv, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY Zenon, <1>8 DEF LearnerDecide, TypeOK
<1>9. CASE FakeAcceptorAction
      BY Zenon, <1>9
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
           DEF Next, AcceptorProcessAction, LearnerAction

LEMMA WellFormed_monotone ==
    ASSUME NEW m \in Message, WellFormed(m), BVal' = BVal
    PROVE WellFormed(m)'
PROOF BY Isa DEF WellFormed, q, Fresh, Con2as, Buried, V

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
  <2> QED BY DEF Process1a, Recv, TypeOK
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, m1b \in msgs : Process1b(acc, m1b)
      BY <1>3
  <2> QED BY DEF Process1b, Recv, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, m2a \in msgs : Process2a(acc, m2a)
      BY <1>4
  <2> QED BY DEF Process2a, Recv, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7 DEF LearnerRecv, Recv, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8 DEF LearnerDecide, TypeOK
<1>9. CASE FakeAcceptorAction
      BY <1>9 DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
           DEF Next, AcceptorProcessAction, LearnerAction

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
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> QED BY KnownMsgMonotone DEF Process1b, V, TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> QED BY KnownMsgMonotone DEF Process2a, V, TypeOK
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, KnownMsgMonotone DEF LearnerRecv, V, TypeOK
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
      BY <1>8, KnownMsgMonotone, Zenon DEF LearnerDecide, V, TypeOK
<1>9. CASE FakeAcceptorAction
      BY <1>9, KnownMsgMonotone
      DEF FakeAcceptorAction, FakeSend1b, FakeSend2a, V, TypeOK
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
          DEF Next, AcceptorProcessAction, LearnerAction

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
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> QED BY Known2aMonotone DEF Process1b
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> QED BY Known2aMonotone DEF Process2a
<1>7. CASE \E lrn \in Learner : \E m \in msgs : LearnerRecv(lrn, m)
      BY <1>7, Known2aMonotone DEF LearnerRecv
<1>8. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, BVal >>
      BY <1>8, Zenon DEF LearnerDecide
  <2>0. QED BY Known2aMonotone DEF TypeOK
<1>9. CASE FakeAcceptorAction
      BY <1>9, Known2aMonotone DEF FakeAcceptorAction, FakeSend1b, FakeSend2a
<1>10. QED BY <1>1, <1>2, <1>3, <1>4, <1>7, <1>8, <1>9
          DEF Next, AcceptorProcessAction, LearnerAction

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
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2>1. CASE acc = A
    <3> DEFINE new1b == [type |-> "1b", acc |-> acc, prev |-> prev_msg[acc],
                         ref |-> recent_msgs[acc] \cup {m1a, prev_msg[acc]}]
    <3> CASE WellFormed(new1b)
        <4> prev_msg' = [prev_msg EXCEPT ![acc] = new1b]
            OBVIOUS
        <4> new1b \in Message BY <2>1 DEF Send, TypeOK
        <4> new1b \in msgs' BY <2>1 DEF Send
        <4> QED BY <2>1, NoMessageIsNotAMessage DEF SentBy, Send, TypeOK
    <3> CASE ~WellFormed(new1b)
        <4> QED BY <2>1 DEF SentBy, TypeOK
    <3> QED OBVIOUS
  <2>2. CASE acc # A
        BY <2>2 DEF SentBy, Send, TypeOK
  <2> QED BY <2>1, <2>2
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> USE DEF Process1b
  <2> CASE (\A mb, b \in Ballot : MaxBal(acc, mb) /\ B(msg, b) => mb =< b)
    <3> PICK ll \in SUBSET Learner :
          LET new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                        prev |-> prev_msg[acc],
                        ref |-> recent_msgs[acc] \cup {msg, prev_msg[acc]}] IN
            /\ WellFormed(new2a)
            /\ Send(new2a)
            /\ prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
        OBVIOUS
    <3> DEFINE new2a == [type |-> "2a", lrn |-> ll, acc |-> acc,
                        prev |-> prev_msg[acc],
                        ref |-> recent_msgs[acc] \cup {msg, prev_msg[acc]}]
    <3> prev_msg' = [prev_msg EXCEPT ![acc] = new2a]
        OBVIOUS
    <3> new2a \in Message BY DEF Send, TypeOK
    <3> new2a \in msgs' BY DEF Send
    <3> QED BY NoMessageIsNotAMessage DEF SentBy, Send, TypeOK
  <2> CASE ~(\A mb, b \in Ballot : MaxBal(acc, mb) /\ B(msg, b) => mb =< b)
    <3> QED BY DEF SentBy
  <2> QED OBVIOUS
<1>4. CASE \E a \in SafeAcceptor : \E m \in msgs : Process2a(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process2a(acc, msg)
      BY <1>4
  <2> QED BY DEF Process2a, SentBy, Send, TypeOK
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
<1> QED BY Zenon, <1>1, <1>2, <1>3, <1>4, <1>6, <1>7, <1>8
        DEF Next, AcceptorProcessAction, FakeAcceptorAction

=============================================================================
\* Modification History
\* Last modified Fri May 03 16:59:22 CEST 2024 by karbyshev
\* Created Tue Jun 20 00:28:26 CEST 2023 by karbyshev
