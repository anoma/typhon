--------------------------- MODULE HPaxosTR_proof ---------------------------
EXTENDS HPaxosTR, Sequences, NaturalsInduction, WellFoundedInduction, TLAPS

-----------------------------------------------------------------------------
LEMMA FinSubset_sub ==
    ASSUME NEW S, NEW R \in SUBSET Nat, NEW F \in FINSUBSET(S, R)
    PROVE F \subseteq S
PROOF BY DEF Range, FINSUBSET

\*LEMMA FinSubset_sub ==
\*    ASSUME NEW S, NEW K \in Nat, NEW F \in FINSUBSET(S, K)
\*    PROVE F \subseteq S
\*PROOF BY DEF Range, FINSUBSET

\*LEMMA FinSubset_finite ==
\*    ASSUME NEW S, NEW K \in Nat, NEW F \in FINSUBSET(S, K)
\*    PROVE IsFiniteSet(F)
\*PROOF BY DEF FINSUBSET, IsFiniteSet, Range
\*
\*LEMMA IsFiniteSet_add ==
\*    ASSUME NEW S, IsFiniteSet(S), NEW x
\*    PROVE IsFiniteSet(S \cup {x})
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

LEMMA EntanglementSym ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent
    PROVE <<L2, L1>> \in Ent
PROOF BY LearnerGraphAssumptionSymmetry DEF Ent

LEMMA EntanglementSelf ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, <<L1, L2>> \in Ent
    PROVE <<L1, L1>> \in Ent
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

LEMMA EntanglementTransitive ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner, NEW L3 \in Learner,
    <<L1, L2>> \in Ent, <<L2, L3>> \in Ent
    PROVE <<L1, L3>> \in Ent
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
    PROVE MessageRec[n] = MessageRec1(MessageRec[n-1], n)
PROOF BY MessageRec_def DEF MessageRec1

LEMMA MessageRec_monotone_1 ==
    ASSUME NEW n \in Nat
    PROVE MessageRec[n] \subseteq MessageRec[n+1]
PROOF BY MessageRec_eq1 DEF MessageRec1

LEMMA MessageRec_monotone ==
    \A n, m \in Nat : n <= m => MessageRec[n] \subseteq MessageRec[m]
PROOF
<1> DEFINE P(m) == \A n \in Nat : n < m => MessageRec[n] \subseteq MessageRec[m]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1) BY <1>1, MessageRec_monotone_1
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA MessageRec_ref0 ==
    ASSUME NEW m \in MessageRec[0]
    PROVE m.ref = {}
PROOF BY MessageRec_def DEF MessageRec0

LEMMA MessageRec_ref1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE \A m \in MessageRec[n] : m.ref \subseteq MessageRec[n-1]
PROOF
<1> DEFINE P(j) == j # 0 =>
                \A mm \in MessageRec[j] : mm.ref \subseteq MessageRec[j-1]
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) OBVIOUS
<1>0. P(0) OBVIOUS
<1>1. ASSUME NEW m \in Nat, P(m) PROVE P(m+1)
  <2> SUFFICES ASSUME NEW mm \in MessageRec[m+1]
               PROVE mm.ref \subseteq MessageRec[m]
      OBVIOUS
  <2>1. CASE m = 0
        BY <2>1, MessageRec_eq1, MessageRec_ref0, FinSubset_sub
           DEF MessageRec1, RefCardinality
  <2>2. CASE m # 0
        BY <1>1, <2>2, MessageRec_eq1, MessageRec_monotone, FinSubset_sub
           DEF MessageRec1, RefCardinality
  <2>3. QED BY <2>1, <2>2
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA Message_ref ==
    ASSUME NEW m \in Message
    PROVE m.ref \subseteq Message
PROOF BY MessageRec_ref0, MessageRec_ref1, Message_spec DEF MessageDepthRange

LEMMA MessageRec_min ==
    ASSUME NEW m \in Message
    PROVE \E n \in Nat :
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
    PROVE m \notin m.ref
PROOF
<1>0. PICK n \in Nat :
        /\ m \in MessageRec[n]
        /\ \A k \in 0 .. n-1 : m \notin MessageRec[k]
      BY MessageRec_min
<1>1. CASE n = 0 BY <1>0, <1>1, MessageRec_eq0 DEF MessageRec0
<1>2. CASE n # 0 /\ m \in m.ref
  <2>1. m.ref \in SUBSET MessageRec[n-1]
        BY <1>0, <1>2, MessageRec_eq1, FinSubset_sub DEF MessageRec1, RefCardinality
  <2>10. QED BY <2>1, <1>0, <1>2
<1>10. QED BY <1>1, <1>2

\*LEMMA Message_ref_acyclic_2 ==
\*    ASSUME NEW m1 \in Message, NEW m2 \in m1.ref
\*    PROVE m1 \notin m2.ref
\*PROOF
\*<1> SUFFICES ASSUME NEW x \in Message,
\*                    NEW y \in x.ref,
\*                    x \in y.ref
\*             PROVE FALSE
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
\*    PROVE [type |-> "1b", acc |-> A, ref |-> M] \in Message
\*PROOF
\*<1> PICK n \in Nat : \A m \in M : m \in MessageRec[n] BY Message_finite_1
\*<1> [type |-> "1b", acc |-> A, ref |-> M] \in MessageRec[n + 1]
\*    BY MessageRec_eq1 DEF MessageRec1
\*<1>10. QED

-----------------------------------------------------------------------------
LEMMA MessageTypeSpec ==
    ASSUME NEW m \in Message
    PROVE \/ /\ m.type = "1a"
             /\ m.bal \in Ballot
             /\ m.ref = {}
          \/ /\ m.type = "1b"
             /\ m.acc \in Acceptor
             /\ m.ref \in SUBSET Message
          \/ /\ m.type = "2a"
             /\ m.lrn \in Learner
             /\ m.acc \in Acceptor
             /\ m.ref \in SUBSET Message
PROOF
<1> DEFINE P(n) ==
        \A x \in MessageRec[n] :
            \/ /\ x.type = "1a"
               /\ x.bal \in Ballot
               /\ x.ref = {}
            \/ /\ x.type = "1b"
               /\ x.acc \in Acceptor
               /\ x.ref \in SUBSET Message
            \/ /\ x.type = "2a"
               /\ x.lrn \in Learner
               /\ x.acc \in Acceptor
               /\ x.ref \in SUBSET Message
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j) BY Message_spec
<1>0. P(0) BY MessageRec_eq0 DEF MessageRec0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  BY <1>1, MessageRec_eq1, Message_spec, FinSubset_sub DEF MessageRec1, RefCardinality
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
    PROVE
    /\ \A n \in Nat : TranBound[n][m] \subseteq Tran(m)
    /\ \A r \in Tran(m) : \E n \in Nat : r \in TranBound[n][m]
PROOF BY DEF Tran, TranDepthRange, MessageDepthRange

LEMMA TranBound_eq0 ==
    TranBound[0] = [m \in Message |-> {m}]
PROOF BY TranBound_def DEF TranBound0

LEMMA TranBound_eq1 ==
    ASSUME NEW n \in Nat, n # 0
    PROVE TranBound[n] =
            [m \in Message |-> {m} \cup UNION {TranBound[n-1][r] : r \in m.ref}]
PROOF BY TranBound_def, Zenon DEF TranBound1

LEMMA Tran_refl ==
    ASSUME NEW m \in Message PROVE m \in Tran(m)
PROOF BY TranBound_eq0 DEF Tran, TranDepthRange, MessageDepthRange

LEMMA Tran_1a ==
    ASSUME NEW m \in Message, m.type = "1a"
    PROVE Tran(m) = {m}
PROOF
<1> DEFINE P(n) == TranBound[n][m] = {m}
<1> SUFFICES ASSUME NEW j \in Nat PROVE P(j)
    BY DEF Tran, TranDepthRange, MessageDepthRange
<1>0. P(0) BY TranBound_eq0
<1>1. ASSUME NEW k \in Nat, P(k) PROVE P(k + 1)
  <2> SUFFICES TranBound[k + 1][m] = {m} OBVIOUS
  <2> m.ref = {} BY MessageTypeSpec
  <2> QED BY <1>1, TranBound_eq1, Isa
<1>2. HIDE DEF P
<1>3. QED BY <1>0, <1>1, NatInduction, Isa

LEMMA TranBound_Message ==
    ASSUME NEW m1 \in Message,
           NEW n \in Nat
    PROVE TranBound[n][m1] \in SUBSET Message
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
    PROVE Tran(m1) \in SUBSET Message
PROOF BY Tran_spec, TranBound_Message

LEMMA TranBound_monotone_1 ==
    ASSUME NEW n \in Nat, NEW m \in Message
    PROVE TranBound[n][m] \subseteq TranBound[n+1][m]
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

LEMMA Message_ref_TranBound1 == \* TODO remove
    ASSUME NEW m1 \in Message
    PROVE m1.ref \in SUBSET TranBound[1][m1]
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
                 PROVE z \in TranBound[n + 1 + k][x]
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
    ASSUME NEW m1 \in Message, NEW m2 \in m1.ref
    PROVE m2 \in Tran(m1)
PROOF BY Message_ref_TranBound1, Zenon
      DEF Tran, TranDepthRange, MessageDepthRange

LEMMA MessageRec0_Tran ==
    ASSUME NEW m1 \in MessageRec[0], NEW m2 \in Tran(m1)
    PROVE m1 = m2
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
    PROVE m2 \in MessageRec[n]
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
               PROVE y \in MessageRec[k]
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
    PROVE m \notin Tran(r)
PROOF
<1> r \in Message BY Message_ref
<1> SUFFICES ASSUME NEW n \in Nat,
                    NEW x \in Message,
                    NEW y \in x.ref, x \in Tran(y)
             PROVE x \in MessageRec[n] => FALSE
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
    PROVE m1 = m2
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
    PROVE /\ CaughtMsg(M) \in SUBSET Message
          /\ \A X \in CaughtMsg(M) : X.type # "1a"
BY Tran_Message DEF CaughtMsg

-----------------------------------------------------------------------------
Msg1aInv ==
    \A m1, m2 \in msgs :
        m1.type = "1a" /\ m2.type = "1a" /\ m1.bal = m2.bal => m1 = m2

\*Msg2aInv(m) ==
\*    /\ [lr |-> m.lr, bal |-> m.bal, val |-> m.val] \in votesSent[m.acc]
\*    /\ \E Q \in ByzQuorum :
\*        /\ [lr |-> m.lr, q |-> Q] \in TrustLive
\*        /\ \A ba \in Q :
\*            \E m2av \in received[m.acc] :
\*                /\ m2av.type = "2av"
\*                /\ m2av.lr = m.lr
\*                /\ m2av.acc = ba
\*                /\ m2av.bal = m.bal
\*                /\ m2av.val = m.val

-----------------------------------------------------------------------------
LEMMA Get1a_TypeOK ==
    ASSUME NEW m \in Message
    PROVE /\ Get1a(m) \subseteq Message
          /\ \A x \in Get1a(m) : x.bal \in Ballot
PROOF BY Tran_Message, MessageTypeSpec DEF Get1a

LEMMA Get1a_correct ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m), NEW y \in Get1a(m)
    PROVE x.bal = y.bal
PROOF BY Tran_Message, MessageTypeSpec DEF Get1a, Ballot

LEMMA B_func ==
    ASSUME NEW m \in Message,
           NEW b1 \in Ballot, B(m, b1),
           NEW b2 \in Ballot, B(m, b2)
    PROVE b1 = b2
PROOF BY DEF B, Get1a, Ballot

LEMMA B_def ==
    ASSUME NEW m \in Message,
           NEW x \in Get1a(m)
    PROVE \E b \in Ballot : B(m, b)
PROOF BY Get1a_correct, Get1a_TypeOK DEF B

LEMMA V_func ==
    ASSUME NEW m \in Message,
           NEW v1 \in Value, V(m, v1),
           NEW v2 \in Value, V(m, v2)
    PROVE v1 = v2
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

\*LEMMA q_ByzQuorum ==
\*    ASSUME NEW m \in Message
\*    PROVE q(m) \in ByzQuorum
\*PROOF BY DEF q, ByzQuorum

-----------------------------------------------------------------------------
\* vars == << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, decision >>
TypeOK ==
    /\ msgs \in SUBSET Message
    /\ known_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ recent_msgs \in [Acceptor \cup Learner -> SUBSET Message]
    /\ 2a_lrn_loop \in [Acceptor -> BOOLEAN]
    /\ processed_lrns \in [Acceptor -> SUBSET Learner]
    /\ decision \in [Learner \X Ballot -> SUBSET Value]
    /\ BVal \in [Ballot -> Value]

-----------------------------------------------------------------------------
RecentMsgSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ recent_msgs[AL] \in SUBSET known_msgs[AL]

KnownMsgSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        /\ known_msgs[AL] \in SUBSET msgs
        /\ \A M \in known_msgs[AL] :
            /\ Proper(AL, M)
            /\ WellFormed(M)
            /\ Tran(M) \in SUBSET known_msgs[AL]

CaughtSpec ==
    \A AL \in SafeAcceptor \cup Learner :
        \A M \in known_msgs[AL] :
            Caught(M) \cap SafeAcceptor = {}

DecisionSpec ==
    \A L \in Learner : \A BB \in Ballot : \A VV \in Value :
        VV \in decision[L, BB] => ChosenIn(L, BB, VV)

SentBy(acc) == { mm \in msgs : mm.type # "1a" /\ mm.acc = acc }

RecentMsgsSafeAcceptorSpec ==
    \A A \in SafeAcceptor :
        SentBy(A) # {} =>
        \E m0 \in recent_msgs[A] :
            \A m1 \in SentBy(A) : m1 \in Tran(m0)

MsgsSafeAcceptorSpec ==
    \A A \in SafeAcceptor :
        \A m1, m2 \in msgs :
            m1.type # "1a" /\ m2.type # "1a" /\
            m1.acc = A /\ m2.acc = A =>
            m1 \in Tran(m2) \/ m2 \in Tran(m1)

LEMMA WellFormedMessage ==
    ASSUME NEW M, WellFormed(M) PROVE M \in Message
BY DEF WellFormed

LEMMA TypeOKInvariant == TypeOK /\ Next => TypeOK'
PROOF
<1> SUFFICES ASSUME TypeOK, Next PROVE TypeOK' OBVIOUS
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot, val \in Value : Send1a(bal, val)
      BY <1>1 DEF ProposerSendAction
  <2> [type |-> "1a", bal |-> bal, ref |-> {}] \in Message
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
      BY Zenon DEF Recv, TypeOK
  <2> recent_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
    <3> DEFINE new1b == [type |-> "1b", acc |-> acc,
                         ref |-> recent_msgs[acc] \cup {msg}]
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
      BY DEF Recv, TypeOK
  <2> QED BY Zenon DEF TypeOK
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> acc \in Acceptor BY DEF Acceptor
  <2> msgs' \in SUBSET Message
      BY WellFormedMessage, Zenon DEF Send, TypeOK
  <2> 2a_lrn_loop' \in [Acceptor -> BOOLEAN]
      BY Zenon DEF TypeOK
  <2> recent_msgs' \in [Acceptor \cup Learner -> SUBSET Message]
      BY CVC4, WellFormedMessage DEF TypeOK
  <2> processed_lrns' \in [Acceptor -> SUBSET Learner]
      BY Isa DEF TypeOK
  <2>1. QED BY DEF TypeOK
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5, Zenon DEF Process1bLearnerLoopDone, TypeOK
<1>6. CASE LearnerAction
      BY <1>6, Isa DEF LearnerAction, LearnerRecv, LearnerDecide, Recv, TypeOK
<1>7. CASE FakeAcceptorAction
      BY <1>7 DEF FakeAcceptorAction, FakeSend, Send, TypeOK
<1>8. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop

LEMMA RecentMsgsSafeAcceptorSpecInvariant ==
    TypeOK /\ Next /\ RecentMsgsSafeAcceptorSpec => RecentMsgsSafeAcceptorSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next,
                    RecentMsgsSafeAcceptorSpec
             PROVE  RecentMsgsSafeAcceptorSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW mm \in SentBy(A)'
             PROVE \E m0 \in recent_msgs[A]' :
                        \A m1 \in SentBy(A)' : m1 \in Tran(m0)
    BY DEF RecentMsgsSafeAcceptorSpec
<1> A \in Acceptor BY DEF Acceptor
<1> mm \in msgs' /\ mm.type # "1a" /\ mm.acc = A BY DEF SentBy
<1> USE DEF RecentMsgsSafeAcceptorSpec
<1>1. CASE ProposerSendAction
  <2> PICK bal \in Ballot, val \in Value : Send1a(bal, val)
      BY <1>1 DEF ProposerSendAction
  <2> QED BY DEF Send1a, Send, SentBy
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> CASE acc # A
    <3> SentBy(A) = SentBy(A)'
        BY DEF Send, SentBy
    <3>1. CASE SentBy(A) = {}
          BY <3>1 DEF Send, SentBy
    <3>2. CASE SentBy(A) # {}
      <4> DEFINE new1b == [type |-> "1b", acc |-> acc,
                            ref |-> recent_msgs[acc] \cup {m1a}]
      <4> PICK m0 \in recent_msgs[A] :
                    \A m1 \in SentBy(A) : m1 \in Tran(m0)
          OBVIOUS
      <4> recent_msgs[A]' = recent_msgs[A]
        <5>1. CASE WellFormed(new1b)
          <6> recent_msgs' = [recent_msgs EXCEPT ![acc] = {new1b}]
              BY <5>1
          <6> QED OBVIOUS
        <5>2. CASE ~WellFormed(new1b)
          <6> recent_msgs' =
                [recent_msgs EXCEPT ![acc] = recent_msgs[acc] \cup {m1a}]
              BY <5>2
          <6> QED OBVIOUS
        <5>3. QED BY <5>1, <5>2
      <4> QED OBVIOUS
    <3>3. QED BY <3>1, <3>2
  <2> CASE acc = A
    <3> DEFINE new1b == [type |-> "1b", acc |-> acc,
                           ref |-> recent_msgs[acc] \cup {m1a}]
    <3>1. CASE mm \in msgs
      <4> PICK m0 \in recent_msgs[A] :
                    \A m1 \in SentBy(A) : m1 \in Tran(m0)
          BY <3>1 DEF SentBy
      <4>1. CASE WellFormed(new1b)
        <5> msgs' = msgs \cup {new1b}
            BY <4>1 DEF Send
        <5> new1b \in Message BY DEF TypeOK
        <5> SentBy(A)' = SentBy(A) \cup {new1b}
            BY <4>1 DEF Send, SentBy
        <5> recent_msgs' = [recent_msgs EXCEPT ![A] = {new1b}]
            BY <4>1
        <5> new1b \in recent_msgs[A]'
            BY CVC4 DEF TypeOK
        <5> WITNESS new1b \in recent_msgs[A]'
        <5> SUFFICES ASSUME NEW m1 \in SentBy(A)'
                     PROVE m1 \in Tran(new1b)
            OBVIOUS
        <5> m0 \in Tran(new1b) BY Message_ref_Tran
        <5> HIDE DEF new1b
        <5> QED BY Tran_trans, Tran_refl
      <4>2. CASE ~WellFormed(new1b)
        <5> recent_msgs' = [recent_msgs EXCEPT ![A] = recent_msgs[A] \cup {m1a}]
            BY <4>2
        <5> SentBy(A) = SentBy(A)'
            BY <4>2 DEF Send, SentBy
        <5> QED OBVIOUS
      <4>3. QED BY <4>1, <4>2
    <3>2. CASE mm \notin msgs
      <4>1. CASE WellFormed(new1b)
        <5> mm = new1b
            BY <3>2, <4>1 DEF Send
        <5> msgs' = msgs \cup {new1b}
            BY <4>1 DEF Send
        <5> new1b \in Message BY DEF TypeOK
        <5> SentBy(A)' = SentBy(A) \cup {new1b}
            BY <4>1 DEF Send, SentBy
        <5> recent_msgs' = [recent_msgs EXCEPT ![A] = {new1b}]
            BY <4>1
        <5> new1b \in recent_msgs[A]'
            BY CVC4 DEF TypeOK
        <5> WITNESS new1b \in recent_msgs[A]'
        <5>1. CASE SentBy(A) = {}
          <6> HIDE DEF new1b
          <6> QED BY <5>1, Tran_refl
        <5>2. CASE SentBy(A) # {}
          <6> PICK m0 \in recent_msgs[A] :
                    \A m1 \in SentBy(A) : m1 \in Tran(m0)
              BY <5>2
          <6> m0 \in Tran(new1b) BY Message_ref_Tran
          <6> HIDE DEF new1b
          <6> QED BY Tran_refl, Tran_trans
        <5> QED BY <5>1, <5>2, Zenon
      <4>2. CASE ~WellFormed(new1b)
            BY <4>2, <3>2 DEF Send
      <4>3. QED BY <4>1, <4>2
    <3>3. QED BY <3>1, <3>2
  <2>10. QED OBVIOUS
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  <2> PICK acc \in SafeAcceptor, msg \in msgs : Process1b(acc, msg)
      BY <1>3
  <2> USE DEF Process1b
  <2> acc \in Acceptor BY DEF Acceptor
  <2> SentBy(A) = SentBy(A)'
      BY DEF Send, SentBy
  <2>1. CASE SentBy(A) = {}
        BY <2>1 DEF Send, SentBy
  <2>2. CASE SentBy(A) # {}
    <3> PICK m0 \in recent_msgs[A] :
                \A m1 \in SentBy(A) : m1 \in Tran(m0)
        OBVIOUS
    <3> QED OBVIOUS
  <2>3. QED BY <2>1, <2>2
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> acc \in Acceptor BY DEF Acceptor
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       ref |-> recent_msgs[acc]]
  <2>1. CASE WellFormed(new2a)
    <3> new2a \in Message BY <2>1 DEF Send, TypeOK
    <3> recent_msgs' = [recent_msgs EXCEPT ![acc] = {new2a}]
        BY <2>1
    <3> CASE acc = A
      <4> msgs' = msgs \cup {new2a}
          BY <2>1 DEF Send
      <4> SentBy(A)' = SentBy(A) \cup {new2a}
          BY DEF SentBy
      <4> new2a \in Tran(new2a)
          BY Tran_refl
      <4> new2a \in recent_msgs[A]' BY DEF TypeOK
      <4> WITNESS new2a \in recent_msgs[A]'
      <4> CASE SentBy(A) # {}
        <5> SUFFICES ASSUME NEW m1 \in SentBy(A)
                     PROVE m1 \in Tran(new2a)
            OBVIOUS
        <5> PICK m0 \in recent_msgs[A] :
                    \A m \in SentBy(A) : m \in Tran(m0)
            OBVIOUS
        <5> m0 \in Tran(new2a) BY Message_ref_Tran
        <5> HIDE DEF new2a
        <5> QED BY Tran_refl, Tran_trans
      <4> QED OBVIOUS
    <3> CASE acc # A
      <4> SentBy(A) = SentBy(A)'
          BY <2>1 DEF Send, SentBy
      <4>1. CASE SentBy(A) = {}
            BY <4>1 DEF Send, SentBy
      <4>2. CASE SentBy(A) # {}
        <5> PICK m0 \in recent_msgs[A] :
                    \A m1 \in SentBy(A) : m1 \in Tran(m0)
            BY <4>2
        <5> WITNESS m0 \in recent_msgs[A]'
        <5> QED OBVIOUS
      <4>3. QED BY <4>1, <4>2
    <3> QED OBVIOUS
  <2>2. CASE ~WellFormed(new2a)
        BY <2>2 DEF SentBy, RecentMsgsSafeAcceptorSpec
  <2>3. QED BY <2>1, <2>2
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send, SentBy
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send, SentBy
<1>7. CASE FakeAcceptorAction
      BY <1>7, AcceptorAssumption DEF FakeAcceptorAction, FakeSend, Send, SentBy
<1>8. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
           DEF Next, AcceptorProcessAction, Process1bLearnerLoop

\* TODO
LEMMA UniqueMessageSent ==
    TypeOK /\ Next =>
    \A m1 \in msgs' : \A m2 \in msgs' :
        m1 \notin msgs /\ m2 \notin msgs =>
        m1 = m2

\* TODO
LEMMA KnownMsgSpecInvariant ==
    TypeOK /\ Next /\ KnownMsgSpec => KnownMsgSpec'

LEMMA MsgsSafeAcceptorSpecInvariant ==
    TypeOK /\ Next /\ RecentMsgsSafeAcceptorSpec /\
    MsgsSafeAcceptorSpec => MsgsSafeAcceptorSpec'
PROOF
<1> SUFFICES ASSUME TypeOK, Next, RecentMsgsSafeAcceptorSpec,
                    MsgsSafeAcceptorSpec
             PROVE  MsgsSafeAcceptorSpec'
    OBVIOUS
<1> TypeOK' BY TypeOKInvariant
<1> SUFFICES ASSUME NEW A \in SafeAcceptor,
                    NEW m1 \in msgs', NEW m2 \in msgs',
                    m1.type # "1a", m2.type # "1a",
                    m1.acc = A, m2.acc = A,
                    m1 \in msgs, m2 \notin msgs
             PROVE  m1 \in Tran(m2)
  <2> USE DEF MsgsSafeAcceptorSpec
  <2> SUFFICES ASSUME NEW A \in SafeAcceptor,
                      NEW x \in msgs', NEW y \in msgs',
                      x.type # "1a", y.type # "1a",
                      x.acc = A, y.acc = A
               PROVE  x \in Tran(y) \/ y \in Tran(x)
      OBVIOUS
  <2> QED BY UniqueMessageSent, Tran_refl DEF TypeOK
<1>1. CASE ProposerSendAction
      BY <1>1 DEF ProposerSendAction, Send1a, Send
<1>2. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1a(a, m)
  <2> PICK acc \in SafeAcceptor, m1a \in msgs : Process1a(acc, m1a)
      BY <1>2
  <2> USE DEF Process1a
  <2> acc \in Acceptor BY DEF Acceptor
  <2> acc = A BY DEF Send
  <2> DEFINE new1b == [type |-> "1b", acc |-> acc,
                       ref |-> recent_msgs[acc] \cup {m1a}]
  <2> m2 = new1b BY DEF Send
  <2> m2 \in Message BY DEF TypeOK
  <2> PICK m0 \in recent_msgs[A] :
            \A m \in SentBy(A) : m \in Tran(m0)
      BY DEF RecentMsgsSafeAcceptorSpec, SentBy
  <2> m0 \in Tran(m2) BY Message_ref_Tran
  <2> QED BY Tran_trans DEF SentBy
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
  BY <1>3 DEF Process1b, Send
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
  <2> PICK acc \in SafeAcceptor, lrn \in Learner : Process1bLearnerLoopStep(acc, lrn)
      BY <1>4
  <2> USE DEF Process1bLearnerLoopStep
  <2> acc \in Acceptor BY DEF Acceptor
  <2> acc = A BY DEF Send
  <2> DEFINE new2a == [type |-> "2a", lrn |-> lrn, acc |-> acc,
                       ref |-> recent_msgs[acc]]
  <2> m2 = new2a BY DEF Send
  <2> m2 \in Message BY DEF TypeOK
  <2> PICK m0 \in recent_msgs[A] :
            \A m \in SentBy(A) : m \in Tran(m0)
      BY DEF RecentMsgsSafeAcceptorSpec, SentBy
  <2> m0 \in Tran(m2) BY Message_ref_Tran
  <2> QED BY Tran_trans DEF SentBy
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Send
<1>6. CASE LearnerAction
      BY <1>6 DEF LearnerAction, LearnerRecv, LearnerDecide, Send
<1>7. CASE FakeAcceptorAction
      BY <1>7, AcceptorAssumption DEF FakeAcceptorAction, FakeSend, Send
<1>8. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop

LEMMA MsgsSafeAcceptorSpecImpliesCaughtSpec ==
    ASSUME TypeOK, KnownMsgSpec, MsgsSafeAcceptorSpec
    PROVE CaughtSpec
PROOF BY MessageTypeSpec
      DEF MsgsSafeAcceptorSpec, CaughtSpec, Caught, CaughtMsg, KnownMsgSpec, TypeOK

LEMMA QuorumIntersection ==
    ASSUME TypeOK,
           NEW a \in Learner, NEW b \in Learner,
           NEW M \in Message,
           NEW Qa \in SUBSET Message, NEW Qb \in SUBSET Message,
           { mm.acc : mm \in Qa } \in ByzQuorum,
           { mm.acc : mm \in Qb } \in ByzQuorum,
           [lr |-> a, q |-> { mm.acc : mm \in Qa }] \in TrustLive,
           [lr |-> b, q |-> { mm.acc : mm \in Qb }] \in TrustLive,
           b \in Con(a, M)
    PROVE \E p \in Acceptor, ma \in Qa, mb \in Qb :
            ma.acc = p /\ mb.acc = p
PROOF
<1> PICK S \in ByzQuorum :
            /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
            /\ S \cap Caught(M) = {}
    BY Zenon DEF Con
<1> PICK acc \in S : /\ acc \in { mm.acc : mm \in Qa }
                     /\ acc \in { mm.acc : mm \in Qb }
    BY LearnerGraphAssumptionValidity, Zenon
<1> QED BY BQAssumption

LEMMA EntConnected ==
    ASSUME CaughtSpec,
           NEW a \in Learner, NEW b \in Learner,
           <<a, b>> \in Ent,
           NEW s \in SafeAcceptor,
           NEW m \in known_msgs[s]
    PROVE b \in Con(a, m)
PROOF BY BQAssumption DEF Con, Ent, CaughtSpec

\*Con(a, x) ==
\*    { b \in Learner :
\*        \E S \in ByzQuorum :
\*            /\ [from |-> a, to |-> b, q |-> S] \in TrustSafe
\*            /\ S \cap Caught(x) = {} }

\*CaughtSpec ==
\*    \A AL \in SafeAcceptor \cup Learner :
\*        \A M \in known_msgs[AL] :
\*            Caught(M) \cap SafeAcceptor = {}


\* TODO
LEMMA DecisionSpecInvariant ==
    TypeOK /\ Next /\ DecisionSpec => DecisionSpec'

LEMMA ChosenSafeCaseEq ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW BB \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK,
           <<L1, L2>> \in Ent,
           ChosenIn(L1, BB, V1), ChosenIn(L2, BB, V2)
    PROVE V1 = V2
PROOF
<1> PICK S1 \in SUBSET { x \in known_msgs[L1] :
                            /\ B(x, BB)
                            /\ V(x, V1) },
         Q1 \in ByzQuorum :
            /\ [lr |-> L1, q |-> Q1] \in TrustLive
            /\ \A aa \in Q1 :
                \E mm \in S1 : mm.acc = aa
    BY DEF ChosenIn
<1> PICK S2 \in SUBSET { x \in known_msgs[L2] :
                            /\ B(x, BB)
                            /\ V(x, V2) },
         Q2 \in ByzQuorum :
            /\ [lr |-> L2, q |-> Q2] \in TrustLive
            /\ \A aa \in Q2 :
                \E mm \in S2 : mm.acc = aa
    BY DEF ChosenIn
<1> PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2
    BY EntanglementTrustLive
<1>4. PICK m1 \in known_msgs[L1] :
        /\ B(m1, BB)
        /\ V(m1, V1)
      BY DEF ChosenIn
<1>5. PICK m2 \in known_msgs[L2] :
        /\ B(m2, BB)
        /\ V(m2, V2)
      BY DEF ChosenIn
<1>6. QED BY <1>4, <1>5, V_def, V_func DEF TypeOK

LEMMA ChosenSafeCaseLt ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK, KnownMsgSpec, \*ReceivedSpec, MsgInv,
           \*HeterogeneousSpec,
           <<L1, L2>> \in Ent,
           B1 < B2,
           ChosenIn(L1, B1, V1), ChosenIn(L2, B2, V2)
    PROVE V1 = V2
PROOF
<1> SUFFICES ASSUME V1 # V2 PROVE FALSE OBVIOUS
<1> PICK S1 \in SUBSET { x \in known_msgs[L1] :
                            /\ x.type = "2a"
                            /\ x.lrn = L1
                            /\ B(x, B1)
                            /\ V(x, V1) },
         Q1 \in ByzQuorum :
            /\ [lr |-> L1, q |-> Q1] \in TrustLive
            /\ \A aa \in Q1 :
                \E mm \in S1 : mm.acc = aa
    BY DEF ChosenIn
<1> PICK S2 \in SUBSET { x \in known_msgs[L2] :
                            /\ x.type = "2a"
                            /\ x.lrn = L2
                            /\ B(x, B2)
                            /\ V(x, V2) },
         Q2 \in ByzQuorum :
            /\ [lr |-> L2, q |-> Q2] \in TrustLive
            /\ \A aa \in Q2 :
                \E mm \in S2 : mm.acc = aa
    BY DEF ChosenIn
<1> PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2
    BY EntanglementTrustLive
<1>4. PICK m1 \in msgs :
        /\ Proper(L1, m1)
        /\ WellFormed(m1)
        /\ m1.type = "2a"
        /\ m1.lrn = L1
        /\ m1.acc = A
        /\ B(m1, B1)
        /\ V(m1, V1)
      BY Tran_refl DEF ChosenIn, KnownMsgSpec, TypeOK
<1>5. PICK m2 \in msgs :
        /\ Proper(L2, m2)
        /\ WellFormed(m2)
        /\ m2.type = "2a"
        /\ m2.lrn = L2
        /\ m2.acc = A
        /\ B(m2, B2)
        /\ V(m2, V2)
      BY Tran_refl DEF ChosenIn, KnownMsgSpec, TypeOK
<1> [lr |-> L1, q |-> q(m1)] \in TrustLive
      BY <1>4 DEF WellFormed
<1> [lr |-> L2, q |-> q(m2)] \in TrustLive
      BY <1>5 DEF WellFormed
<1> q(m1) \in ByzQuorum BY TrustLiveAssumption
<1> q(m2) \in ByzQuorum BY TrustLiveAssumption
<1>8. PICK A0 \in SafeAcceptor : A0 \in q(m1) /\ A0 \in q(m2)
      BY EntanglementTrustLive DEF TypeOK
\*q(x) ==
\*    LET Q == { m \in Tran(x) :
\*                /\ m.type = "1b"
\*                /\ Fresh(x.lrn, m)
\*                /\ \A mb, xb \in Ballot :
\*                    B(m, mb) /\ B(x, xb) => mb = xb }
\*    IN {a \in Acceptor : \E m \in Q : m.acc = a}
<1>9. PICK m1b \in Tran(m2) :
        /\ m1b.type = "1b"
        /\ m1b.acc = A0
        /\ Fresh(L2, m1b)
        /\ \A b \in Ballot : B(m1b, b) => b = B2
      BY <1>5, <1>8 DEF q
\*<1>7. PICK R2 \in ByzQuorum :
<1>20. QED
\*<1> USE DEF MsgInv
\*<1> SUFFICES ASSUME V1 # V2 PROVE FALSE OBVIOUS
\*<1>1. PICK Q1 \in ByzQuorum :
\*        /\ [lr |-> L1, q |-> Q1] \in TrustLive
\*        /\ \A aa \in Q1 :
\*            \E m \in {mm \in receivedByLearner[L1] : mm.bal = B1} :
\*                /\ m.val = V1
\*                /\ m.acc = aa
\*      BY DEF ChosenIn
\*<1>2. PICK Q2 \in ByzQuorum :
\*        /\ [lr |-> L2, q |-> Q2] \in TrustLive
\*        /\ \A aa \in Q2 :
\*            \E m \in {mm \in receivedByLearner[L2] : mm.bal = B2} :
\*                /\ m.val = V2
\*                /\ m.acc = aa
\*      BY DEF ChosenIn
\*<1>3. PICK A \in SafeAcceptor : A \in Q1 /\ A \in Q2 BY EntanglementTrustLive, <1>1, <1>2
\*<1>4. PICK m1 \in receivedByLearner[L1] : m1.acc = A /\ m1.bal = B1 /\ m1.val = V1 BY <1>1, <1>3 DEF ChosenIn
\*<1>5. PICK m2 \in receivedByLearner[L2] : m2.acc = A /\ m2.bal = B2 /\ m2.val = V2 BY <1>2, <1>3 DEF ChosenIn
\*<1>6. /\ m1 \in msgs
\*      /\ m1.type = "2b"
\*      /\ m1.lr = L1
\*      /\ m1.acc = A
\*      /\ m1.bal = B1
\*      /\ m1.val = V1
\*      BY <1>4 DEF ReceivedByLearnerSpec, TypeOK
\*<1>7. /\ m2 \in msgs
\*      /\ m2.type = "2b"
\*      /\ m2.lr = L2
\*      /\ m2.acc = A
\*      /\ m2.bal = B2
\*      /\ m2.val = V2
\*      BY <1>5 DEF ReceivedByLearnerSpec, TypeOK
\*<1>10. PICK R1 \in ByzQuorum :
\*            /\ [lr |-> L1, q |-> R1] \in TrustLive
\*       BY <1>6 DEF MsgInv2b
\*<1>11. PICK R2 \in ByzQuorum :
\*            /\ [lr |-> L2, q |-> R2] \in TrustLive
\*            /\ \A aa \in R2 :
\*                \E m2av \in received[A] :
\*                    /\ m2av.type = "2av"
\*                    /\ m2av.lr = L2
\*                    /\ m2av.acc = aa
\*                    /\ m2av.bal = B2
\*                    /\ m2av.val = V2
\*       BY <1>7 DEF MsgInv2b
\*<1>12. PICK A0 \in SafeAcceptor : A0 \in R1 /\ A0 \in R2 BY EntanglementTrustLive, <1>10, <1>11
\*<1>14. PICK m2av2 \in received[A] :
\*            m2av2.type = "2av" /\ m2av2.lr = L2 /\ m2av2.acc = A0 /\ m2av2.bal = B2 /\ m2av2.val = V2
\*       BY <1>12, <1>11
\*<1>16. /\ m2av2 \in msgs
\*       /\ m2av2.type = "2av"
\*       /\ m2av2.lr = L2
\*       /\ m2av2.acc = A0
\*       /\ m2av2.bal = B2
\*       /\ m2av2.val = V2
\*       BY <1>14, SafeAcceptorIsAcceptor DEF ReceivedSpec, TypeOK
\*<1>17. CannotDecide(Q1, L1, B1, V1)
\*  <2>1. [lr |-> L1, q |-> Q1] \in TrustLive BY <1>1
\*  <2>5. QED BY <1>16, <2>1 DEF HeterogeneousSpec
\*<1>18. PICK S \in SafeAcceptor : S \in Q1 /\ ~VotedFor(L1, S, B1, V1) BY <1>17 DEF CannotDecide
\*<1>19. PICK m \in receivedByLearner[L1] : m.acc = S /\ m.bal = B1 /\ m.val = V1
\*       BY <1>18, <1>1 DEF CannotDecide
\*<1>20. /\ m \in {mm \in msgs : mm.type = "2b"}
\*       /\ m.lr = L1
\*       /\ m.acc = S
\*       /\ m.bal = B1
\*       /\ m.val = V1
\*       BY <1>19 DEF ReceivedByLearnerSpec, TypeOK
\*<1>50. QED BY <1>20, <1>18 DEF CannotDecide, VotedFor, ReceivedByLearnerSpec, TypeOK

LEMMA ChosenSafe ==
    ASSUME NEW L1 \in Learner, NEW L2 \in Learner,
           NEW B1 \in Ballot, NEW B2 \in Ballot,
           NEW V1 \in Value, NEW V2 \in Value,
           TypeOK, KnownMsgSpec,
           \*ReceivedSpec, VotesSentSpec4, MsgInv,
           \*HeterogeneousSpec,
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
    KnownMsgSpec /\ DecisionSpec /\
    Safety => Safety'
PROOF
<1> SUFFICES
        ASSUME TypeOK, Next,
               KnownMsgSpec, DecisionSpec,
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
<1>3. CASE \E a \in SafeAcceptor : \E m \in msgs : Process1b(a, m)
      BY <1>3 DEF Process1b, Safety
<1>4. CASE \E a \in SafeAcceptor : \E l \in Learner : Process1bLearnerLoopStep(a, l)
      BY <1>4 DEF Process1bLearnerLoopStep, Safety
<1>5. CASE \E a \in SafeAcceptor : Process1bLearnerLoopDone(a)
      BY <1>5 DEF Process1bLearnerLoopDone, Safety
<1>6. CASE \E lrn \in Learner : LearnerRecv(lrn)
      BY <1>6 DEF LearnerRecv, Safety
<1>7. CASE \E lrn \in Learner : \E bal \in Ballot : \E val \in Value :
            LearnerDecide(lrn, bal, val)
  <2> PICK lrn \in Learner, bal \in Ballot, val \in Value :
        /\ ChosenIn(lrn, bal, val)
        /\ decision' = [decision EXCEPT ![<<lrn, bal>>] = decision[lrn, bal] \cup {val}]
        /\ UNCHANGED << msgs, known_msgs, recent_msgs, 2a_lrn_loop, processed_lrns, BVal >>
      BY <1>7 DEF LearnerDecide
  <2> CASE V1 # V2
    <3>1. CASE val # V1 /\ val # V2 BY <3>1 DEF Safety, TypeOK
    <3>2. CASE val = V1
      <4> V2 \in decision[L2, B2] BY <3>2 DEF TypeOK
      <4>1. ChosenIn(L2, B2, V2) BY DEF DecisionSpec
      <4>2. CASE V1 \in decision[L1, B1] BY <4>2 DEF Safety
      <4>3. CASE V1 \notin decision[L1, B1]
        <5> lrn = L1 /\ bal = B1 BY <4>3, <3>2 DEF TypeOK
        <5>2. ChosenIn(L1, B1, V1) BY <3>2
        <5>3. QED BY <4>1, <5>2, ChosenSafe, AllProvers
      <4>4. QED BY <4>2, <4>3
    <3>3. CASE val = V2
      <4> V1 \in decision[L1, B1] BY <3>3 DEF TypeOK
      <4>1. ChosenIn(L1, B1, V1) BY DEF DecisionSpec
      <4>2. CASE V2 \in decision[L2, B2] BY <4>2 DEF Safety
      <4>3. CASE V2 \notin decision[L2, B2]
        <5> lrn = L2 /\ bal = B2 BY <4>3, <3>2 DEF TypeOK
        <5>2. ChosenIn(L2, B2, V2) BY <3>3
        <5>3. QED BY <4>1, <5>2, ChosenSafe
      <4>4. QED BY <4>2, <4>3
    <3>10. QED BY <3>1, <3>2, <3>3
  <2>10. QED OBVIOUS
<1>8. CASE FakeAcceptorAction
      BY <1>8 DEF FakeAcceptorAction, FakeSend, Safety
<1>9. QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8
          DEF Next, AcceptorProcessAction, Process1bLearnerLoop, LearnerAction 

-----------------------------------------------------------------------------
\*LEMMA SafetyStep ==
\*    TypeOK /\ Next /\ MsgInv /\
\*    DecisionSpec /\ ReceivedSpec /\ ReceivedByLearnerSpec /\
\*    2avSentSpec1 /\ 2avSentSpec3 /\ VotesSentSpec4 /\
\*    HeterogeneousSpec /\ Safety => Safety'

=============================================================================
\* Modification History
\* Last modified Mon Sep 19 13:11:03 CEST 2022 by aleph
\* Created Thu Aug 25 10:12:00 CEST 2022 by aleph
